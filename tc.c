/* tc-sparc.c -- Assemble for the SPARC
   Copyright (C) 1989-2025 Free Software Foundation, Inc.
   This file is part of GAS, the GNU Assembler.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public
   License along with GAS; see the file COPYING.  If not, write
   to the Free Software Foundation, 51 Franklin Street - Fifth Floor,
   Boston, MA 02110-1301, USA.  */

#include "as.h"
#include "safe-ctype.h"
#include "subsegs.h"

#include "opcode/sparc.h"
#include "dw2gencfi.h"

#include "elf/sparc.h"
#include "dwarf2dbg.h"

/* Some ancient Sun C compilers would not take such hex constants as
   unsigned, and would end up sign-extending them to form an offsetT,
   so use these constants instead.  */
#define U0xffffffff ((((unsigned long) 1 << 16) << 16) - 1)
#define U0x80000000 ((((unsigned long) 1 << 16) << 15))

static int sparc_ip (char *, const struct sparc_opcode **);
static int parse_sparc_asi (char **, const sparc_asi **);
static int parse_keyword_arg (int (*) (const char *), char **, int *);
static int parse_const_expr_arg (char **, int *);
static int get_expression (char *);

/* Default architecture.  */
/* ??? The default value should be V8, but sparclite support was added
   by making it the default.  GCC now passes -Asparclite, so maybe sometime in
   the future we can set this to V8.  */
#ifndef DEFAULT_ARCH
#define DEFAULT_ARCH "sparclite"
#endif
static const char *default_arch = DEFAULT_ARCH;

/* Non-zero if the initial values of `max_architecture' and `sparc_arch_size'
   have been set.  */
static int default_init_p;

/* Current architecture.  We don't bump up unless necessary.  */
static enum sparc_opcode_arch_val current_architecture = SPARC_OPCODE_ARCH_V6;

/* The maximum architecture level we can bump up to.
   In a 32 bit environment, don't allow bumping up to v9 by default.
   The native assembler works this way.  The user is required to pass
   an explicit argument before we'll create v9 object files.  However, if
   we don't see any v9 insns, a v8plus object file is not created.  */
static enum sparc_opcode_arch_val max_architecture;

/* Either 32 or 64, selects file format.  */
static int sparc_arch_size;
/* Initial (default) value, recorded separately in case a user option
   changes the value before md_show_usage is called.  */
static int default_arch_size;

/* The currently selected v9 memory model.  Currently only used for
   ELF.  */
static enum { MM_TSO, MM_PSO, MM_RMO } sparc_memory_model = MM_RMO;

#ifndef TE_SOLARIS
/* Bitmask of instruction types seen so far, used to populate the
   GNU attributes section with hwcap information.  */
static uint64_t hwcap_seen;
#endif

static uint64_t hwcap_allowed;

static int architecture_requested;
static int warn_on_bump;

/* If warn_on_bump and the needed architecture is higher than this
   architecture, issue a warning.  */
static enum sparc_opcode_arch_val warn_after_architecture;

/* Non-zero if the assembler should generate error if an undeclared
   g[23] register has been used in -64.  */
static int no_undeclared_regs;

/* Non-zero if the assembler should generate a warning if an
   unpredictable DCTI (delayed control transfer instruction) couple is
   found.  */
static int dcti_couples_detect;

/* Non-zero if we should try to relax jumps and calls.  */
static int sparc_relax;

/* Non-zero if we are generating PIC code.  */
int sparc_pic_code;

/* Non-zero if we should give an error when misaligned data is seen.  */
static int enforce_aligned_data;

extern int target_big_endian;

static int target_little_endian_data;

/* Symbols for global registers on v9.  */
static symbolS *globals[8];

/* The dwarf2 data alignment, adjusted for 32 or 64 bit.  */
int sparc_cie_data_alignment;

/* V9 and 86x have big and little endian data, but instructions are always big
   endian.  The sparclet has bi-endian support but both data and insns have
   the same endianness.  Global `target_big_endian' is used for data.
   The following macro is used for instructions.  */
#ifndef INSN_BIG_ENDIAN
#define INSN_BIG_ENDIAN (target_big_endian \
			 || default_arch_type == sparc86x \
			 || SPARC_OPCODE_ARCH_V9_P (max_architecture))
#endif

/* Handle of the OPCODE hash table.  */
static htab_t op_hash;

static void s_data1 (void);
static void s_seg (int);
static void s_proc (int);
static void s_reserve (int);
static void s_common (int);
static void s_empty (int);
static void s_uacons (int);
static void s_ncons (int);
static void s_register (int);

const pseudo_typeS md_pseudo_table[] =
{
  {"align", s_align_bytes, 0},	/* Defaulting is invalid (0).  */
  {"common", s_common, 0},
  {"empty", s_empty, 0},
  {"global", s_globl, 0},
  {"half", cons, 2},
  {"nword", s_ncons, 0},
  {"optim", s_ignore, 0},
  {"proc", s_proc, 0},
  {"reserve", s_reserve, 0},
  {"seg", s_seg, 0},
  {"skip", s_space, 0},
  {"word", cons, 4},
  {"xword", cons, 8},
  {"uahalf", s_uacons, 2},
  {"uaword", s_uacons, 4},
  {"uaxword", s_uacons, 8},
  /* These are specific to sparc/svr4.  */
  {"2byte", s_uacons, 2},
  {"4byte", s_uacons, 4},
  {"8byte", s_uacons, 8},
  {"register", s_register, 0},
  {NULL, 0, 0},
};

/* This array holds the chars that always start a comment.  If the
   pre-processor is disabled, these aren't very useful.  */
const char comment_chars[] = "!";	/* JF removed '|' from
                                           comment_chars.  */

/* This array holds the chars that only start a comment at the beginning of
   a line.  If the line seems to have the form '# 123 filename'
   .line and .file directives will appear in the pre-processed output.  */
/* Note that input_file.c hand checks for '#' at the beginning of the
   first line of the input file.  This is because the compiler outputs
   #NO_APP at the beginning of its output.  */
/* Also note that comments started like this one will always
   work if '/' isn't otherwise defined.  */
const char line_comment_chars[] = "#";

const char line_separator_chars[] = ";";

/* Chars that can be used to separate mant from exp in floating point
   nums.  */
const char EXP_CHARS[] = "eE";

/* Chars that mean this number is a floating point constant.
   As in 0f12.456
   or    0d1.2345e12  */
const char FLT_CHARS[] = "rRsSfFdDxXpP";

/* Also be aware that MAXIMUM_NUMBER_OF_CHARS_FOR_FLOAT may have to be
   changed in read.c.  Ideally it shouldn't have to know about it at all,
   but nothing is ideal around here.  */

#define isoctal(c)  ((unsigned) ((c) - '0') < 8)

struct sparc_it
  {
    const char *error;
    unsigned long opcode;
    struct nlist *nlistp;
    expressionS exp;
    expressionS exp2;
    int pcrel;
    bfd_reloc_code_real_type reloc;
  };

struct sparc_it the_insn, set_insn;

static void output_insn (const struct sparc_opcode *, struct sparc_it *);

/* Table of arguments to -A.
   The sparc_opcode_arch table in sparc-opc.c is insufficient and incorrect
   for this use.  That table is for opcodes only.  This table is for opcodes
   and file formats.  */

enum sparc_arch_types {v6, v7, v8, leon, sparclet, sparclite, sparc86x, v8plus,
		       v8plusa, v9, v9a, v9b, v9_64};

static struct sparc_arch {
  const char *name;
  const char *opcode_arch;
  enum sparc_arch_types arch_type;
  /* Default word size, as specified during configuration.
     A value of zero means can't be used to specify default architecture.  */
  int default_arch_size;
  /* Allowable arg to -A?  */
  int user_option_p;
  /* Extra hardware capabilities allowed.  These are added to the
     hardware capabilities associated with the opcode
     architecture.  */
  int hwcap_allowed;
  int hwcap2_allowed;
} sparc_arch_table[] = {
  { "v6",         "v6",  v6,  0, 1, 0, 0 },
  { "v7",         "v7",  v7,  0, 1, 0, 0 },
  { "v8",         "v8",  v8, 32, 1, 0, 0 },
  { "v8a",        "v8",  v8, 32, 1, 0, 0 },
  { "sparc",      "v9",  v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "sparcvis",   "v9a", v9,  0, 1, 0, 0 },
  { "sparcvis2",  "v9b", v9,  0, 1, 0, 0 },
  { "sparcfmaf",  "v9b", v9,  0, 1, HWCAP_FMAF, 0 },
  { "sparcima",   "v9b", v9,  0, 1, HWCAP_FMAF|HWCAP_IMA, 0 },
  { "sparcvis3",  "v9b", v9,  0, 1, HWCAP_FMAF|HWCAP_VIS3|HWCAP_HPC, 0 },
  { "sparcvis3r", "v9b", v9,  0, 1, HWCAP_FMAF|HWCAP_VIS3|HWCAP_HPC|HWCAP_FJFMAU, 0 },

  { "sparc4",     "v9v", v9,  0, 1, 0, 0 },
  { "sparc5",     "v9m", v9,  0, 1, 0, 0 },
  { "sparc6",     "m8",  v9,  0, 1, 0, 0 },

  { "leon",      "leon",      leon,      32, 1, 0, 0 },
  { "sparclet",  "sparclet",  sparclet,  32, 1, 0, 0 },
  { "sparclite", "sparclite", sparclite, 32, 1, 0, 0 },
  { "sparc86x",  "sparclite", sparc86x,  32, 1, 0, 0 },

  { "v8plus",  "v9",  v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8plusa", "v9a", v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8plusb", "v9b", v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8plusc", "v9c", v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8plusd", "v9d", v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8pluse", "v9e", v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8plusv", "v9v", v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8plusm", "v9m", v9,  0, 1, HWCAP_V8PLUS, 0 },
  { "v8plusm8", "m8", v9,  0, 1, HWCAP_V8PLUS, 0 },
  
  { "v9",      "v9",  v9,  0, 1, 0, 0 },
  { "v9a",     "v9a", v9,  0, 1, 0, 0 },
  { "v9b",     "v9b", v9,  0, 1, 0, 0 },
  { "v9c",     "v9c", v9,  0, 1, 0, 0 },
  { "v9d",     "v9d", v9,  0, 1, 0, 0 },
  { "v9e",     "v9e", v9,  0, 1, 0, 0 },
  { "v9v",     "v9v", v9,  0, 1, 0, 0 },
  { "v9m",     "v9m", v9,  0, 1, 0, 0 },
  { "v9m8",     "m8", v9,  0, 1, 0, 0 },

  /* This exists to allow configure.tgt to pass one
     value to specify both the default machine and default word size.  */
  { "v9-64",   "v9",  v9, 64, 0, 0, 0 },
  { NULL, NULL, v8, 0, 0, 0, 0 }
};

/* Variant of default_arch */
static enum sparc_arch_types default_arch_type;

static struct sparc_arch *
lookup_arch (const char *name)
{
  struct sparc_arch *sa;

  for (sa = &sparc_arch_table[0]; sa->name != NULL; sa++)
    if (strcmp (sa->name, name) == 0)
      return sa;
  
  return NULL;
}

/* Initialize the default opcode arch and word size from the default
   architecture name.  */

static void
validate_arch(struct sparc_arch *sa)
{
  if (sa == NULL || sa->default_arch_size == 0)
    as_fatal (_("Invalid default architecture, broken assembler."));
}

static void
validate_opcode_arch(enum sparc_opcode_arch_val arch)
{
  if (arch == SPARC_OPCODE_ARCH_BAD)
    as_fatal (_("Bad opcode table, broken assembler."));
}

static void
set_arch_defaults(struct sparc_arch *sa)
{
  max_architecture = sparc_opcode_lookup_arch (sa->opcode_arch);
  validate_opcode_arch(max_architecture);
  
  default_arch_size = sparc_arch_size = sa->default_arch_size;
  default_init_p = 1;
  default_arch_type = sa->arch_type;
}

static void
init_default_arch (void)
{
  struct sparc_arch *sa = lookup_arch (default_arch);
  validate_arch(sa);
  set_arch_defaults(sa);
}

/* Called by TARGET_MACH.  */

unsigned long
sparc_mach (void)
{
  if (! default_init_p)
    init_default_arch ();

  const int SPARC_64_BIT_SIZE = 64;
  return sparc_arch_size == SPARC_64_BIT_SIZE ? bfd_mach_sparc_v9 : bfd_mach_sparc;
}

/* Called by TARGET_FORMAT.  */

const char *
sparc_target_format (void)
{
  if (!default_init_p)
    init_default_arch ();

#ifdef TE_VXWORKS
  return "elf32-sparc-vxworks";
#endif

  return sparc_arch_size == 64 ? ELF64_TARGET_FORMAT : ELF_TARGET_FORMAT;
}

/* md_parse_option
 *	Invocation line includes a switch not recognized by the base assembler.
 *	See if it's a processor-specific option.  These are:
 *
 *	-bump
 *		Warn on architecture bumps.  See also -A.
 *
 *	-Av6, -Av7, -Av8, -Aleon, -Asparclite, -Asparclet
 *		Standard 32 bit architectures.
 *	-Av9, -Av9a, -Av9b
 *		Sparc64 in either a 32 or 64 bit world (-32/-64 says which).
 *		This used to only mean 64 bits, but properly specifying it
 *		complicated gcc's ASM_SPECs, so now opcode selection is
 *		specified orthogonally to word size (except when specifying
 *		the default, but that is an internal implementation detail).
 *	-Av8plus, -Av8plusa, -Av8plusb
 *		Same as -Av9{,a,b}.
 *	-xarch=v8plus, -xarch=v8plusa, -xarch=v8plusb
 *		Same as -Av8plus{,a,b} -32, for compatibility with Sun's
 *		assembler.
 *	-xarch=v9, -xarch=v9a, -xarch=v9b
 *		Same as -Av9{,a,b} -64, for compatibility with Sun's
 *		assembler.
 *
 *		Select the architecture and possibly the file format.
 *		Instructions or features not supported by the selected
 *		architecture cause fatal errors.
 *
 *		The default is to start at v6, and bump the architecture up
 *		whenever an instruction is seen at a higher level.  In 32 bit
 *		environments, v9 is not bumped up to, the user must pass
 * 		-Av8plus{,a,b}.
 *
 *		If -bump is specified, a warning is printing when bumping to
 *		higher levels.
 *
 *		If an architecture is specified, all instructions must match
 *		that architecture.  Any higher level instructions are flagged
 *		as errors.  Note that in the 32 bit environment specifying
 *		-Av8plus does not automatically create a v8plus object file, a
 *		v9 insn must be seen.
 *
 *		If both an architecture and -bump are specified, the
 *		architecture starts at the specified level, but bumps are
 *		warnings.  Note that we can't set `current_architecture' to
 *		the requested level in this case: in the 32 bit environment,
 *		we still must avoid creating v8plus object files unless v9
 * 		insns are seen.
 *
 * Note:
 *		Bumping between incompatible architectures is always an
 *		error.  For example, from sparclite to v9.
 */

const char md_shortopts[] = "A:K:VQ:sq";
const struct option md_longopts[] = {
#define OPTION_BUMP (OPTION_MD_BASE)
  {"bump", no_argument, NULL, OPTION_BUMP},
#define OPTION_SPARC (OPTION_MD_BASE + 1)
  {"sparc", no_argument, NULL, OPTION_SPARC},
#define OPTION_XARCH (OPTION_MD_BASE + 2)
  {"xarch", required_argument, NULL, OPTION_XARCH},
#define OPTION_32 (OPTION_MD_BASE + 3)
  {"32", no_argument, NULL, OPTION_32},
#define OPTION_64 (OPTION_MD_BASE + 4)
  {"64", no_argument, NULL, OPTION_64},
#define OPTION_TSO (OPTION_MD_BASE + 5)
  {"TSO", no_argument, NULL, OPTION_TSO},
#define OPTION_PSO (OPTION_MD_BASE + 6)
  {"PSO", no_argument, NULL, OPTION_PSO},
#define OPTION_RMO (OPTION_MD_BASE + 7)
  {"RMO", no_argument, NULL, OPTION_RMO},
#ifdef SPARC_BIENDIAN
#define OPTION_LITTLE_ENDIAN (OPTION_MD_BASE + 8)
  {"EL", no_argument, NULL, OPTION_LITTLE_ENDIAN},
#define OPTION_BIG_ENDIAN (OPTION_MD_BASE + 9)
  {"EB", no_argument, NULL, OPTION_BIG_ENDIAN},
#endif
#define OPTION_ENFORCE_ALIGNED_DATA (OPTION_MD_BASE + 10)
  {"enforce-aligned-data", no_argument, NULL, OPTION_ENFORCE_ALIGNED_DATA},
#define OPTION_LITTLE_ENDIAN_DATA (OPTION_MD_BASE + 11)
  {"little-endian-data", no_argument, NULL, OPTION_LITTLE_ENDIAN_DATA},
#define OPTION_NO_UNDECLARED_REGS (OPTION_MD_BASE + 12)
  {"no-undeclared-regs", no_argument, NULL, OPTION_NO_UNDECLARED_REGS},
#define OPTION_UNDECLARED_REGS (OPTION_MD_BASE + 13)
  {"undeclared-regs", no_argument, NULL, OPTION_UNDECLARED_REGS},
#define OPTION_RELAX (OPTION_MD_BASE + 14)
  {"relax", no_argument, NULL, OPTION_RELAX},
#define OPTION_NO_RELAX (OPTION_MD_BASE + 15)
  {"no-relax", no_argument, NULL, OPTION_NO_RELAX},
#define OPTION_DCTI_COUPLES_DETECT (OPTION_MD_BASE + 16)
  {"dcti-couples-detect", no_argument, NULL, OPTION_DCTI_COUPLES_DETECT},
  {NULL, no_argument, NULL, 0}
};

const size_t md_longopts_size = sizeof (md_longopts);

int
md_parse_option (int c, const char *arg)
{
  if (!default_init_p)
    init_default_arch ();

  switch (c)
    {
    case OPTION_BUMP:
      return handle_bump_option();

    case OPTION_XARCH:
      return handle_xarch_option(arg);

    case 'A':
      return handle_arch_option(arg, c);

    case OPTION_SPARC:
      break;

    case OPTION_ENFORCE_ALIGNED_DATA:
      enforce_aligned_data = 1;
      break;

#ifdef SPARC_BIENDIAN
    case OPTION_LITTLE_ENDIAN:
      return handle_little_endian_option();

    case OPTION_LITTLE_ENDIAN_DATA:
      return handle_little_endian_data_option();

    case OPTION_BIG_ENDIAN:
      target_big_endian = 1;
      break;
#endif

    case OPTION_32:
    case OPTION_64:
      return handle_arch_size_option(c);

    case OPTION_TSO:
      sparc_memory_model = MM_TSO;
      break;

    case OPTION_PSO:
      sparc_memory_model = MM_PSO;
      break;

    case OPTION_RMO:
      sparc_memory_model = MM_RMO;
      break;

    case 'V':
      print_version_id ();
      break;

    case 'Q':
    case 's':
    case 'q':
      break;

    case 'K':
      return handle_K_option(arg);

    case OPTION_NO_UNDECLARED_REGS:
      no_undeclared_regs = 1;
      break;

    case OPTION_UNDECLARED_REGS:
      no_undeclared_regs = 0;
      break;

    case OPTION_RELAX:
      sparc_relax = 1;
      break;

    case OPTION_NO_RELAX:
      sparc_relax = 0;
      break;

    case OPTION_DCTI_COUPLES_DETECT:
      dcti_couples_detect = 1;
      break;

    default:
      return 0;
    }

  return 1;
}

static int
handle_bump_option(void)
{
  warn_on_bump = 1;
  warn_after_architecture = SPARC_OPCODE_ARCH_V6;
  return 1;
}

static int
is_v8_or_older_arch(const char *arg)
{
  return startswith (arg, "v8")
      || startswith (arg, "v7")
      || startswith (arg, "v6")
      || !strcmp (arg, "sparclet")
      || !strcmp (arg, "sparclite")
      || !strcmp (arg, "sparc86x");
}

static int
handle_xarch_option(const char *arg)
{
  if (startswith (arg, "v9"))
    md_parse_option (OPTION_64, NULL);
  else if (is_v8_or_older_arch(arg))
    md_parse_option (OPTION_32, NULL);

  return handle_arch_option(arg, OPTION_XARCH);
}

static void
report_invalid_arch(const char *arg, int option_type)
{
  if (option_type == OPTION_XARCH)
    as_bad (_("invalid architecture -xarch=%s"), arg);
  else
    as_bad (_("invalid architecture -A%s"), arg);
}

static void
update_max_architecture(enum sparc_opcode_arch_val opcode_arch)
{
  if (!architecture_requested || opcode_arch > max_architecture)
    max_architecture = opcode_arch;
}

static void
update_hwcap_allowed(struct sparc_arch *sa, enum sparc_opcode_arch_val opcode_arch)
{
  hwcap_allowed = (hwcap_allowed
                  | ((uint64_t) sparc_opcode_archs[opcode_arch].hwcaps2 << 32)
                  | ((uint64_t) sa->hwcap2_allowed << 32)
                  | sparc_opcode_archs[opcode_arch].hwcaps
                  | sa->hwcap_allowed);
}

static int
handle_arch_option(const char *arg, int option_type)
{
  struct sparc_arch *sa;
  enum sparc_opcode_arch_val opcode_arch;

  sa = lookup_arch (arg);
  if (sa == NULL || !sa->user_option_p)
    {
      report_invalid_arch(arg, option_type);
      return 0;
    }

  opcode_arch = sparc_opcode_lookup_arch (sa->opcode_arch);
  if (opcode_arch == SPARC_OPCODE_ARCH_BAD)
    as_fatal (_("Bad opcode table, broken assembler."));

  update_max_architecture(opcode_arch);
  update_hwcap_allowed(sa, opcode_arch);
  architecture_requested = 1;

  return 1;
}

#ifdef SPARC_BIENDIAN
static int
handle_little_endian_option(void)
{
  target_big_endian = 0;
  if (default_arch_type != sparclet)
    as_fatal ("This target does not support -EL");
  return 1;
}

static int
handle_little_endian_data_option(void)
{
  target_little_endian_data = 1;
  target_big_endian = 0;
  if (default_arch_type != sparc86x && default_arch_type != v9)
    as_fatal ("This target does not support --little-endian-data");
  return 1;
}
#endif

static const char *
find_matching_elf_target(const char **list, int arch_size)
{
  const char **l;
  const char *prefix = arch_size == 32 ? "elf32-sparc" : "elf64-sparc";

  for (l = list; *l != NULL; l++)
    {
      if (startswith (*l, prefix))
        return *l;
    }
  return NULL;
}

static int
handle_arch_size_option(int option)
{
  const char **list;
  const char *target;

  sparc_arch_size = option == OPTION_32 ? 32 : 64;
  list = bfd_target_list ();
  target = find_matching_elf_target(list, sparc_arch_size);

  if (target == NULL)
    as_fatal (_("No compiled in support for %d bit object file format"),
              sparc_arch_size);
  free (list);

  if (sparc_arch_size == 64 && max_architecture < SPARC_OPCODE_ARCH_V9)
    max_architecture = SPARC_OPCODE_ARCH_V9;

  return 1;
}

static int
handle_K_option(const char *arg)
{
  if (strcmp (arg, "PIC") != 0)
    as_warn (_("Unrecognized option following -K"));
  else
    sparc_pic_code = 1;
  return 1;
}

void
md_show_usage (FILE *stream)
{
  #define MAX_LINE_LENGTH 70
  #define XARCH_MAX_LINE_LENGTH 65
  #define ARCH_PREFIX_LENGTH 5
  #define SEPARATOR_LENGTH 2
  #define XARCH_PREFIX_LENGTH 7

  const struct sparc_arch *arch;
  int column;

  if (! default_init_p)
    init_default_arch ();

  fprintf (stream, _("SPARC options:\n"));
  
  column = print_arch_options(stream, "-A%s", MAX_LINE_LENGTH, ARCH_PREFIX_LENGTH, 0);
  print_arch_options(stream, "-xarch=%s", XARCH_MAX_LINE_LENGTH, ARCH_PREFIX_LENGTH + XARCH_PREFIX_LENGTH, column);
  
  print_usage_text(stream);
}

static int
print_arch_options(FILE *stream, const char *format, int max_length, int prefix_length, int initial_column)
{
  const struct sparc_arch *arch;
  int column = initial_column;
  int first = (initial_column == 0);
  
  for (arch = &sparc_arch_table[0]; arch->name; arch++)
    {
      if (!arch->user_option_p)
        continue;
        
      if (!first)
        fprintf (stream, " | ");
      else
        first = 0;
        
      if (column + strlen (arch->name) > max_length)
        {
          column = 0;
          fputc ('\n', stream);
        }
        
      column += prefix_length + SEPARATOR_LENGTH + strlen (arch->name);
      fprintf (stream, format, arch->name);
    }
    
  return column;
}

static void
print_usage_text(FILE *stream)
{
  fprintf (stream, _("\n\
			specify variant of SPARC architecture\n\
-bump			warn when assembler switches architectures\n\
-sparc			ignored\n\
--enforce-aligned-data	force .long, etc., to be aligned correctly\n\
-relax			relax jumps and branches (default)\n\
-no-relax		avoid changing any jumps and branches\n"));
  
  fprintf (stream, _("\
-32			create 32 bit object file\n\
-64			create 64 bit object file\n"));
  
  fprintf (stream, _("\
			[default is %d]\n"), default_arch_size);
  
  fprintf (stream, _("\
-TSO			use Total Store Ordering\n\
-PSO			use Partial Store Ordering\n\
-RMO			use Relaxed Memory Ordering\n"));
  
  fprintf (stream, _("\
			[default is %s]\n"), (default_arch_size == 64) ? "RMO" : "TSO");
  
  fprintf (stream, _("\
-KPIC			generate PIC\n\
-V			print assembler version number\n\
-undeclared-regs	ignore application global register usage without\n\
			appropriate .register directive (default)\n\
-no-undeclared-regs	force error on application global register usage\n\
			without appropriate .register directive\n\
--dcti-couples-detect	warn when an unpredictable DCTI couple is found\n\
-q			ignored\n\
-Qy, -Qn		ignored\n\
-s			ignored\n"));
  
#ifdef SPARC_BIENDIAN
  fprintf (stream, _("\
-EL			generate code for a little endian machine\n\
-EB			generate code for a big endian machine\n\
--little-endian-data	generate code for a machine having big endian\n\
                        instructions and little endian data.\n"));
#endif
}

/* Native operand size opcode translation.  */
static struct
  {
    const char *name;
    const char *name32;
    const char *name64;
  } native_op_table[] =
{
  {"ldn", "ld", "ldx"},
  {"ldna", "lda", "ldxa"},
  {"stn", "st", "stx"},
  {"stna", "sta", "stxa"},
  {"slln", "sll", "sllx"},
  {"srln", "srl", "srlx"},
  {"sran", "sra", "srax"},
  {"casn", "cas", "casx"},
  {"casna", "casa", "casxa"},
  {"clrn", "clr", "clrx"},
  {NULL, NULL, NULL},
};

/* sparc64 privileged and hyperprivileged registers.  */

struct priv_reg_entry
{
  const char *name;
  int regnum;
};

struct priv_reg_entry priv_reg_table[] =
{
  {"tpc", 0},
  {"tnpc", 1},
  {"tstate", 2},
  {"tt", 3},
  {"tick", 4},
  {"tba", 5},
  {"pstate", 6},
  {"tl", 7},
  {"pil", 8},
  {"cwp", 9},
  {"cansave", 10},
  {"canrestore", 11},
  {"cleanwin", 12},
  {"otherwin", 13},
  {"wstate", 14},
  {"fq", 15},
  {"gl", 16},
  {"pmcdper", 23},
  {"ver", 31},
  {NULL, -1},			/* End marker.  */
};

struct priv_reg_entry hpriv_reg_table[] =
{
  {"hpstate", 0},
  {"htstate", 1},
  {"hintp", 3},
  {"htba", 5},
  {"hver", 6},
  {"hmcdper", 23},
  {"hmcddfr", 24},
  {"hva_mask_nz", 27},
  {"hstick_offset", 28},
  {"hstick_enable", 29},
  {"hstick_cmpr", 31},
  {NULL, -1},			/* End marker.  */
};

/* v9a or later specific ancillary state registers. */

struct priv_reg_entry v9a_asr_table[] =
{
  {"tick_cmpr", 23},
  {"sys_tick_cmpr", 25},
  {"sys_tick", 24},
  {"stick_cmpr", 25},
  {"stick", 24},
  {"softint_clear", 21},
  {"softint_set", 20},
  {"softint", 22},
  {"set_softint", 20},
  {"pause", 27},
  {"pic", 17},
  {"pcr", 16},
  {"mwait", 28},
  {"gsr", 19},
  {"dcr", 18},
  {"cfr", 26},
  {"clear_softint", 21},
  {NULL, -1},			/* End marker.  */
};

static int
cmp_reg_entry (const void *parg, const void *qarg)
{
  const struct priv_reg_entry *p = parg;
  const struct priv_reg_entry *q = qarg;

  if (p->name == q->name)
    return 0;
  
  if (p->name == NULL)
    return 1;
  
  if (q->name == NULL)
    return -1;
  
  return strcmp (q->name, p->name);
}

/* sparc %-pseudo-operations.  */


#define F_POP_V9       0x1 /* The pseudo-op is for v9 only.  */
#define F_POP_PCREL    0x2 /* The pseudo-op can be used in pc-relative
                              contexts.  */
#define F_POP_TLS_CALL 0x4 /* The pseudo-op marks a tls call.  */
#define F_POP_POSTFIX  0x8 /* The pseudo-op should appear after the
                              last operand of an
                              instruction. (Generally they can appear
                              anywhere an immediate operand is
                              expected.  */
struct pop_entry
{
  /* The name as it appears in assembler.  */
  const char *name;
  /* The reloc this pseudo-op translates to.  */
  bfd_reloc_code_real_type reloc;
  /* Flags.  See F_POP_* above.  */
  int flags;
};

struct pop_entry pop_table[] =
{
  { "hix",		BFD_RELOC_SPARC_HIX22,		F_POP_V9 },
  { "lox",		BFD_RELOC_SPARC_LOX10, 		F_POP_V9 },
  { "hi",		BFD_RELOC_HI22,			F_POP_PCREL },
  { "lo",		BFD_RELOC_LO10,			F_POP_PCREL },
  { "pc22",		BFD_RELOC_SPARC_PC22,		F_POP_PCREL },
  { "pc10",		BFD_RELOC_SPARC_PC10,		F_POP_PCREL },
  { "hh",		BFD_RELOC_SPARC_HH22,		F_POP_V9|F_POP_PCREL },
  { "hm",		BFD_RELOC_SPARC_HM10,		F_POP_V9|F_POP_PCREL },
  { "lm",		BFD_RELOC_SPARC_LM22,		F_POP_V9|F_POP_PCREL },
  { "h34",		BFD_RELOC_SPARC_H34,		F_POP_V9 },
  { "l34",		BFD_RELOC_SPARC_L44,		F_POP_V9 },
  { "h44",		BFD_RELOC_SPARC_H44,		F_POP_V9 },
  { "m44",		BFD_RELOC_SPARC_M44,		F_POP_V9 },
  { "l44",		BFD_RELOC_SPARC_L44,		F_POP_V9 },
  { "uhi",		BFD_RELOC_SPARC_HH22,		F_POP_V9 },
  { "ulo",		BFD_RELOC_SPARC_HM10,		F_POP_V9 },
  { "tgd_hi22",		BFD_RELOC_SPARC_TLS_GD_HI22, 	0 },
  { "tgd_lo10",		BFD_RELOC_SPARC_TLS_GD_LO10, 	0 },
  { "tldm_hi22",	BFD_RELOC_SPARC_TLS_LDM_HI22, 	0 },
  { "tldm_lo10",	BFD_RELOC_SPARC_TLS_LDM_LO10, 	0 },
  { "tldo_hix22",	BFD_RELOC_SPARC_TLS_LDO_HIX22, 	0 },
  { "tldo_lox10",	BFD_RELOC_SPARC_TLS_LDO_LOX10, 	0 },
  { "tie_hi22",		BFD_RELOC_SPARC_TLS_IE_HI22, 	0 },
  { "tie_lo10",		BFD_RELOC_SPARC_TLS_IE_LO10, 	0 },
  { "tle_hix22",	BFD_RELOC_SPARC_TLS_LE_HIX22, 	0 },
  { "tle_lox10",	BFD_RELOC_SPARC_TLS_LE_LOX10, 	0 },
  { "gdop_hix22",	BFD_RELOC_SPARC_GOTDATA_OP_HIX22, 0 },
  { "gdop_lox10",	BFD_RELOC_SPARC_GOTDATA_OP_LOX10, 0 },
  { "tgd_add", 		BFD_RELOC_SPARC_TLS_GD_ADD,	F_POP_POSTFIX },
  { "tgd_call",		BFD_RELOC_SPARC_TLS_GD_CALL, 	F_POP_POSTFIX|F_POP_TLS_CALL },
  { "tldm_add",		BFD_RELOC_SPARC_TLS_LDM_ADD, 	F_POP_POSTFIX },
  { "tldm_call",	BFD_RELOC_SPARC_TLS_LDM_CALL,	F_POP_POSTFIX|F_POP_TLS_CALL },
  { "tldo_add",		BFD_RELOC_SPARC_TLS_LDO_ADD, 	F_POP_POSTFIX },
  { "tie_ldx",		BFD_RELOC_SPARC_TLS_IE_LDX, 	F_POP_POSTFIX },
  { "tie_ld",		BFD_RELOC_SPARC_TLS_IE_LD,	F_POP_POSTFIX },
  { "tie_add",		BFD_RELOC_SPARC_TLS_IE_ADD,	F_POP_POSTFIX },
  { "gdop",	 	BFD_RELOC_SPARC_GOTDATA_OP,	F_POP_POSTFIX }
};

/* Table of %-names that can appear in a sparc assembly program.  This
   table is initialized in md_begin and contains entries for each
   privileged/hyperprivileged/alternate register and %-pseudo-op.  */

enum perc_entry_type
{
  perc_entry_none = 0,
  perc_entry_reg,
  perc_entry_post_pop,
  perc_entry_imm_pop
};

struct perc_entry
{
  /* Entry type.  */
  enum perc_entry_type type;
  /* Name of the %-entity.  */
  const char *name;
  /* strlen (name).  */
  int len;
  /* Value.  Either a pop or a reg depending on type.*/
  union
  {
    struct pop_entry *pop;
    struct priv_reg_entry *reg;
  };
};

#define NUM_PERC_ENTRIES \
  (((sizeof (priv_reg_table) / sizeof (priv_reg_table[0])) - 1)         \
   + ((sizeof (hpriv_reg_table) / sizeof (hpriv_reg_table[0])) - 1)     \
   + ((sizeof (v9a_asr_table) / sizeof (v9a_asr_table[0])) - 1)         \
   + ARRAY_SIZE (pop_table)						\
   + 1)

struct perc_entry perc_table[NUM_PERC_ENTRIES];

static int
cmp_perc_entry (const void *parg, const void *qarg)
{
  const struct perc_entry *p = parg;
  const struct perc_entry *q = qarg;

  if (p->name == q->name)
    return 0;
  
  if (p->name == NULL)
    return 1;
  
  if (q->name == NULL)
    return -1;
  
  return strcmp (q->name, p->name);
}

/* This function is called once, at assembler startup time.  It should
   set up all the tables, etc. that the MD part of the assembler will
   need.  */

#define CIE_DATA_ALIGNMENT_64 -8
#define CIE_DATA_ALIGNMENT_32 -4
#define ARCH_SIZE_32 32
#define ARCH_SIZE_64 64

static int insert_opcode(const struct sparc_opcode *opcode, const char *name)
{
    if (str_hash_insert(op_hash, name, opcode, 0) != NULL) {
        as_bad(_("duplicate %s"), name);
        return 1;
    }
    return 0;
}

static int validate_opcode(const struct sparc_opcode *opcode)
{
    if (opcode->match & opcode->lose) {
        as_bad(_("Internal error: losing opcode: `%s' \"%s\"\n"),
               opcode->name, opcode->args);
        return 1;
    }
    return 0;
}

static int process_sparc_opcodes(void)
{
    int lose = 0;
    unsigned int i = 0;
    
    while (i < (unsigned int)sparc_num_opcodes) {
        const char *name = sparc_opcodes[i].name;
        lose |= insert_opcode(&sparc_opcodes[i], name);
        
        do {
            lose |= validate_opcode(&sparc_opcodes[i]);
            ++i;
        } while (i < (unsigned int)sparc_num_opcodes && 
                 !strcmp(sparc_opcodes[i].name, name));
    }
    
    return lose;
}

static int process_native_opcodes(void)
{
    int lose = 0;
    
    for (int i = 0; native_op_table[i].name; i++) {
        const char *name = (sparc_arch_size == ARCH_SIZE_32)
                          ? native_op_table[i].name32
                          : native_op_table[i].name64;
        
        const struct sparc_opcode *insn = str_hash_find(op_hash, name);
        
        if (insn == NULL) {
            as_bad(_("Internal error: can't find opcode `%s' for `%s'\n"),
                   name, native_op_table[i].name);
            lose = 1;
        } else {
            lose |= insert_opcode(insn, native_op_table[i].name);
        }
    }
    
    return lose;
}

static void sort_register_table(void *table, size_t element_count)
{
    qsort(table, element_count, sizeof(struct priv_reg_entry), cmp_reg_entry);
}

static void sort_register_tables(void)
{
    sort_register_table(priv_reg_table, 
                       sizeof(priv_reg_table) / sizeof(priv_reg_table[0]));
    sort_register_table(hpriv_reg_table, 
                       sizeof(hpriv_reg_table) / sizeof(hpriv_reg_table[0]));
    sort_register_table(v9a_asr_table, 
                       sizeof(v9a_asr_table) / sizeof(v9a_asr_table[0]));
}

static void setup_warn_architecture(void)
{
    if (warn_on_bump && architecture_requested) {
        warn_after_architecture = max_architecture;
    }
}

static void find_max_architecture(void)
{
    if (!warn_on_bump && architecture_requested)
        return;
    
    enum sparc_opcode_arch_val current_max_architecture = max_architecture;
    
    for (max_architecture = SPARC_OPCODE_ARCH_MAX;
         max_architecture > warn_after_architecture;
         --max_architecture) {
        if (!SPARC_OPCODE_CONFLICT_P(max_architecture, current_max_architecture))
            break;
    }
}

static int add_register_entries(struct priv_reg_entry **reg_tables, int entry)
{
    for (struct priv_reg_entry **reg_table = reg_tables; *reg_table; reg_table++) {
        for (struct priv_reg_entry *reg = *reg_table; reg->name; reg++) {
            struct perc_entry *p = &perc_table[entry++];
            p->type = perc_entry_reg;
            p->name = reg->name;
            p->len = strlen(reg->name);
            p->reg = reg;
        }
    }
    return entry;
}

static int add_pop_entries(int entry)
{
    for (unsigned int i = 0; i < ARRAY_SIZE(pop_table); i++) {
        struct perc_entry *p = &perc_table[entry++];
        p->type = (pop_table[i].flags & F_POP_POSTFIX)
                  ? perc_entry_post_pop : perc_entry_imm_pop;
        p->name = pop_table[i].name;
        p->len = strlen(pop_table[i].name);
        p->pop = &pop_table[i];
    }
    return entry;
}

static void prepare_perc_table(void)
{
    struct priv_reg_entry *reg_tables[] = 
        {priv_reg_table, hpriv_reg_table, v9a_asr_table, NULL};
    int entry = 0;
    
    entry = add_register_entries(reg_tables, entry);
    entry = add_pop_entries(entry);
    
    perc_table[entry].type = perc_entry_none;
    
    qsort(perc_table, sizeof(perc_table) / sizeof(perc_table[0]),
          sizeof(perc_table[0]), cmp_perc_entry);
}

void md_begin(void)
{
    int lose = 0;
    
    if (!default_init_p)
        init_default_arch();
    
    sparc_cie_data_alignment = (sparc_arch_size == ARCH_SIZE_64) 
                              ? CIE_DATA_ALIGNMENT_64 
                              : CIE_DATA_ALIGNMENT_32;
    op_hash = str_htab_create();
    
    lose |= process_sparc_opcodes();
    lose |= process_native_opcodes();
    
    if (lose)
        as_fatal(_("Broken assembler.  No assembly attempted."));
    
    sort_register_tables();
    setup_warn_architecture();
    find_max_architecture();
    prepare_perc_table();
}

/* Called after all assembly has been done.  */

void
sparc_md_finish (void)
{
  unsigned long mach = get_machine_type();
  bfd_set_arch_mach (stdoutput, bfd_arch_sparc, mach);
  
#ifndef TE_SOLARIS
  add_hardware_capabilities();
#endif
}

static unsigned long
get_machine_type (void)
{
  if (sparc_arch_size == 64)
    return get_64bit_machine();
  return get_32bit_machine();
}

static unsigned long
get_64bit_machine (void)
{
  switch (current_architecture)
    {
    case SPARC_OPCODE_ARCH_V9A: return bfd_mach_sparc_v9a;
    case SPARC_OPCODE_ARCH_V9B: return bfd_mach_sparc_v9b;
    case SPARC_OPCODE_ARCH_V9C: return bfd_mach_sparc_v9c;
    case SPARC_OPCODE_ARCH_V9D: return bfd_mach_sparc_v9d;
    case SPARC_OPCODE_ARCH_V9E: return bfd_mach_sparc_v9e;
    case SPARC_OPCODE_ARCH_V9V: return bfd_mach_sparc_v9v;
    case SPARC_OPCODE_ARCH_V9M: return bfd_mach_sparc_v9m;
    case SPARC_OPCODE_ARCH_M8:  return bfd_mach_sparc_v9m8;
    default: return bfd_mach_sparc_v9;
    }
}

static unsigned long
get_32bit_machine (void)
{
  switch (current_architecture)
    {
    case SPARC_OPCODE_ARCH_SPARCLET: return bfd_mach_sparc_sparclet;
    case SPARC_OPCODE_ARCH_V9: return bfd_mach_sparc_v8plus;
    case SPARC_OPCODE_ARCH_V9A: return bfd_mach_sparc_v8plusa;
    case SPARC_OPCODE_ARCH_V9B: return bfd_mach_sparc_v8plusb;
    case SPARC_OPCODE_ARCH_V9C: return bfd_mach_sparc_v8plusc;
    case SPARC_OPCODE_ARCH_V9D: return bfd_mach_sparc_v8plusd;
    case SPARC_OPCODE_ARCH_V9E: return bfd_mach_sparc_v8pluse;
    case SPARC_OPCODE_ARCH_V9V: return bfd_mach_sparc_v8plusv;
    case SPARC_OPCODE_ARCH_V9M: return bfd_mach_sparc_v8plusm;
    case SPARC_OPCODE_ARCH_M8:  return bfd_mach_sparc_v8plusm8;
    default: return bfd_mach_sparc;
    }
}

#ifndef TE_SOLARIS
#define HWCAP_MASK 0xffffffff
#define HWCAP2_SHIFT 32

static void
add_hardware_capabilities (void)
{
  int hwcaps = hwcap_seen & HWCAP_MASK;
  int hwcaps2 = hwcap_seen >> HWCAP2_SHIFT;
  
  if (hwcaps)
    add_hwcap_attribute(Tag_GNU_Sparc_HWCAPS, hwcaps);
  
  if (hwcaps2)
    add_hwcap_attribute(Tag_GNU_Sparc_HWCAPS2, hwcaps2);
}

static void
add_hwcap_attribute (int tag, int value)
{
  if (!bfd_elf_add_obj_attr_int (stdoutput, OBJ_ATTR_GNU, tag, value))
    as_fatal (_("error adding attribute: %s"),
              bfd_errmsg (bfd_get_error ()));
}
#endif

/* Return non-zero if VAL is in the range -(MAX+1) to MAX.  */

static inline int
in_signed_range (bfd_signed_vma val, bfd_signed_vma max)
{
  if (max <= 0)
    abort ();
  
  if (sparc_arch_size == 32)
    val = sign_extend_32bit(val);
  
  return val <= max && val >= ~max;
}

static inline bfd_signed_vma
sign_extend_32bit(bfd_signed_vma val)
{
  #define SIGN_BIT_32 ((bfd_vma) 1 << 31)
  #define MASK_32BIT U0xffffffff
  
  return ((val & MASK_32BIT) ^ SIGN_BIT_32) - SIGN_BIT_32;
}

/* Return non-zero if VAL is in the range 0 to MAX.  */

static inline int
in_unsigned_range (bfd_vma val, bfd_vma max)
{
  return val <= max;
}

/* Return non-zero if VAL is in the range -(MAX/2+1) to MAX.
   (e.g. -15 to +31).  */

static inline int
in_bitfield_range (bfd_signed_vma val, bfd_signed_vma max)
{
  if (max <= 0)
    abort ();
  
  bfd_signed_vma min = ~(max >> 1);
  return (val <= max && val >= min);
}

static int sparc_ffs(unsigned int mask)
{
    if (mask == 0)
        return -1;

    int i = 0;
    while ((mask & 1) == 0)
    {
        mask >>= 1;
        ++i;
    }
    return i;
}

/* Implement big shift right.  */
static bfd_vma
BSR (bfd_vma val, int amount)
{
  #define BFD_VMA_32BIT_SIZE 4
  #define MAX_SHIFT_32BIT 32
  
  if (sizeof (bfd_vma) <= BFD_VMA_32BIT_SIZE && amount >= MAX_SHIFT_32BIT)
    as_fatal (_("Support for 64-bit arithmetic not compiled in."));
  return val >> amount;
}

/* For communication between sparc_ip and get_expression.  */
static char *expr_parse_end;

/* Values for `special_case'.
   Instructions that require weird handling because they're longer than
   4 bytes.  */
#define SPECIAL_CASE_NONE	0
#define	SPECIAL_CASE_SET	1
#define SPECIAL_CASE_SETSW	2
#define SPECIAL_CASE_SETX	3
/* FIXME: sparc-opc.c doesn't have necessary "S" trigger to enable this.  */
#define	SPECIAL_CASE_FDIV	4

/* Bit masks of various insns.  */
#define NOP_INSN 0x01000000
#define OR_INSN 0x80100000
#define XOR_INSN 0x80180000
#define FMOVS_INSN 0x81A00020
#define SETHI_INSN 0x01000000
#define SLLX_INSN 0x81281000
#define SRA_INSN 0x81380000

/* The last instruction to be assembled.  */
static const struct sparc_opcode *last_insn;
/* The assembled opcode of `last_insn'.  */
static unsigned long last_opcode;

/* Handle the set and setuw synthetic instructions.  */

static void check_constant_range(void)
{
    if (the_insn.exp.X_op != O_constant)
        return;
        
    if (SPARC_OPCODE_ARCH_V9_P(max_architecture))
    {
        if (sizeof(offsetT) > 4 &&
            (the_insn.exp.X_add_number < 0 ||
             the_insn.exp.X_add_number > (offsetT)U0xffffffff))
        {
            as_warn(_("set: number not in 0..4294967295 range"));
        }
    }
    else
    {
        if (sizeof(offsetT) > 4 &&
            (the_insn.exp.X_add_number < -(offsetT)U0x80000000 ||
             the_insn.exp.X_add_number > (offsetT)U0xffffffff))
        {
            as_warn(_("set: number not in -2147483648..4294967295 range"));
        }
        the_insn.exp.X_add_number = (int32_t)the_insn.exp.X_add_number;
    }
}

static int is_small_absolute_operand(void)
{
    #define SMALL_OPERAND_LIMIT (1 << 12)
    
    return the_insn.exp.X_op == O_constant &&
           the_insn.exp.X_add_number < SMALL_OPERAND_LIMIT &&
           the_insn.exp.X_add_number >= -SMALL_OPERAND_LIMIT;
}

static void emit_sethi_instruction(const struct sparc_opcode *insn, int rd)
{
    #define SETHI_MASK 0x3fffff
    
    int is_constant = (the_insn.exp.X_op == O_constant);
    
    the_insn.opcode = SETHI_INSN | RD(rd) |
                      ((the_insn.exp.X_add_number >> 10) & 
                       (is_constant ? SETHI_MASK : 0));
                       
    the_insn.reloc = is_constant ? BFD_RELOC_NONE : BFD_RELOC_HI22;
    output_insn(insn, &the_insn);
}

static int has_low_order_bits(void)
{
    #define LOW_ORDER_MASK 0x3FF
    
    return the_insn.exp.X_op != O_constant ||
           (the_insn.exp.X_add_number & LOW_ORDER_MASK) != 0;
}

static void emit_or_instruction(const struct sparc_opcode *insn, int rd, int need_hi22_p)
{
    #define OR_LOW_MASK 0x3ff
    #define OR_FULL_MASK 0x1fff
    
    int is_constant = (the_insn.exp.X_op == O_constant);
    int mask_value = is_constant ? (need_hi22_p ? OR_LOW_MASK : OR_FULL_MASK) : 0;
    
    the_insn.opcode = OR_INSN | (need_hi22_p ? RS1(rd) : 0) |
                      RD(rd) | IMMED |
                      (the_insn.exp.X_add_number & mask_value);
                      
    the_insn.reloc = is_constant ? BFD_RELOC_NONE : BFD_RELOC_LO10;
    output_insn(insn, &the_insn);
}

static int should_emit_or_instruction(int need_hi22_p)
{
    return the_insn.exp.X_op != O_constant ||
           (need_hi22_p && has_low_order_bits()) ||
           !need_hi22_p;
}

static void synthetize_setuw(const struct sparc_opcode *insn)
{
    int need_hi22_p = 0;
    int rd = (the_insn.opcode & RD(~0)) >> 25;

    check_constant_range();

    if (!is_small_absolute_operand())
    {
        emit_sethi_instruction(insn, rd);
        need_hi22_p = 1;
    }

    if (should_emit_or_instruction(need_hi22_p))
    {
        emit_or_instruction(insn, rd, need_hi22_p);
    }
}

/* Handle the setsw synthetic instruction.  */

static void handle_non_constant_expression(const struct sparc_opcode *insn, int rd)
{
    synthetize_setuw(insn);
    the_insn.opcode = (SRA_INSN | RS1(rd) | RD(rd));
    the_insn.reloc = BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void check_setsw_range(offsetT value)
{
    #define MIN_SETSW_VALUE (-(offsetT)U0x80000000)
    #define MAX_SETSW_VALUE ((offsetT)U0xffffffff)
    
    if (sizeof(offsetT) > 4 && (value < MIN_SETSW_VALUE || value > MAX_SETSW_VALUE))
        as_warn(_("setsw: number not in -2147483648..4294967295 range"));
}

static void handle_large_negative_value(const struct sparc_opcode *insn, int rd, int low32)
{
    #define SETHI_MASK 0x3fffff
    #define LOW_10_BITS 0x3ff
    #define XOR_CONSTANT 0x1c00
    #define SHIFT_10 10
    
    the_insn.opcode = (SETHI_INSN | RD(rd) | (((~the_insn.exp.X_add_number) >> SHIFT_10) & SETHI_MASK));
    output_insn(insn, &the_insn);
    
    int adjusted_low32 = XOR_CONSTANT | (low32 & LOW_10_BITS);
    the_insn.opcode = (RS1(rd) | XOR_INSN | RD(rd) | IMMED | (adjusted_low32 & 0x1fff));
    output_insn(insn, &the_insn);
}

static void handle_small_negative_value(const struct sparc_opcode *insn, int rd, int low32)
{
    #define IMMED_MASK 0x1fff
    
    the_insn.opcode = (OR_INSN | RD(rd) | IMMED | (low32 & IMMED_MASK));
    output_insn(insn, &the_insn);
}

static void synthetize_setsw(const struct sparc_opcode *insn)
{
    #define RD_SHIFT 25
    #define SMALL_NEGATIVE_THRESHOLD (-(1 << 12))
    
    int rd = (the_insn.opcode & RD(~0)) >> RD_SHIFT;
    
    if (the_insn.exp.X_op != O_constant)
    {
        handle_non_constant_expression(insn, rd);
        return;
    }
    
    check_setsw_range(the_insn.exp.X_add_number);
    
    int low32 = the_insn.exp.X_add_number;
    
    if (low32 >= 0)
    {
        synthetize_setuw(insn);
        return;
    }
    
    the_insn.reloc = BFD_RELOC_NONE;
    
    if (low32 < SMALL_NEGATIVE_THRESHOLD)
        handle_large_negative_value(insn, rd, low32);
    else
        handle_small_negative_value(insn, rd, low32);
}

/* Handle the setx synthetic instruction.  */

static int signext32(int x) {
    return ((x & U0xffffffff) ^ U0x80000000) - U0x80000000;
}

static void extract_registers(int *tmpreg, int *dstreg) {
    *tmpreg = (the_insn.opcode & RS1(~0)) >> 14;
    *dstreg = (the_insn.opcode & RD(~0)) >> 25;
}

static void check_register_conflict(int tmpreg, int dstreg) {
    if (tmpreg == dstreg)
        as_warn(_("setx: temporary register same as destination register"));
}

static void handle_32bit_arch(const struct sparc_opcode *insn) {
    the_insn.exp.X_add_number &= 0xffffffff;
    synthetize_setuw(insn);
}

static int needs_hh22(int upper32) {
    return upper32 < -(1 << 12) || upper32 >= (1 << 12);
}

static int needs_hm10(int upper32, int need_hh22_p) {
    return (need_hh22_p && (upper32 & 0x3ff) != 0) ||
           (!need_hh22_p && upper32 != 0 && upper32 != -1);
}

static int needs_hi22(int lower32, int upper32) {
    return lower32 < -(1 << 12) || lower32 >= (1 << 12) ||
           (lower32 < 0 && upper32 != -1) ||
           (lower32 >= 0 && upper32 == -1);
}

static int needs_lo10(int lower32, int need_hi22_p, int need_hh22_p, int need_hm10_p) {
    return (need_hi22_p && (lower32 & 0x3ff) != 0) ||
           (!need_hi22_p && (lower32 & 0x1fff) != 0) ||
           (!need_hi22_p && !need_hh22_p && !need_hm10_p);
}

static void determine_needs_for_constant(int upper32, int lower32, 
                                        int *need_hh22_p, int *need_hm10_p, 
                                        int *need_hi22_p, int *need_lo10_p, 
                                        int *need_xor10_p, int *upper_dstreg, 
                                        int dstreg) {
    *need_hh22_p = needs_hh22(upper32);
    *need_hm10_p = needs_hm10(upper32, *need_hh22_p);
    
    if (lower32 != 0 || (!*need_hh22_p && !*need_hm10_p)) {
        *need_hi22_p = needs_hi22(lower32, upper32);
        
        if (*need_hi22_p && upper32 == -1) {
            *need_xor10_p = 1;
        } else {
            *need_lo10_p = needs_lo10(lower32, *need_hi22_p, *need_hh22_p, *need_hm10_p);
        }
    } else {
        *upper_dstreg = dstreg;
    }
}

static void output_hh22_instruction(const struct sparc_opcode *insn, int upper_dstreg, int upper32) {
    the_insn.opcode = SETHI_INSN | RD(upper_dstreg) | ((upper32 >> 10) & 0x3fffff);
    the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_SPARC_HH22 : BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void output_hi22_instruction(const struct sparc_opcode *insn, int dstreg, int lower32, int need_xor10_p) {
    int value = need_xor10_p ? ~lower32 : lower32;
    the_insn.opcode = SETHI_INSN | RD(dstreg) | ((value >> 10) & 0x3fffff);
    the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_SPARC_LM22 : BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void output_hm10_instruction(const struct sparc_opcode *insn, int upper_dstreg, int upper32, int need_hh22_p) {
    the_insn.opcode = OR_INSN | (need_hh22_p ? RS1(upper_dstreg) : 0) | 
                     RD(upper_dstreg) | IMMED | (upper32 & (need_hh22_p ? 0x3ff : 0x1fff));
    the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_SPARC_HM10 : BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void output_lo10_instruction(const struct sparc_opcode *insn, int dstreg, int lower32, int need_hi22_p) {
    the_insn.opcode = OR_INSN | (need_hi22_p ? RS1(dstreg) : 0) | 
                     RD(dstreg) | IMMED | (lower32 & (need_hi22_p ? 0x3ff : 0x1fff));
    the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_LO10 : BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void output_shift_instruction(const struct sparc_opcode *insn, int upper_dstreg) {
    the_insn.opcode = SLLX_INSN | RS1(upper_dstreg) | RD(upper_dstreg) | IMMED | 32;
    the_insn.reloc = BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void output_xor10_instruction(const struct sparc_opcode *insn, int dstreg, int lower32) {
    the_insn.opcode = XOR_INSN | RS1(dstreg) | RD(dstreg) | IMMED | 0x1c00 | (lower32 & 0x3ff);
    the_insn.reloc = BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void output_final_or_instruction(const struct sparc_opcode *insn, int dstreg, int upper_dstreg) {
    the_insn.opcode = OR_INSN | RS1(dstreg) | RS2(upper_dstreg) | RD(dstreg);
    the_insn.reloc = BFD_RELOC_NONE;
    output_insn(insn, &the_insn);
}

static void synthetize_setx(const struct sparc_opcode *insn) {
    int tmpreg, dstreg, upper_dstreg;
    int lower32, upper32;
    int need_hh22_p = 0, need_hm10_p = 0, need_hi22_p = 0, need_lo10_p = 0;
    int need_xor10_p = 0;
    
    extract_registers(&tmpreg, &dstreg);
    check_register_conflict(tmpreg, dstreg);
    
    lower32 = signext32(the_insn.exp.X_add_number);
    upper32 = signext32(BSR(the_insn.exp.X_add_number, 32));
    upper_dstreg = tmpreg;
    
    if (the_insn.exp.X_op != O_constant) {
        if (sparc_arch_size == 32) {
            handle_32bit_arch(insn);
            return;
        }
        need_hh22_p = need_hm10_p = need_hi22_p = need_lo10_p = 1;
        lower32 = 0;
        upper32 = 0;
    } else {
        the_insn.exp.X_add_number = 0;
        determine_needs_for_constant(upper32, lower32, &need_hh22_p, &need_hm10_p,
                                    &need_hi22_p, &need_lo10_p, &need_xor10_p,
                                    &upper_dstreg, dstreg);
    }
    
    if (!upper_dstreg && dstreg)
        as_warn(_("setx: illegal temporary register g0"));
    
    if (need_hh22_p)
        output_hh22_instruction(insn, upper_dstreg, upper32);
    
    if (need_hi22_p)
        output_hi22_instruction(insn, dstreg, lower32, need_xor10_p);
    
    if (need_hm10_p)
        output_hm10_instruction(insn, upper_dstreg, upper32, need_hh22_p);
    
    if (need_lo10_p)
        output_lo10_instruction(insn, dstreg, lower32, need_hi22_p);
    
    if (need_hh22_p || need_hm10_p)
        output_shift_instruction(insn, upper_dstreg);
    
    if (need_xor10_p)
        output_xor10_instruction(insn, dstreg, lower32);
    else if ((need_hh22_p || need_hm10_p) && (need_hi22_p || need_lo10_p))
        output_final_or_instruction(insn, dstreg, upper_dstreg);
}

/* Main entry point to assemble one instruction.  */

void
md_assemble (char *str)
{
  const struct sparc_opcode *insn;
  int special_case;

  know (str);
  special_case = sparc_ip (str, &insn);
  if (insn == NULL)
    return;

  check_delay_slot_restrictions(insn);
  handle_fp_compare_before_branch(insn);
  process_special_case(special_case, insn);
}

static void
check_delay_slot_restrictions(const struct sparc_opcode *insn)
{
  if (last_insn == NULL || (last_insn->flags & F_DELAYED) == 0)
    return;

  check_dcti_couple(insn);
  check_fp_branch_in_delay_slot(insn);
}

static void
check_dcti_couple(const struct sparc_opcode *insn)
{
  if (!dcti_couples_detect || (insn->flags & F_DELAYED) == 0)
    return;

  if (is_deprecated_dcti_couple())
    as_warn (_("unpredictable DCTI couple"));
}

static int
is_deprecated_dcti_couple(void)
{
  return (max_architecture < SPARC_OPCODE_ARCH_V9 && (last_insn->flags & F_CONDBR) != 0) ||
         max_architecture >= SPARC_OPCODE_ARCH_V9C;
}

static void
check_fp_branch_in_delay_slot(const struct sparc_opcode *insn)
{
  if ((insn->flags & F_FBR) == 0)
    return;

  if (is_non_annulled_delay_slot())
    as_warn (_("FP branch in delay slot"));
}

static int
is_non_annulled_delay_slot(void)
{
  return ((last_insn->flags & (F_UNBR | F_CONDBR | F_FBR)) == 0 ||
          (last_opcode & ANNUL) == 0);
}

static void
handle_fp_compare_before_branch(const struct sparc_opcode *insn)
{
  if (!needs_nop_after_fp_compare(insn))
    return;

  insert_nop_instruction(insn);
  as_warn (_("FP branch preceded by FP compare; NOP inserted"));
}

static int
needs_nop_after_fp_compare(const struct sparc_opcode *insn)
{
  return max_architecture < SPARC_OPCODE_ARCH_V9 &&
         last_insn != NULL &&
         (insn->flags & F_FBR) != 0 &&
         (last_insn->flags & F_FLOAT) != 0 &&
         (last_insn->match & OP3 (0x35)) == OP3 (0x35);
}

static void
insert_nop_instruction(const struct sparc_opcode *insn)
{
  struct sparc_it nop_insn;
  nop_insn.opcode = NOP_INSN;
  nop_insn.reloc = BFD_RELOC_NONE;
  output_insn (insn, &nop_insn);
}

static void
process_special_case(int special_case, const struct sparc_opcode *insn)
{
  switch (special_case)
    {
    case SPECIAL_CASE_NONE:
      output_insn (insn, &the_insn);
      break;

    case SPECIAL_CASE_SETSW:
      synthetize_setsw (insn);
      break;

    case SPECIAL_CASE_SET:
      synthetize_setuw (insn);
      break;

    case SPECIAL_CASE_SETX:
      synthetize_setx (insn);
      break;

    case SPECIAL_CASE_FDIV:
      handle_fdiv_special_case(insn);
      break;

    default:
      as_fatal (_("failed special case insn sanity check"));
    }
}

static void
handle_fdiv_special_case(const struct sparc_opcode *insn)
{
  #define RD_SHIFT 25
  #define RD_MASK 0x1f
  
  int rd = (the_insn.opcode >> RD_SHIFT) & RD_MASK;
  
  output_insn (insn, &the_insn);
  
  gas_assert (the_insn.reloc == BFD_RELOC_NONE);
  the_insn.opcode = FMOVS_INSN | rd | RD (rd);
  output_insn (insn, &the_insn);
}

static const char *
get_hwcap_name (uint64_t mask)
{
  static const struct {
    uint64_t flag;
    const char *name;
  } hwcap_map[] = {
    {HWCAP_MUL32, "mul32"},
    {HWCAP_DIV32, "div32"},
    {HWCAP_FSMULD, "fsmuld"},
    {HWCAP_V8PLUS, "v8plus"},
    {HWCAP_POPC, "popc"},
    {HWCAP_VIS, "vis"},
    {HWCAP_VIS2, "vis2"},
    {HWCAP_ASI_BLK_INIT, "ASIBlkInit"},
    {HWCAP_FMAF, "fmaf"},
    {HWCAP_VIS3, "vis3"},
    {HWCAP_HPC, "hpc"},
    {HWCAP_RANDOM, "random"},
    {HWCAP_TRANS, "trans"},
    {HWCAP_FJFMAU, "fjfmau"},
    {HWCAP_IMA, "ima"},
    {HWCAP_ASI_CACHE_SPARING, "cspare"},
    {HWCAP_AES, "aes"},
    {HWCAP_DES, "des"},
    {HWCAP_KASUMI, "kasumi"},
    {HWCAP_CAMELLIA, "camellia"},
    {HWCAP_MD5, "md5"},
    {HWCAP_SHA1, "sha1"},
    {HWCAP_SHA256, "sha256"},
    {HWCAP_SHA512, "sha512"},
    {HWCAP_MPMUL, "mpmul"},
    {HWCAP_MONT, "mont"},
    {HWCAP_PAUSE, "pause"},
    {HWCAP_CBCOND, "cbcond"},
    {HWCAP_CRC32C, "crc32c"},
    {0, NULL}
  };

  static const struct {
    uint64_t flag;
    const char *name;
  } hwcap2_map[] = {
    {HWCAP2_FJATHPLUS, "fjathplus"},
    {HWCAP2_VIS3B, "vis3b"},
    {HWCAP2_ADP, "adp"},
    {HWCAP2_SPARC5, "sparc5"},
    {HWCAP2_MWAIT, "mwait"},
    {HWCAP2_XMPMUL, "xmpmul"},
    {HWCAP2_XMONT, "xmont"},
    {HWCAP2_NSEC, "nsec"},
    {HWCAP2_SPARC6, "sparc6"},
    {HWCAP2_ONADDSUB, "onaddsub"},
    {HWCAP2_ONMUL, "onmul"},
    {HWCAP2_ONDIV, "ondiv"},
    {HWCAP2_DICTUNP, "dictunp"},
    {HWCAP2_FPCMPSHL, "fpcmpshl"},
    {HWCAP2_RLE, "rle"},
    {HWCAP2_SHA3, "sha3"},
    {0, NULL}
  };

  for (int i = 0; hwcap_map[i].name; i++)
    if (mask & hwcap_map[i].flag)
      return hwcap_map[i].name;

  mask = mask >> 32;
  for (int i = 0; hwcap2_map[i].name; i++)
    if (mask & hwcap2_map[i].flag)
      return hwcap2_map[i].name;

  return "UNKNOWN";
}

/* Subroutine of md_assemble to do the actual parsing.  */

static int parse_opcode_name(char **s) {
    if (ISLOWER(**s)) {
        do {
            (*s)++;
        } while (ISLOWER(**s) || ISDIGIT(**s) || **s == '_');
    }
    
    switch (**s) {
    case '\0':
        return 0;
    case ',':
        *(*s)++ = '\0';
        return 1;
    default:
        if (is_whitespace(**s)) {
            *(*s)++ = '\0';
            return 0;
        }
        return -1;
    }
}

static int parse_membar_mask(char **s) {
    int kmask = 0;
    
    if (**s == '#') {
        while (**s == '#') {
            int jmask;
            if (!parse_keyword_arg(sparc_encode_membar, s, &jmask))
                return -1;
            kmask |= jmask;
            while (is_whitespace(**s))
                (*s)++;
            if (**s == '|' || **s == '+')
                (*s)++;
            while (is_whitespace(**s))
                (*s)++;
        }
    } else {
        if (!parse_const_expr_arg(s, &kmask))
            return -2;
        if (kmask < 0 || kmask > 127)
            return -3;
    }
    
    return kmask;
}

static int parse_siam_mode(char **s) {
    int smask = 0;
    if (!parse_const_expr_arg(s, &smask))
        return -1;
    if (smask < 0 || smask > 7)
        return -2;
    return smask;
}

static int parse_prefetch_function(char **s) {
    int fcn = 0;
    
    if (**s == '#') {
        if (!parse_keyword_arg(sparc_encode_prefetch, s, &fcn))
            return -1;
    } else {
        if (!parse_const_expr_arg(s, &fcn))
            return -2;
        if (fcn < 0 || fcn > 31)
            return -3;
    }
    
    return fcn;
}

static int parse_privileged_register(char **s, struct priv_reg_entry *table, unsigned int opcode_val, int shift_pos) {
    struct priv_reg_entry *p;
    unsigned int len;
    
    if (**s != '%')
        return 0;
    
    (*s)++;
    for (p = table; p->name; p++) {
        if (p->name[0] == **s) {
            len = strlen(p->name);
            if (strncmp(p->name, *s, len) == 0)
                break;
        }
    }
    
    if (!p->name)
        return 0;
    
    if (((opcode_val >> shift_pos) & 0x1f) != (unsigned)p->regnum)
        return 0;
    
    *s += len;
    return 1;
}

static int parse_crypto_immediate(char **s) {
    long num = 0;
    
    if (is_whitespace(**s))
        (*s)++;
    
    if ((**s == '0' && (*s)[1] == 'x' && ISXDIGIT((*s)[2])) || ISDIGIT(**s)) {
        if (**s == '0' && (*s)[1] == 'x') {
            *s += 2;
            while (ISXDIGIT(**s)) {
                num <<= 4;
                num |= hex_value(**s);
                (*s)++;
            }
        } else {
            while (ISDIGIT(**s)) {
                num = num * 10 + **s - '0';
                (*s)++;
            }
        }
        if (num < 0 || num > 31)
            return -1;
        return num;
    }
    
    return -2;
}

static int parse_asr_register(char **s, char arg_type) {
    long num = 0;
    
    if (!startswith(*s, "%asr"))
        return -1;
    
    *s += 4;
    
    if (!ISDIGIT(**s))
        return -2;
    
    while (ISDIGIT(**s)) {
        num = num * 10 + **s - '0';
        (*s)++;
    }
    
    if (num < 0 || 31 < num)
        return -3;
    
    return (arg_type == 'M') ? RS1(num) : RD(num);
}

static int parse_condition_code(char **s, const char *cc_name, int cc_len) {
    if (is_whitespace(**s))
        (*s)++;
    
    if (startswith(*s, cc_name)) {
        *s += cc_len;
        return 1;
    }
    
    return 0;
}

static int parse_register_mask(char **s, unsigned int *mask_out) {
    unsigned int mask;
    char c;
    
    if (**s != '%')
        return 0;
    
    (*s)++;
    c = *(*s)++;
    
    switch (c) {
    case 'f':
        if (**s == 'p') {
            (*s)++;
            *mask_out = 0x1e;
            return 1;
        }
        return -1;
    case 'g':
        c = *(*s)++;
        if (isoctal(c)) {
            *mask_out = c - '0';
            return 1;
        }
        return -1;
    case 'i':
        c = *(*s)++;
        if (isoctal(c)) {
            *mask_out = c - '0' + 24;
            return 1;
        }
        return -1;
    case 'l':
        c = *(*s)++;
        if (isoctal(c)) {
            *mask_out = c - '0' + 16;
            return 1;
        }
        return -1;
    case 'o':
        c = *(*s)++;
        if (isoctal(c)) {
            *mask_out = c - '0' + 8;
            return 1;
        }
        return -1;
    case 's':
        if (**s == 'p') {
            (*s)++;
            *mask_out = 0xe;
            return 1;
        }
        return -1;
    case 'r':
        if (!ISDIGIT((c = *(*s)++)))
            return -1;
    case '0': case '1': case '2': case '3': case '4':
    case '5': case '6': case '7': case '8': case '9':
        if (ISDIGIT(**s)) {
            c = 10 * (c - '0') + (*(*s)++ - '0');
            if (c >= 32)
                return -1;
        } else {
            c -= '0';
        }
        *mask_out = c;
        return 1;
    default:
        return -1;
    }
}

static int parse_float_register(char **s, char arg_type, unsigned int *mask_out, int *v9_arg_p) {
    char format;
    unsigned int mask;
    
    if (**s != '%')
        return 0;
    
    (*s)++;
    format = **s;
    
    if ((format != 'f' && format != 'd' && format != 'q') || !ISDIGIT(*++(*s)))
        return 0;
    
    for (mask = 0; ISDIGIT(**s); (*s)++)
        mask = 10 * mask + (**s - '0');
    
    if ((arg_type == 'v' || arg_type == 'B' || arg_type == '5' || 
         arg_type == 'H' || arg_type == '\'' || format == 'd') && (mask & 1))
        return -1;
    
    if ((arg_type == 'V' || arg_type == 'R' || arg_type == 'J' || 
         format == 'q') && (mask & 3))
        return -1;
    
    if ((arg_type == ':' || arg_type == ';' || arg_type == '^') && (mask & 7))
        return -1;
    
    if (arg_type == '\'' && mask < 48)
        return -1;
    
    if (mask >= 64)
        return -2;
    
    if (mask >= 32) {
        if (!SPARC_OPCODE_ARCH_V9_P(max_architecture))
            return -3;
        if (arg_type == 'e' || arg_type == 'f' || arg_type == 'g')
            return -4;
        *v9_arg_p = 1;
        mask -= 31;
    }
    
    *mask_out = mask;
    return 1;
}

static int sparc_ip(char *str, const struct sparc_opcode **pinsn) {
    const char *error_message = "";
    char *s;
    const char *args;
    char c;
    const struct sparc_opcode *insn;
    char *argsStart;
    unsigned long opcode;
    unsigned int mask = 0;
    int match = 0;
    int comma = 0;
    int v9_arg_p;
    int special_case = SPECIAL_CASE_NONE;
    const sparc_asi *sasi = NULL;
    
    s = str;
    comma = parse_opcode_name(&s);
    if (comma == -1) {
        as_bad(_("Unknown opcode: `%s'"), str);
        *pinsn = NULL;
        return special_case;
    }
    
    insn = str_hash_find(op_hash, str);
    *pinsn = insn;
    if (insn == NULL) {
        as_bad(_("Unknown opcode: `%s'"), str);
        return special_case;
    }
    if (comma) {
        *--s = ',';
    }
    
    argsStart = s;
    for (;;) {
        opcode = insn->match;
        memset(&the_insn, '\0', sizeof(the_insn));
        the_insn.reloc = BFD_RELOC_NONE;
        v9_arg_p = 0;
        
        for (args = insn->args;; ++args) {
            switch (*args) {
            case 'K': {
                int kmask = parse_membar_mask(&s);
                if (kmask == -1) {
                    error_message = _(": invalid membar mask name");
                    goto error;
                }
                if (kmask == -2) {
                    error_message = _(": invalid membar mask expression");
                    goto error;
                }
                if (kmask == -3) {
                    error_message = _(": invalid membar mask number");
                    goto error;
                }
                opcode |= MEMBAR(kmask);
                continue;
            }
            
            case '3': {
                int smask = parse_siam_mode(&s);
                if (smask == -1) {
                    error_message = _(": invalid siam mode expression");
                    goto error;
                }
                if (smask == -2) {
                    error_message = _(": invalid siam mode number");
                    goto error;
                }
                opcode |= smask;
                continue;
            }
            
            case '*': {
                int fcn = parse_prefetch_function(&s);
                if (fcn == -1) {
                    error_message = _(": invalid prefetch function name");
                    goto error;
                }
                if (fcn == -2) {
                    error_message = _(": invalid prefetch function expression");
                    goto error;
                }
                if (fcn == -3) {
                    error_message = _(": invalid prefetch function number");
                    goto error;
                }
                opcode |= RD(fcn);
                continue;
            }
            
            case '!':
            case '?':
                if (!parse_privileged_register(&s, priv_reg_table, opcode, *args == '?' ? 14 : 25)) {
                    error_message = _(": unrecognizable privileged register");
                    goto error;
                }
                continue;
            
            case '$':
            case '%':
                if (!parse_privileged_register(&s, hpriv_reg_table, opcode, *args == '$' ? 14 : 25)) {
                    error_message = _(": unrecognizable hyperprivileged register");
                    goto error;
                }
                continue;
            
            case '_':
            case '/':
                if (!parse_privileged_register(&s, v9a_asr_table, opcode, *args == '/' ? 14 : 25)) {
                    error_message = _(": unrecognizable ancillary state register");
                    goto error;
                }
                continue;
            
            case 'M':
            case 'm': {
                int result = parse_asr_register(&s, *args);
                if (result == -1) {
                    break;
                }
                if (result == -2) {
                    error_message = _(": expecting %asrN");
                    goto error;
                }
                if (result == -3) {
                    error_message = _(": asr number must be between 0 and 31");
                    goto error;
                }
                opcode |= result;
                continue;
            }
            
            case 'I':
                the_insn.reloc = BFD_RELOC_SPARC_11;
                goto immediate;
            
            case 'j':
                the_insn.reloc = BFD_RELOC_SPARC_10;
                goto immediate;
            
            case ')': {
                int num = parse_crypto_immediate(&s);
                if (num == -1) {
                    error_message = _(": crypto immediate must be between 0 and 31");
                    goto error;
                }
                if (num == -2) {
                    error_message = _(": expecting crypto immediate");
                    goto error;
                }
                opcode |= RS3(num);
                continue;
            }
            
            case 'X':
                if (SPARC_OPCODE_ARCH_V9_P(max_architecture))
                    the_insn.reloc = BFD_RELOC_SPARC_5;
                else
                    the_insn.reloc = BFD_RELOC_SPARC13;
                goto immediate;
            
            case 'Y':
                if (SPARC_OPCODE_ARCH_V9_P(max_architecture))
                    the_insn.reloc = BFD_RELOC_SPARC_6;
                else
                    the_insn.reloc = BFD_RELOC_SPARC13;
                goto immediate;
            
            case 'k':
                the_insn.reloc = BFD_RELOC_SPARC_WDISP16;
                the_insn.pcrel = 1;
                goto immediate;
            
            case '=':
                the_insn.reloc = BFD_RELOC_SPARC_WDISP10;
                the_insn.pcrel = 1;
                goto immediate;
            
            case 'G':
                the_insn.reloc = BFD_RELOC_SPARC_WDISP19;
                the_insn.pcrel = 1;
                goto immediate;
            
            case 'N':
                if (*s == 'p' && s[1] == 'n') {
                    s += 2;
                    continue;
                }
                break;
            
            case 'T':
                if (*s == 'p' && s[1] == 't') {
                    s += 2;
                    continue;
                }
                break;
            
            case 'z':
                if (parse_condition_code(&s, "%icc", 4) ||
                    (sparc_arch_size == 32 && parse_condition_code(&s, "%ncc", 4)))
                    continue;
                break;
            
            case 'Z':
                if (parse_condition_code(&s, "%xcc", 4) ||
                    (sparc_arch_size == 64 && parse_condition_code(&s, "%ncc", 4)))
                    continue;
                break;
            
            case '6':
                if (parse_condition_code(&s, "%fcc0", 5))
                    continue;
                break;
            
            case '7':
                if (parse_condition_code(&s, "%fcc1", 5))
                    continue;
                break;
            
            case '8':
                if (parse_condition_code(&s, "%fcc2", 5))
                    continue;
                break;
            
            case '9':
                if (parse_condition_code(&s, "%fcc3", 5))
                    continue;
                break;
            
            case 'P':
                if (startswith(s, "%pc")) {
                    s += 3;
                    continue;
                }
                break;
            
            case 'W':
                if (startswith(s, "%tick")) {
                    s += 5;
                    continue;
                }
                break;
            
            case '\0': {
                if (s[0] == ',' && s[1] == '%') {
                    char *s1;
                    int npar = 0;
                    const struct perc_entry *p;
                    
                    for (p = perc_table; p->type != perc_entry_none; p++)
                        if ((p->type == perc_entry_post_pop || p->type == perc_entry_reg) &&
                            strncmp(s + 2, p->name, p->len) == 0)
                            break;
                    if (p->type == perc_entry_none || p->type == perc_entry_reg)
                        break;
                    
                    if (s[p->len + 2] != '(') {
                        as_bad(_("Illegal operands: %%%s requires arguments in ()"), p->name);
                        return special_case;
                    }
                    
                    if (!(p->pop->flags & F_POP_TLS_CALL) && the_insn.reloc != BFD_RELOC_NONE) {
                        as_bad(_("Illegal operands: %%%s cannot be used together with other relocs in the insn ()"),
                               p->name);
                        return special_case;
                    }
                    
                    if ((p->pop->flags & F_POP_TLS_CALL) &&
                        (the_insn.reloc != BFD_RELOC_32_PCREL_S2 ||
                         the_insn.exp.X_add_number != 0 ||
                         the_insn.exp.X_add_symbol != symbol_find_or_make("__tls_get_addr"))) {
                        as_bad(_("Illegal operands: %%%s can be only used with call __tls_get_addr"),
                               p->name);
                        return special_case;
                    }
                    
                    the_insn.reloc = p->pop->reloc;
                    memset(&the_insn.exp, 0, sizeof(the_insn.exp));
                    s += p->len + 3;
                    
                    for (s1 = s; *s1 && *s1 != ',' && *s1 != ']'; s1++)
                        if (*s1 == '(')
                            npar++;
                        else if (*s1 == ')') {
                            if (!npar)
                                break;
                            npar--;
                        }
                    
                    if (*s1 != ')') {
                        as_bad(_("Illegal operands: %%%s requires arguments in ()"), p->name);
                        return special_case;
                    }
                    
                    *s1 = '\0';
                    (void)get_expression(s);
                    *s1 = ')';
                    s = s1 + 1;
                }
                if (*s == '\0')
                    match = 1;
                break;
            }
            
            case '+':
                if (*s == '+') {
                    ++s;
                    continue;
                }
                if (*s == '-') {
                    continue;
                }
                break;
            
            case '[':
            case ']':
            case ',':
                if (*s++ == *args)
                    continue;
                break;
            
            case ' ':
                if (is_whitespace(*s++))
                    continue;
                break;
            
            case '#':
                if (ISDIGIT(*s++)) {
                    while (ISDIGIT(*s)) {
                        ++s;
                    }
                    continue;
                }
                break;
            
            case 'C':
                if (startswith(s, "%csr")) {
                    s += 4;
                    continue;
                }
                break;
            
            case 'b':
            case 'c':
            case 'D':
                if (*s++ == '%' && *s++ == 'c' && ISDIGIT(*s)) {
                    mask = *s++;
                    if (ISDIGIT(*s)) {
                        mask = 10 * (mask - '0') + (*s++ - '0');
                        if (mask >= 32) {
                            break;
                        }
                    } else {
                        mask -= '0';
                    }
                    switch (*args) {
                    case 'b':
                        opcode |= mask << 14;
                        continue;
                    case 'c':
                        opcode |= mask;
                        continue;
                    case 'D':
                        opcode |= mask << 25;
                        continue;
                    }
                }
                break;
            
            case 'r':
            case 'O':
            case '1':
            case '2':
            case 'd': {
                int ret = parse_register_mask(&s, &mask);
                if (ret == -1) {
                    goto error;
                }
                if (ret == 0) {
                    break;
                }
                
                if ((mask & ~1) == 2 && sparc_arch_size == 64 &&
                    no_undeclared_regs && !globals[mask])
                    as_bad(_("detected global register use not covered by .register pseudo-op"));
                
                switch (*args) {
                case '1':
                    opcode |= mask << 14;
                    continue;
                case '2':
                    opcode |= mask;
                    continue;
                case 'd':
                    opcode |= mask << 25;
                    continue;
                case 'r':
                    opcode |= (mask << 25) | (mask << 14);
                    continue;
                case 'O':
                    opcode |= (mask << 25) | (mask << 0);
                    continue;
                }
                break;
            }
            
            case 'e':
            case 'v':
            case 'V':
            case ';':
            case 'f':
            case 'B':
            case 'R':
            case ':':
            case '\'':
            case '4':
            case '5':
            case 'g':
            case 'H':
            case 'J':
            case '}':
            case '^': {
                int ret = parse_float_register(&s, *args, &mask, &v9_arg_p);
                if (ret == -1 || ret == -2) {
                    break;
                }
                if (ret == -3) {
                    error_message = _(": There are only 32 f registers; [0-31]");
                    goto error;
                }
                if (ret == -4) {
                    error_message = _(": There are only 32 single precision f registers; [0-31]");
                    goto error;
                }
                if (ret == 0) {
                    break;
                }
                
                if (mask >= 64) {
                    if (SPARC_OPCODE_ARCH_V9_P(max_architecture))
                        error_message = _(": There are only 64 f registers; [0-63]");
                    else
                        error_message = _(": There are only 32 f registers; [0-31]");
                    goto error;
                } else if (mask >= 32) {
                    if (SPARC_OPCODE_ARCH_V9_P(max_architecture)) {
                        if (*args == 'e' || *args == 'f' || *args == 'g') {
                            error_message = _(": There are only 32 single precision f registers; [0-31]");
                            goto error;
                        }
                        v9_arg_p = 1;
                        mask -= 31;
                    } else {
                        error_message = _(": There are only 32 f registers; [0-31]");
                        goto error;
                    }
                }
                
                switch (*args) {
                case 'v':
                case 'V':
                case 'e':
                case ';':
                    opcode |= RS1(mask);
                    continue;
                case 'f':
                case 'B':
                case 'R':
                case ':':
                    opcode |= RS2(mask);
                    continue;
                case '\'':
                    opcode |= RS2(mask & 0xe);
                    continue;
                case '4':
                case '5':
                    opcode |= RS3(mask);
                    continue;
                case 'g':
                case 'H':
                case 'J':
                case '^':
                    opcode |= RD(mask);
                    continue;
                case '}':
                    if (RD(mask) != (opcode & RD(0x1f))) {
                        error_message = _(": Instruction requires frs2 and frsd must be the same register");
                        goto error;
                    }
                    continue;
                }
                
                know(0);
                break;
            }
            
            case 'F':
                if (startswith(s, "%fsr")) {
                    s += 4;
                    continue;
                }
                break;
            
            case '(':
                if (startswith(s, "%efsr")) {
                    s += 5;
                    continue;
                }
                break;
            
            case '0':
                the_insn.reloc = BFD_RELOC_NONE;
                goto immediate;
            
            case 'l':
                the_insn.reloc = BFD_RELOC_SPARC_WDISP22;
                the_insn.pcrel = 1;
                goto immediate;
            
            case 'L':
                the_insn.reloc = BFD_RELOC_32_PCREL_S2;
                the_insn.pcrel = 1;
                goto immediate;
            
            case 'h':
            case 'n':
                the_insn.reloc = BFD_RELOC_SPARC22;
                goto immediate;
            
            case 'i':
                the_insn.reloc = BFD_RELOC_SPARC13;
                
            immediate:
                if (is_whitespace(*s))
                    s++;
                
                {
                    char *s1;
                    const char *op_arg = NULL;
                    static expressionS op_exp;
                    bfd_reloc_code_real_type old_reloc = the_insn.reloc;
                    
                    if (*s == '%') {
                        const struct perc_entry *p;
                        
                        for (p = perc_table; p->type != perc_entry_none; p++)
                            if ((p->type == perc_entry_imm_pop || p->type == perc_entry_reg) &&
                                strncmp(s + 1, p->name, p->len) == 0)
                                break;
                        if (p->type == perc_entry_none || p->type == perc_entry_reg)
                            break;
                        
                        if (s[p->len + 1] != '(') {
                            as_bad(_("Illegal operands: %%%s requires arguments in ()"), p->name);
                            return special_case;
                        }
                        
                        op_arg = p->name;
                        the_insn.reloc = p->pop->reloc;
                        s += p->len + 2;
                        v9_arg_p = p->pop->flags & F_POP_V9;
                    }
                    
                    if (op_arg) {
                        int npar = 0;
                        
                        for (s1 = s; *s1 && *s1 != ',' && *s1 != ']'; s1++)
                            if (*s1 == '(')
                                npar++;
                            else if (*s1 == ')') {
                                if (!npar)
                                    break;
                                npar--;
                            }
                        
                        if (*s1 != ')') {
                            as_bad(_("Illegal operands: %%%s requires arguments in ()"), op_arg);
                            return special_case;
                        }
                        
                        *s1 = '\0';
                        (void)get_expression(s);
                        *s1 = ')';
                        if (expr_parse_end != s1) {
                            as_bad(_("Expression inside %%%s could not be parsed"), op_arg);
                            return special_case;
                        }
                        s = s1 + 1;
                        if (*s == ',' || *s == ']' || !*s)
                            continue;
                        if (*s != '+' && *s != '-') {
                            as_bad(_("Illegal operands: Can't do arithmetics other than + and - involving %%%s()"), op_arg);
                            return special_case;
                        }
                        *s1 = '0';
                        s = s1;
                        op_exp = the_insn.exp;
                        memset(&the_insn.exp, 0, sizeof(the_insn.exp));
                    }
                    
                    for (s1 = s; *s1 && *s1 != ',' && *s1 != ']'; s1++)
                        ;
                    
                    if (s1 != s && ISDIGIT(s1[-1])) {
                        if (s1[-2] == '%' && s1[-3] == '+')
                            s1 -= 3;
                        else if (strchr("golir0123456789", s1[-2]) && s1[-3] == '%' && s1[-4] == '+')
                            s1 -= 4;
                        else if (s1[-3] == 'r' && s1[-4] == '%' && s1[-5] == '+')
                            s1 -= 5;
                        else
                            s1 = NULL;
                        if (s1) {
                            *

static char *skip_over_keyword(char *q)
{
    const char HASH = '#';
    const char PERCENT = '%';
    const char UNDERSCORE = '_';
    
    if (*q == HASH || *q == PERCENT) {
        ++q;
    }
    
    while (ISALNUM(*q) || *q == UNDERSCORE) {
        ++q;
    }
    
    return q;
}

static int parse_sparc_asi(char **input_pointer_p, const sparc_asi **value_p)
{
    char *keyword_start = *input_pointer_p;
    char *keyword_end = skip_over_keyword(keyword_start);
    char saved_char = *keyword_end;
    
    *keyword_end = 0;
    const sparc_asi *value = sparc_encode_asi(keyword_start);
    *keyword_end = saved_char;
    
    if (value == NULL)
        return 0;
    
    *value_p = value;
    *input_pointer_p = keyword_end;
    return 1;
}

/* Parse an argument that can be expressed as a keyword.
   (eg: #StoreStore or %ccfr).
   The result is a boolean indicating success.
   If successful, INPUT_POINTER is updated.  */

static int
parse_keyword_arg (int (*lookup_fn) (const char *),
		   char **input_pointerP,
		   int *valueP)
{
  char *keyword_start = *input_pointerP;
  char *keyword_end = skip_over_keyword(keyword_start);
  
  char saved_char = *keyword_end;
  *keyword_end = '\0';
  
  int lookup_result = (*lookup_fn) (keyword_start);
  
  *keyword_end = saved_char;
  
  if (lookup_result == -1)
    return 0;
    
  *valueP = lookup_result;
  *input_pointerP = keyword_end;
  return 1;
}

/* Parse an argument that is a constant expression.
   The result is a boolean indicating success.  */

static int is_percent_prefix(const char *input)
{
    return *input == '%';
}

static int is_constant_expression(const expressionS *exp)
{
    return exp->X_op == O_constant;
}

static void save_and_set_input_pointer(char **saved, char *new_value)
{
    *saved = input_line_pointer;
    input_line_pointer = new_value;
}

static void restore_input_pointer(char *saved)
{
    input_line_pointer = saved;
}

static int
parse_const_expr_arg (char **input_pointerP, int *valueP)
{
    char *save;
    expressionS exp;

    save_and_set_input_pointer(&save, *input_pointerP);
    
    if (is_percent_prefix(input_line_pointer))
    {
        restore_input_pointer(save);
        return 0;
    }
    
    expression(&exp);
    *input_pointerP = input_line_pointer;
    restore_input_pointer(save);
    
    if (!is_constant_expression(&exp))
        return 0;
        
    *valueP = exp.X_add_number;
    return 1;
}

/* Subroutine of sparc_ip to parse an expression.  */

static int is_valid_segment(segT seg)
{
    return seg == absolute_section ||
           seg == text_section ||
           seg == data_section ||
           seg == bss_section ||
           seg == undefined_section;
}

static void restore_input_pointer(char *save_in)
{
    expr_parse_end = input_line_pointer;
    input_line_pointer = save_in;
}

static int
get_expression (char *str)
{
    char *save_in;
    segT seg;

    save_in = input_line_pointer;
    input_line_pointer = str;
    seg = expression (&the_insn.exp);
    
    if (!is_valid_segment(seg))
    {
        the_insn.error = _("bad segment");
        restore_input_pointer(save_in);
        return 1;
    }
    
    restore_input_pointer(save_in);
    return 0;
}

/* Subroutine of md_assemble to output one insn.  */

static void write_opcode(char *toP, const struct sparc_it *theinsn)
{
    if (INSN_BIG_ENDIAN)
        number_to_chars_bigendian(toP, theinsn->opcode, 4);
    else
        number_to_chars_littleendian(toP, theinsn->opcode, 4);
}

static void create_fixup(char *toP, const struct sparc_it *theinsn)
{
    const int INSN_SIZE = 4;
    
    fixS *fixP = fix_new_exp(frag_now,
                            (toP - frag_now->fr_literal),
                            INSN_SIZE,
                            &theinsn->exp,
                            theinsn->pcrel,
                            theinsn->reloc);
    
    fixP->fx_no_overflow = 1;
    
    if (theinsn->reloc == BFD_RELOC_SPARC_OLO10)
        fixP->tc_fix_data = theinsn->exp2.X_add_number;
}

static void output_insn(const struct sparc_opcode *insn, struct sparc_it *theinsn)
{
    const int INSN_SIZE = 4;
    char *toP = frag_more(INSN_SIZE);
    
    write_opcode(toP, theinsn);
    
    if (theinsn->reloc != BFD_RELOC_NONE)
        create_fixup(toP, theinsn);
    
    last_insn = insn;
    last_opcode = theinsn->opcode;
    
    dwarf2_emit_insn(INSN_SIZE);
}

const char *
md_atof (int type, char *litP, int *sizeP)
{
  return ieee_md_atof (type, litP, sizeP, target_big_endian);
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

void
md_number_to_chars (char *buf, valueT val, int n)
{
  if (should_use_big_endian(n))
    number_to_chars_bigendian (buf, val, n);
  else
    number_to_chars_littleendian (buf, val, n);
}

static int
should_use_big_endian(int n)
{
  if (target_big_endian)
    return 1;
    
  if (is_debug_word(n))
    return 1;
    
  return 0;
}

static int
is_debug_word(int n)
{
  #define WORD_SIZE 4
  #define HALF_WORD_SIZE 2
  
  if (!target_little_endian_data)
    return 0;
    
  if (n != WORD_SIZE && n != HALF_WORD_SIZE)
    return 0;
    
  if (~now_seg->flags & SEC_ALLOC)
    return 1;
    
  return 0;
}

/* Apply a fixS to the frags, now that we know the value it ought to
   hold.  */

#define G0		0
#define O7		15
#define XCC		(2 << 20)
#define COND(x)		(((x)&0xf)<<25)
#define CONDA		COND(0x8)
#define INSN_BPA	(F2(0,1) | CONDA | BPRED | XCC)
#define INSN_BA		(F2(0,2) | CONDA)
#define INSN_OR		F3(2, 0x2, 0)
#define INSN_NOP	F2(0,4)
#define WDISP10_OFFSET_MAX 0x007fc
#define WDISP10_OFFSET_MIN 0x808
#define WDISP16_OFFSET_MAX 0x1fffc
#define WDISP16_OFFSET_MIN 0x20008
#define WDISP19_OFFSET_MAX 0xffffc
#define WDISP19_OFFSET_MIN 0x100008
#define SPARC22_MASK 0x003fffff
#define SPARC_SIGNED_RANGE_0x7FF 0x7ff
#define SPARC_SIGNED_RANGE_0x3FF 0x3ff
#define SPARC_BITFIELD_0x7F 0x7f
#define SPARC_BITFIELD_0x3F 0x3f
#define SPARC_BITFIELD_0x1F 0x1f
#define SPARC13_SIGNED_RANGE 0x1fff
#define INSN_MASK_0x3FE00000 0x3fe00000
#define INSN_MASK_0x3C0000 0x3c0000
#define INSN_MASK_0x3FFFFF 0x3fffff
#define INSN_MASK_0x7FFFF 0x7ffff
#define SHIFT_10 10
#define SHIFT_12 12
#define SHIFT_22 22
#define SHIFT_32 32

static int is_tls_relocation(int reloc_type)
{
    switch (reloc_type) {
    case BFD_RELOC_SPARC_TLS_GD_HI22:
    case BFD_RELOC_SPARC_TLS_GD_LO10:
    case BFD_RELOC_SPARC_TLS_GD_ADD:
    case BFD_RELOC_SPARC_TLS_GD_CALL:
    case BFD_RELOC_SPARC_TLS_LDM_HI22:
    case BFD_RELOC_SPARC_TLS_LDM_LO10:
    case BFD_RELOC_SPARC_TLS_LDM_ADD:
    case BFD_RELOC_SPARC_TLS_LDM_CALL:
    case BFD_RELOC_SPARC_TLS_LDO_HIX22:
    case BFD_RELOC_SPARC_TLS_LDO_LOX10:
    case BFD_RELOC_SPARC_TLS_LDO_ADD:
    case BFD_RELOC_SPARC_TLS_IE_HI22:
    case BFD_RELOC_SPARC_TLS_IE_LO10:
    case BFD_RELOC_SPARC_TLS_IE_LD:
    case BFD_RELOC_SPARC_TLS_IE_LDX:
    case BFD_RELOC_SPARC_TLS_IE_ADD:
    case BFD_RELOC_SPARC_TLS_LE_HIX22:
    case BFD_RELOC_SPARC_TLS_LE_LOX10:
    case BFD_RELOC_SPARC_TLS_DTPMOD32:
    case BFD_RELOC_SPARC_TLS_DTPMOD64:
    case BFD_RELOC_SPARC_TLS_DTPOFF32:
    case BFD_RELOC_SPARC_TLS_DTPOFF64:
    case BFD_RELOC_SPARC_TLS_TPOFF32:
    case BFD_RELOC_SPARC_TLS_TPOFF64:
        return 1;
    }
    return 0;
}

static void handle_data_relocation(char *buf, int reloc_type, offsetT val)
{
    switch (reloc_type) {
    case BFD_RELOC_8:
        md_number_to_chars(buf, val, 1);
        break;
    case BFD_RELOC_16:
    case BFD_RELOC_SPARC_UA16:
        md_number_to_chars(buf, val, 2);
        break;
    case BFD_RELOC_32:
    case BFD_RELOC_SPARC_UA32:
    case BFD_RELOC_SPARC_REV32:
        md_number_to_chars(buf, val, 4);
        break;
    case BFD_RELOC_64:
    case BFD_RELOC_SPARC_UA64:
        md_number_to_chars(buf, val, 8);
        break;
    }
}

static int is_data_relocation(int reloc_type)
{
    return reloc_type == BFD_RELOC_8 ||
           reloc_type == BFD_RELOC_16 ||
           reloc_type == BFD_RELOC_SPARC_UA16 ||
           reloc_type == BFD_RELOC_32 ||
           reloc_type == BFD_RELOC_SPARC_UA32 ||
           reloc_type == BFD_RELOC_SPARC_REV32 ||
           reloc_type == BFD_RELOC_64 ||
           reloc_type == BFD_RELOC_SPARC_UA64;
}

static long read_insn(char *buf)
{
    if (INSN_BIG_ENDIAN)
        return bfd_getb32(buf);
    else
        return bfd_getl32(buf);
}

static void write_insn(char *buf, long insn)
{
    if (INSN_BIG_ENDIAN)
        bfd_putb32(insn, buf);
    else
        bfd_putl32(insn, buf);
}

static int check_delay_slot_conditions(long delay)
{
    if ((delay & OP(~0)) != OP(2))
        return 0;
    if ((delay & OP3(~0)) != OP3(0x3d) && 
        ((delay & OP3(0x28)) != 0 || ((delay & RD(~0)) != RD(O7))))
        return 0;
    if ((delay & RS1(~0)) == RS1(O7) ||
        ((delay & F3I(~0)) == 0 && (delay & RS2(~0)) == RS2(O7)))
        return 0;
    return 1;
}

static int can_optimize_branch(offsetT val)
{
    if ((val & INSN_MASK_0x3FE00000) && 
        (val & INSN_MASK_0x3FE00000) != INSN_MASK_0x3FE00000)
        return 0;
    return 1;
}

static long optimize_to_branch(offsetT val)
{
    if (((val & INSN_MASK_0x3C0000) == 0 || 
         (val & INSN_MASK_0x3C0000) == INSN_MASK_0x3C0000) &&
        (sparc_arch_size == 64 || 
         current_architecture >= SPARC_OPCODE_ARCH_V9))
        return INSN_BPA | (val & INSN_MASK_0x7FFFF);
    else
        return INSN_BA | (val & INSN_MASK_0x3FFFFF);
}

static void handle_nop_optimization(fixS *fixP, char *buf, long delay, long insn)
{
    long setter;
    int reg;
    
    if (fixP->fx_where < 4)
        return;
    if ((delay & (0xffffffff ^ RS1(~0))) != (INSN_OR | RD(O7) | RS2(G0)))
        return;
        
    setter = read_insn(buf - 4);
    if ((setter & (0xffffffff ^ RD(~0))) != (INSN_OR | RS1(O7) | RS2(G0)))
        return;
        
    reg = (delay & RS1(~0)) >> 14;
    if (reg != ((setter & RD(~0)) >> 25) || reg == G0 || reg == O7)
        return;
        
    write_insn(buf + 4, INSN_NOP);
}

static long handle_call_optimization(fixS *fixP, char *buf, long insn, offsetT val)
{
    long delay;
    
    if (!sparc_relax || fixP->fx_addsy != NULL || 
        fixP->fx_where + 8 > fixP->fx_frag->fr_fix)
        return insn;
        
    if ((insn & OP(~0)) != OP(1))
        return insn;
        
    delay = read_insn(buf + 4);
    if (!check_delay_slot_conditions(delay))
        return insn;
        
    if (!can_optimize_branch(val))
        return insn;
        
    insn = optimize_to_branch(val);
    handle_nop_optimization(fixP, buf, delay, insn);
    
    return insn;
}

static void check_relocation_overflow(fixS *fixP, offsetT val, offsetT limit)
{
    if (!in_signed_range(val, limit))
        as_bad_where(fixP->fx_file, fixP->fx_line, _("relocation overflow"));
}

static void check_bitfield_overflow(fixS *fixP, offsetT val, offsetT limit)
{
    if (!in_bitfield_range(val, limit))
        as_bad_where(fixP->fx_file, fixP->fx_line, _("relocation overflow"));
}

static long handle_wdisp10_relocation(fixS *fixP, long insn, offsetT val)
{
    if ((val & 3) || val >= WDISP10_OFFSET_MAX || val <= -(offsetT)WDISP10_OFFSET_MIN)
        as_bad_where(fixP->fx_file, fixP->fx_line, _("relocation overflow"));
    val = (val >> 2) + 1;
    return insn | ((val & 0x300) << 11) | ((val & 0xff) << 5);
}

static long handle_wdisp16_relocation(fixS *fixP, long insn, offsetT val)
{
    if ((val & 3) || val >= WDISP16_OFFSET_MAX || val <= -(offsetT)WDISP16_OFFSET_MIN)
        as_bad_where(fixP->fx_file, fixP->fx_line, _("relocation overflow"));
    val = (val >> 2) + 1;
    return insn | ((val & 0xc000) << 6) | (val & 0x3fff);
}

static long handle_wdisp19_relocation(fixS *fixP, long insn, offsetT val)
{
    if ((val & 3) || val >= WDISP19_OFFSET_MAX || val <= -(offsetT)WDISP19_OFFSET_MIN)
        as_bad_where(fixP->fx_file, fixP->fx_line, _("relocation overflow"));
    val = (val >> 2) + 1;
    return insn | (val & INSN_MASK_0x7FFFF);
}

static long handle_instruction_relocation(fixS *fixP, char *buf, long insn, offsetT val)
{
    switch (fixP->fx_r_type) {
    case BFD_RELOC_32_PCREL_S2:
        val = val >> 2;
        if (!sparc_pic_code || fixP->fx_addsy == NULL || symbol_section_p(fixP->fx_addsy))
            ++val;
        insn |= val & 0x3fffffff;
        insn = handle_call_optimization(fixP, buf, insn, val);
        break;

    case BFD_RELOC_SPARC_11:
        check_relocation_overflow(fixP, val, SPARC_SIGNED_RANGE_0x7FF);
        insn |= val & SPARC_SIGNED_RANGE_0x7FF;
        break;

    case BFD_RELOC_SPARC_10:
        check_relocation_overflow(fixP, val, SPARC_SIGNED_RANGE_0x3FF);
        insn |= val & SPARC_SIGNED_RANGE_0x3FF;
        break;

    case BFD_RELOC_SPARC_7:
        check_bitfield_overflow(fixP, val, SPARC_BITFIELD_0x7F);
        insn |= val & SPARC_BITFIELD_0x7F;
        break;

    case BFD_RELOC_SPARC_6:
        check_bitfield_overflow(fixP, val, SPARC_BITFIELD_0x3F);
        insn |= val & SPARC_BITFIELD_0x3F;
        break;

    case BFD_RELOC_SPARC_5:
        check_bitfield_overflow(fixP, val, SPARC_BITFIELD_0x1F);
        insn |= val & SPARC_BITFIELD_0x1F;
        break;

    case BFD_RELOC_SPARC_WDISP10:
        insn = handle_wdisp10_relocation(fixP, insn, val);
        break;

    case BFD_RELOC_SPARC_WDISP16:
        insn = handle_wdisp16_relocation(fixP, insn, val);
        break;

    case BFD_RELOC_SPARC_WDISP19:
        insn = handle_wdisp19_relocation(fixP, insn, val);
        break;

    case BFD_RELOC_SPARC_HH22:
        val = BSR(val, SHIFT_32);
    case BFD_RELOC_SPARC_LM22:
    case BFD_RELOC_HI22:
        if (!fixP->fx_addsy)
            insn |= (val >> SHIFT_10) & SPARC22_MASK;
        else
            insn &= ~0xffff;
        break;

    case BFD_RELOC_SPARC22:
        if (val & ~SPARC22_MASK)
            as_bad_where(fixP->fx_file, fixP->fx_line, _("relocation overflow"));
        insn |= (val & SPARC22_MASK);
        break;

    case BFD_RELOC_SPARC_HM10:
        val = BSR(val, SHIFT_32);
    case BFD_RELOC_LO10:
        if (!fixP->fx_addsy)
            insn |= val & 0x3ff;
        else
            insn &= ~0xff;
        break;

    case BFD_RELOC_SPARC_OLO10:
        val &= 0x3ff;
        val += fixP->tc_fix_data;
    case BFD_RELOC_SPARC13:
        check_relocation_overflow(fixP, val, SPARC13_SIGNED_RANGE);
        insn |= val & SPARC13_SIGNED_RANGE;
        break;

    case BFD_RELOC_SPARC_WDISP22:
        val = (val >> 2) + 1;
    case BFD_RELOC_SPARC_BASE22:
        insn |= val & SPARC22_MASK;
        break;

    case BFD_RELOC_SPARC_H34:
        if (!fixP->fx_addsy) {
            bfd_vma tval = val;
            tval >>= SHIFT_12;
            insn |= tval & SPARC22_MASK;
        }
        break;

    case BFD_RELOC_SPARC_H44:
        if (!fixP->fx_addsy) {
            bfd_vma tval = val;
            tval >>= SHIFT_22;
            insn |= tval & SPARC22_MASK;
        }
        break;

    case BFD_RELOC_SPARC_M44:
        if (!fixP->fx_addsy)
            insn |= (val >> SHIFT_12) & 0x3ff;
        break;

    case BFD_RELOC_SPARC_L44:
        if (!fixP->fx_addsy)
            insn |= val & 0xfff;
        break;

    case BFD_RELOC_SPARC_HIX22:
        if (!fixP->fx_addsy) {
            val ^= ~(offsetT)0;
            insn |= (val >> SHIFT_10) & SPARC22_MASK;
        }
        break;

    case BFD_RELOC_SPARC_LOX10:
        if (!fixP->fx_addsy)
            insn |= 0x1c00 | (val & 0x3ff);
        break;

    case BFD_RELOC_NONE:
        break;

    default:
        as_bad_where(fixP->fx_file, fixP->fx_line,
                    _("bad or unhandled relocation type: 0x%02x"),
                    fixP->fx_r_type);
        break;
    }
    
    return insn;
}

void md_apply_fix(fixS *fixP, valueT *valP, segT segment ATTRIBUTE_UNUSED)
{
    char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
    offsetT val = *valP;
    long insn;

    gas_assert(fixP->fx_r_type < BFD_RELOC_UNUSED);
    fixP->fx_addnumber = val;

    if (fixP->fx_addsy != NULL) {
        if (is_tls_relocation(fixP->fx_r_type))
            S_SET_THREAD_LOCAL(fixP->fx_addsy);
        return;
    }

    if (fixP->fx_r_type == BFD_RELOC_32_PCREL_S2 && fixP->fx_addsy)
        val += fixP->fx_where + fixP->fx_frag->fr_address;

    if (is_data_relocation(fixP->fx_r_type)) {
        handle_data_relocation(buf, fixP->fx_r_type, val);
    } else if (fixP->fx_r_type == BFD_RELOC_VTABLE_INHERIT ||
               fixP->fx_r_type == BFD_RELOC_VTABLE_ENTRY) {
        fixP->fx_done = 0;
        return;
    } else {
        insn = read_insn(buf);
        insn = handle_instruction_relocation(fixP, buf, insn, val);
        write_insn(buf, insn);
    }

    if (fixP->fx_addsy == 0 && !fixP->fx_pcrel)
        fixP->fx_done = 1;
}

/* Translate internal representation of relocation info to BFD target
   format.  */

static arelent *allocate_reloc(void)
{
    arelent *reloc = notes_alloc(sizeof(arelent));
    reloc->sym_ptr_ptr = notes_alloc(sizeof(asymbol *));
    return reloc;
}

static bfd_reloc_code_real_type get_pcrel_code(fixS *fixp)
{
    switch (fixp->fx_size)
    {
    case 1: return BFD_RELOC_8_PCREL;
    case 2: return BFD_RELOC_16_PCREL;
    case 4: return BFD_RELOC_32_PCREL;
#ifdef BFD64
    case 8: return BFD_RELOC_64_PCREL;
#endif
    default:
        as_bad_where(fixp->fx_file, fixp->fx_line,
                    _("can not do %d byte pc-relative relocation"),
                    fixp->fx_size);
        fixp->fx_pcrel = 0;
        return fixp->fx_r_type;
    }
}

static bfd_reloc_code_real_type handle_basic_relocs(fixS *fixp)
{
    if (!fixp->fx_pcrel)
        return fixp->fx_r_type;
    
    bfd_reloc_code_real_type code = get_pcrel_code(fixp);
    if (fixp->fx_pcrel)
        fixp->fx_addnumber = fixp->fx_offset;
    return code;
}

static int is_got_symbol(const char *name)
{
    return strcmp(name, "_GLOBAL_OFFSET_TABLE_") == 0;
}

#ifdef TE_VXWORKS
static int is_gott_symbol(const char *name)
{
    return strcmp(name, "__GOTT_BASE__") == 0 || 
           strcmp(name, "__GOTT_INDEX__") == 0;
}
#endif

static bfd_reloc_code_real_type adjust_pic_reloc(bfd_reloc_code_real_type code, fixS *fixp)
{
    if (!sparc_pic_code)
        return code;

    switch (code)
    {
    case BFD_RELOC_32_PCREL_S2:
        if (generic_force_reloc(fixp))
            return BFD_RELOC_SPARC_WPLT30;
        break;
    case BFD_RELOC_HI22:
        code = BFD_RELOC_SPARC_GOT22;
        if (fixp->fx_addsy != NULL)
        {
            const char *sym_name = S_GET_NAME(fixp->fx_addsy);
            if (is_got_symbol(sym_name))
                return BFD_RELOC_SPARC_PC22;
#ifdef TE_VXWORKS
            if (is_gott_symbol(sym_name))
                return BFD_RELOC_HI22;
#endif
        }
        break;
    case BFD_RELOC_LO10:
        code = BFD_RELOC_SPARC_GOT10;
        if (fixp->fx_addsy != NULL)
        {
            const char *sym_name = S_GET_NAME(fixp->fx_addsy);
            if (is_got_symbol(sym_name))
                return BFD_RELOC_SPARC_PC10;
#ifdef TE_VXWORKS
            if (is_gott_symbol(sym_name))
                return BFD_RELOC_LO10;
#endif
        }
        break;
    case BFD_RELOC_SPARC13:
        return BFD_RELOC_SPARC_GOT13;
    default:
        break;
    }
    return code;
}

static bfd_reloc_code_real_type adjust_debug_section_reloc(bfd_reloc_code_real_type code, asection *section)
{
    if (!(bfd_section_flags(section) & SEC_DEBUGGING))
        return code;

    switch (code)
    {
    case BFD_RELOC_16: return BFD_RELOC_SPARC_UA16;
    case BFD_RELOC_32: return BFD_RELOC_SPARC_UA32;
    case BFD_RELOC_64: return BFD_RELOC_SPARC_UA64;
    default: return code;
    }
}

static int is_sparc_specific_reloc(bfd_reloc_code_real_type code)
{
    return (code >= BFD_RELOC_HI22 && code <= BFD_RELOC_SPARC_GOTDATA_OP) ||
           (code == BFD_RELOC_8_PCREL) || (code == BFD_RELOC_16_PCREL) ||
           (code == BFD_RELOC_32_PCREL) || (code == BFD_RELOC_64_PCREL) ||
           (code == BFD_RELOC_VTABLE_ENTRY) || (code == BFD_RELOC_VTABLE_INHERIT);
}

static bfd_reloc_code_real_type determine_reloc_code(fixS *fixp)
{
    switch (fixp->fx_r_type)
    {
    case BFD_RELOC_8:
    case BFD_RELOC_16:
    case BFD_RELOC_32:
    case BFD_RELOC_64:
        return handle_basic_relocs(fixp);
    default:
        if (is_sparc_specific_reloc(fixp->fx_r_type))
            return fixp->fx_r_type;
        abort();
        return fixp->fx_r_type;
    }
}

static int needs_fx_offset_addend(bfd_reloc_code_real_type code)
{
    return code == BFD_RELOC_32_PCREL_S2 ||
           code == BFD_RELOC_SPARC_WDISP22 ||
           code == BFD_RELOC_SPARC_WDISP16 ||
           code == BFD_RELOC_SPARC_WDISP19 ||
           code == BFD_RELOC_SPARC_WDISP10 ||
           code == BFD_RELOC_SPARC_WPLT30 ||
           code == BFD_RELOC_SPARC_TLS_GD_CALL ||
           code == BFD_RELOC_SPARC_TLS_LDM_CALL;
}

static void set_reloc_addend(arelent *reloc, fixS *fixp, bfd_reloc_code_real_type code, asection *section)
{
    if (!needs_fx_offset_addend(code))
        reloc->addend = fixp->fx_addnumber;
    else if (symbol_section_p(fixp->fx_addsy))
        reloc->addend = section->vma + fixp->fx_addnumber + md_pcrel_from(fixp);
    else
        reloc->addend = fixp->fx_offset;
}

static arelent **create_olo10_expansion(arelent **relocs, fixS *fixp)
{
    arelent *reloc = allocate_reloc();
    relocs[1] = reloc;
    relocs[2] = NULL;
    *reloc->sym_ptr_ptr = symbol_get_bfdsym(section_symbol(absolute_section));
    reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;
    reloc->howto = bfd_reloc_type_lookup(stdoutput, BFD_RELOC_SPARC13);
    reloc->addend = fixp->tc_fix_data;
    return relocs;
}

arelent **
tc_gen_reloc(asection *section, fixS *fixp)
{
    static arelent *relocs[3];
    arelent *reloc;
    bfd_reloc_code_real_type code;

    reloc = allocate_reloc();
    relocs[0] = reloc;
    relocs[1] = NULL;
    *reloc->sym_ptr_ptr = symbol_get_bfdsym(fixp->fx_addsy);
    reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;

    code = determine_reloc_code(fixp);
    code = adjust_pic_reloc(code, fixp);
    code = adjust_debug_section_reloc(code, section);

    if (code == BFD_RELOC_SPARC_OLO10)
        reloc->howto = bfd_reloc_type_lookup(stdoutput, BFD_RELOC_LO10);
    else
        reloc->howto = bfd_reloc_type_lookup(stdoutput, code);

    if (reloc->howto == 0)
    {
        as_bad_where(fixp->fx_file, fixp->fx_line,
                    _("internal error: can't export reloc type %d (`%s')"),
                    fixp->fx_r_type, bfd_get_reloc_code_name(code));
        relocs[0] = NULL;
        return relocs;
    }

    set_reloc_addend(reloc, fixp, code, section);

    if (code == BFD_RELOC_SPARC_OLO10)
        return create_olo10_expansion(relocs, fixp);

    return relocs;
}

/* We have no need to default values of symbols.  */

symbolS *
md_undefined_symbol (char *name ATTRIBUTE_UNUSED)
{
  return 0;
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment ATTRIBUTE_UNUSED, valueT size)
{
  return size;
}

/* Exactly what point is a PC-relative offset relative TO?
   On the sparc, they're relative to the address of the offset, plus
   its size.  This gets us to the following instruction.
   (??? Is this right?  FIXME-SOON)  */
long
md_pcrel_from (fixS *fixP)
{
  long ret = fixP->fx_where + fixP->fx_frag->fr_address;
  
  if (!sparc_pic_code || fixP->fx_addsy == NULL || symbol_section_p (fixP->fx_addsy))
    ret += fixP->fx_size;
    
  return ret;
}

/* Return log2 (VALUE), or -1 if VALUE is not an exact positive power
   of two.  */

static int mylog2(int value) {
    if (value <= 0) {
        return -1;
    }
    
    int shift = 0;
    while ((value & 1) == 0) {
        value >>= 1;
        ++shift;
    }
    
    return (value == 1) ? shift : -1;
}

/* Sort of like s_lcomm.  */

static int parse_symbol_name(char **name, char **p)
{
    char c = get_symbol_name(name);
    *p = input_line_pointer;
    restore_line_pointer(c);
    SKIP_WHITESPACE();
    return c;
}

static int validate_comma_after_name(void)
{
    if (*input_line_pointer != ',')
    {
        as_bad(_("Expected comma after name"));
        ignore_rest_of_line();
        return 0;
    }
    ++input_line_pointer;
    return 1;
}

static int parse_size(void)
{
    int size = get_absolute_expression();
    if (size < 0)
    {
        as_bad(_("BSS length (%d.) <0! Ignored."), size);
        ignore_rest_of_line();
        return -1;
    }
    return size;
}

static int validate_bss_segment(void)
{
    if (!startswith(input_line_pointer, ",\"bss\"") &&
        !startswith(input_line_pointer, ",\".bss\""))
    {
        as_bad(_("bad .reserve segment -- expected BSS segment"));
        return 0;
    }
    
    if (input_line_pointer[2] == '.')
        input_line_pointer += 7;
    else
        input_line_pointer += 6;
    
    SKIP_WHITESPACE();
    return 1;
}

static int parse_alignment(void)
{
    if (*input_line_pointer != ',')
        return 0;
    
    ++input_line_pointer;
    SKIP_WHITESPACE();
    
    if (*input_line_pointer == '\n')
    {
        as_bad(_("missing alignment"));
        ignore_rest_of_line();
        return -1;
    }
    
    int align = (int)get_absolute_expression();
    
    if (align < 0)
    {
        as_bad(_("negative alignment"));
        ignore_rest_of_line();
        return -1;
    }
    
    if (align == 0)
        return 0;
    
    int temp = mylog2(align);
    if (temp < 0)
    {
        as_bad(_("alignment not a power of 2"));
        ignore_rest_of_line();
        return -1;
    }
    
    return temp;
}

static void allocate_bss_symbol(symbolS *symbolP, int size, int align)
{
    if (need_pass_2)
        return;
    
    char *pfrag;
    segT current_seg = now_seg;
    subsegT current_subseg = now_subseg;
    
    subseg_set(bss_section, 1);
    
    if (align)
        frag_align(align, 0, 0);
    
    if (S_GET_SEGMENT(symbolP) == bss_section)
        symbol_get_frag(symbolP)->fr_symbol = NULL;
    
    symbol_set_frag(symbolP, frag_now);
    pfrag = frag_var(rs_org, 1, 1, 0, symbolP, size, NULL);
    *pfrag = 0;
    
    S_SET_SEGMENT(symbolP, bss_section);
    subseg_set(current_seg, current_subseg);
    S_SET_SIZE(symbolP, size);
}

static void s_reserve(int ignore ATTRIBUTE_UNUSED)
{
    char *name;
    char *p;
    char c;
    symbolS *symbolP;
    
    c = parse_symbol_name(&name, &p);
    
    if (!validate_comma_after_name())
        return;
    
    int size = parse_size();
    if (size < 0)
        return;
    
    *p = 0;
    symbolP = symbol_find_or_make(name);
    *p = c;
    
    if (!validate_bss_segment())
        return;
    
    int align = parse_alignment();
    if (align < 0)
        return;
    
    if (align != 0)
        record_alignment(bss_section, align);
    
    if (!S_IS_DEFINED(symbolP))
    {
        allocate_bss_symbol(symbolP, size, align);
    }
    else
    {
        as_warn(_("Ignoring attempt to re-define symbol %s"),
                S_GET_NAME(symbolP));
    }
    
    demand_empty_rest_of_line();
}

static int parse_symbol_name(char **name, char *c_out, char **p_out)
{
    *c_out = get_symbol_name(name);
    *p_out = input_line_pointer;
    restore_line_pointer(*c_out);
    SKIP_WHITESPACE();
    
    if (*input_line_pointer != ',')
    {
        as_bad(_("Expected comma after symbol-name"));
        ignore_rest_of_line();
        return 0;
    }
    input_line_pointer++;
    return 1;
}

static int parse_common_size(offsetT *size)
{
    offsetT temp = get_absolute_expression();
    if (temp < 0)
    {
        as_bad(_(".COMMon length (%lu) out of range ignored"),
               (unsigned long)temp);
        ignore_rest_of_line();
        return 0;
    }
    *size = temp;
    return 1;
}

static int validate_symbol(symbolS *symbolP, offsetT size)
{
    if (S_IS_DEFINED(symbolP) && !S_IS_COMMON(symbolP))
    {
        as_bad(_("Ignoring attempt to re-define symbol"));
        ignore_rest_of_line();
        return 0;
    }
    
    if (S_GET_VALUE(symbolP) != 0 && S_GET_VALUE(symbolP) != (valueT)size)
    {
        as_warn(_("Length of .comm \"%s\" is already %ld. Not changed to %ld."),
                S_GET_NAME(symbolP), (long)S_GET_VALUE(symbolP), (long)size);
    }
    return 1;
}

static int expect_comma_after_length(void)
{
    if (*input_line_pointer != ',')
    {
        as_bad(_("Expected comma after common length"));
        ignore_rest_of_line();
        return 0;
    }
    input_line_pointer++;
    SKIP_WHITESPACE();
    return 1;
}

static int parse_alignment(offsetT *align_out)
{
    offsetT temp = get_absolute_expression();
    if (temp < 0)
    {
        as_bad(_("negative alignment"));
        ignore_rest_of_line();
        return 0;
    }
    *align_out = temp;
    return 1;
}

static int calculate_alignment(offsetT temp)
{
    if (temp == 0)
        return 0;
    
    int align = mylog2(temp);
    if (align < 0)
    {
        as_bad(_("alignment not a power of 2"));
        ignore_rest_of_line();
        return -1;
    }
    return align;
}

static void handle_local_symbol(symbolS *symbolP, offsetT size, offsetT temp)
{
    int align = calculate_alignment(temp);
    if (align < 0)
        return;
    
    segT old_sec = now_seg;
    int old_subsec = now_subseg;
    
    record_alignment(bss_section, align);
    subseg_set(bss_section, 0);
    
    if (align)
        frag_align(align, 0, 0);
    
    if (S_GET_SEGMENT(symbolP) == bss_section)
        symbol_get_frag(symbolP)->fr_symbol = 0;
    
    symbol_set_frag(symbolP, frag_now);
    char *p = frag_var(rs_org, 1, 1, 0, symbolP, size, NULL);
    *p = 0;
    
    S_SET_SEGMENT(symbolP, bss_section);
    S_CLEAR_EXTERNAL(symbolP);
    S_SET_SIZE(symbolP, size);
    
    subseg_set(old_sec, old_subsec);
}

static void allocate_common_symbol(symbolS *symbolP, offsetT size, offsetT align)
{
    S_SET_VALUE(symbolP, size);
    S_SET_ALIGN(symbolP, align);
    S_SET_SIZE(symbolP, size);
    S_SET_EXTERNAL(symbolP);
    S_SET_SEGMENT(symbolP, bfd_com_section_ptr);
}

static int parse_segment_specifier(void)
{
    input_line_pointer++;
    
    if (*input_line_pointer == '.')
        input_line_pointer++;
    
    if (!startswith(input_line_pointer, "bss\"") &&
        !startswith(input_line_pointer, "data\""))
    {
        while (*--input_line_pointer != '"')
            ;
        input_line_pointer--;
        return 0;
    }
    
    while (*input_line_pointer++ != '"')
        ;
    
    return 1;
}

static void report_bad_segment(void)
{
    char *p = input_line_pointer;
    while (*p && *p != '\n')
        p++;
    char c = *p;
    *p = '\0';
    as_bad(_("bad .common segment %s"), input_line_pointer + 1);
    *p = c;
    input_line_pointer = p;
    ignore_rest_of_line();
}

static void s_common(int ignore ATTRIBUTE_UNUSED)
{
    char *name;
    char c;
    char *p;
    offsetT size;
    symbolS *symbolP;
    
    if (!parse_symbol_name(&name, &c, &p))
        return;
    
    if (!parse_common_size(&size))
        return;
    
    *p = 0;
    symbolP = symbol_find_or_make(name);
    *p = c;
    
    if (!validate_symbol(symbolP, size))
        return;
    
    know(symbol_get_frag(symbolP) == &zero_address_frag);
    
    if (!expect_comma_after_length())
        return;
    
    if (*input_line_pointer != '"')
    {
        offsetT temp;
        if (!parse_alignment(&temp))
            return;
        
        if (symbol_get_obj(symbolP)->local)
        {
            handle_local_symbol(symbolP, size, temp);
        }
        else
        {
            allocate_common_symbol(symbolP, size, temp);
        }
    }
    else
    {
        if (parse_segment_specifier())
        {
            allocate_common_symbol(symbolP, size, 0);
        }
        else
        {
            report_bad_segment();
            return;
        }
    }
    
    symbol_get_bfdsym(symbolP)->flags |= BSF_OBJECT;
    demand_empty_rest_of_line();
}

/* Handle the .empty pseudo-op.  This suppresses the warnings about
   invalid delay slot usage.  */

static void s_empty(int ignore ATTRIBUTE_UNUSED)
{
    last_insn = NULL;
}

static void handle_segment(const char *segment_name, int name_length, void (*handler)(void))
{
    input_line_pointer += name_length;
    handler();
}

static void handle_text_segment(void)
{
    s_text(0);
}

static void handle_data_segment(void)
{
    s_data(0);
}

static void handle_bss_segment(void)
{
    subseg_set(data_section, 255);
}

static void
s_seg(int ignore ATTRIBUTE_UNUSED)
{
    if (startswith(input_line_pointer, "\"text\""))
    {
        handle_segment("\"text\"", 6, handle_text_segment);
        return;
    }
    if (startswith(input_line_pointer, "\"data\""))
    {
        handle_segment("\"data\"", 6, handle_data_segment);
        return;
    }
    if (startswith(input_line_pointer, "\"data1\""))
    {
        handle_segment("\"data1\"", 7, s_data1);
        return;
    }
    if (startswith(input_line_pointer, "\"bss\""))
    {
        handle_segment("\"bss\"", 5, handle_bss_segment);
        return;
    }
    as_bad(_("Unknown segment type"));
    demand_empty_rest_of_line();
}

static void
s_data1 (void)
{
  subseg_set (data_section, 1);
  demand_empty_rest_of_line ();
}

static void
s_proc (int ignore ATTRIBUTE_UNUSED)
{
  while (!is_end_of_stmt (*input_line_pointer))
    {
      ++input_line_pointer;
    }
  ++input_line_pointer;
}

/* This static variable is set by s_uacons to tell sparc_cons_align
   that the expression does not need to be aligned.  */

static int sparc_no_align_cons = 0;

/* This handles the unaligned space allocation pseudo-ops, such as
   .uaword.  .uaword is just like .word, but the value does not need
   to be aligned.  */

static void
s_uacons (int bytes)
{
  sparc_no_align_cons = 1;
  cons (bytes);
  sparc_no_align_cons = 0;
}

/* This handles the native word allocation pseudo-op .nword.
   For sparc_arch_size 32 it is equivalent to .word,  for
   sparc_arch_size 64 it is equivalent to .xword.  */

static void
s_ncons (int bytes ATTRIBUTE_UNUSED)
{
  #define SPARC_32_BIT_SIZE 32
  #define BYTES_FOR_32_BIT 4
  #define BYTES_FOR_64_BIT 8
  
  cons (sparc_arch_size == SPARC_32_BIT_SIZE ? BYTES_FOR_32_BIT : BYTES_FOR_64_BIT);
}

/* Handle the SPARC ELF .register pseudo-op.  This sets the binding of a
   global register.
   The syntax is:

   .register %g[2367],{#scratch|symbolname|#ignore}
*/

static int validate_register_syntax(void)
{
  if (input_line_pointer[0] != '%' || 
      input_line_pointer[1] != 'g' ||
      ((input_line_pointer[2] & ~1) != '2' && (input_line_pointer[2] & ~1) != '6') ||
      input_line_pointer[3] != ',')
  {
    as_bad(_("register syntax is .register %%g[2367],{#scratch|symbolname|#ignore}"));
    return -1;
  }
  return input_line_pointer[2] - '0';
}

static char* parse_register_name(char *c_ptr)
{
  char *regname;
  
  if (*input_line_pointer == '#')
  {
    ++input_line_pointer;
    *c_ptr = get_symbol_name(&regname);
    if (strcmp(regname, "scratch") && strcmp(regname, "ignore"))
      as_bad(_("register syntax is .register %%g[2367],{#scratch|symbolname|#ignore}"));
    if (regname[0] == 'i')
      return NULL;
    return (char *)"";
  }
  
  *c_ptr = get_symbol_name(&regname);
  return regname;
}

static int check_register_redefinition(int reg, char *regname)
{
  if (!globals[reg])
    return 0;
    
  if ((regname && globals[reg] != (symbolS *)1 && 
       strcmp(S_GET_NAME(globals[reg]), regname)) ||
      ((regname != NULL) ^ (globals[reg] != (symbolS *)1)))
  {
    as_bad(_("redefinition of global register"));
    return 1;
  }
  return 0;
}

static void set_symbol_flags(symbolS *symbol)
{
  int flags = symbol_get_bfdsym(symbol)->flags;
  flags = flags & ~(BSF_GLOBAL | BSF_LOCAL | BSF_WEAK);
  flags |= BSF_GLOBAL;
  symbol_get_bfdsym(symbol)->flags = flags;
}

static void configure_register_symbol(symbolS *symbol, int reg)
{
  S_SET_VALUE(symbol, reg);
  S_SET_ALIGN(symbol, reg);
  S_SET_SIZE(symbol, 0);
  S_SET_SEGMENT(symbol, absolute_section);
  S_SET_OTHER(symbol, 0);
  
  elf_symbol(symbol_get_bfdsym(symbol))->internal_elf_sym.st_info = 
    ELF_ST_INFO(STB_GLOBAL, STT_REGISTER);
  elf_symbol(symbol_get_bfdsym(symbol))->internal_elf_sym.st_shndx = SHN_UNDEF;
}

static void create_register_symbol(int reg, char *regname)
{
  if (regname == NULL)
  {
    globals[reg] = (symbolS *)1;
    return;
  }
  
  if (*regname && symbol_find(regname))
  {
    as_bad(_("Register symbol %s already defined."), regname);
  }
  
  globals[reg] = symbol_make(regname);
  
  if (!*regname)
  {
    set_symbol_flags(globals[reg]);
  }
  else
  {
    int flags = symbol_get_bfdsym(globals[reg])->flags;
    if (!(flags & (BSF_GLOBAL | BSF_LOCAL | BSF_WEAK)))
      symbol_get_bfdsym(globals[reg])->flags = flags | BSF_GLOBAL;
  }
  
  configure_register_symbol(globals[reg], reg);
}

static void s_register(int ignore ATTRIBUTE_UNUSED)
{
  char c;
  int reg;
  char *regname;
  
  reg = validate_register_syntax();
  if (reg < 0)
    return;
    
  input_line_pointer += 4;
  regname = parse_register_name(&c);
  
  if (sparc_arch_size == 64)
  {
    if (!check_register_redefinition(reg, regname))
    {
      if (!globals[reg])
      {
        create_register_symbol(reg, regname);
      }
    }
  }
  
  (void)restore_line_pointer(c);
  demand_empty_rest_of_line();
}

/* Adjust the symbol table.  We set undefined sections for STT_REGISTER
   symbols which need it.  */

void
sparc_adjust_symtab (void)
{
  symbolS *sym;

  for (sym = symbol_rootP; sym != NULL; sym = symbol_next (sym))
    {
      if (!is_undefined_register_symbol(sym))
        continue;

      S_SET_SEGMENT (sym, undefined_section);
    }
}

static int
is_undefined_register_symbol (symbolS *sym)
{
  struct elf_internal_sym *internal_sym = &elf_symbol(symbol_get_bfdsym(sym))->internal_elf_sym;
  
  if (ELF_ST_TYPE(internal_sym->st_info) != STT_REGISTER)
    return 0;
    
  if (internal_sym->st_shndx != SHN_UNDEF)
    return 0;
    
  return 1;
}

/* If the --enforce-aligned-data option is used, we require .word,
   et. al., to be aligned correctly.  We do it by setting up an
   rs_align_code frag, and checking in HANDLE_ALIGN to make sure that
   no unexpected alignment was introduced.

   The SunOS and Solaris native assemblers enforce aligned data by
   default.  We don't want to do that, because gcc can deliberately
   generate misaligned data if the packed attribute is used.  Instead,
   we permit misaligned data by default, and permit the user to set an
   option to check for it.  */

void
sparc_cons_align (int nbytes)
{
  int nalign;

  if (!enforce_aligned_data || sparc_no_align_cons)
    return;

  nalign = mylog2 (nbytes);
  if (nalign == 0)
    return;

  gas_assert (nalign > 0);

  if (now_seg == absolute_section)
    {
      if ((abs_section_offset & ((1 << nalign) - 1)) != 0)
	as_bad (_("misaligned data"));
      return;
    }

  frag_var (rs_align_test, 1, 1, 0, NULL, nalign, NULL);
  record_alignment (now_seg, nalign);
}

/* This is called from HANDLE_ALIGN in tc-sparc.h.  */

void
sparc_handle_align (fragS *fragp)
{
  int count = fragp->fr_next->fr_address - fragp->fr_address - fragp->fr_fix;

  switch (fragp->fr_type)
    {
    case rs_align_test:
      if (count != 0)
        as_bad_where (fragp->fr_file, fragp->fr_line, _("misaligned data"));
      break;

    case rs_align_code:
      handle_align_code(fragp, count);
      break;

    default:
      break;
    }
}

static void
handle_align_code(fragS *fragp, int count)
{
  char *p = fragp->fr_literal + fragp->fr_fix;
  int fix = 0;

  fix = handle_alignment_padding(&p, &count);
  fix += handle_v9_branch_instruction(p, &count);
  write_nop_instruction(p);

  fragp->fr_fix += fix;
  fragp->fr_var = 4;
}

static int
handle_alignment_padding(char **p, int *count)
{
  int padding = *count & 3;
  if (padding)
    {
      memset(*p, 0, padding);
      *p += padding;
      *count -= padding;
    }
  return padding;
}

static int
handle_v9_branch_instruction(char *p, int *count)
{
  #define V9_BRANCH_THRESHOLD 8
  #define V9_BRANCH_BASE 0x30680000
  #define INSTRUCTION_SIZE 4
  
  if (!SPARC_OPCODE_ARCH_V9_P(max_architecture) || *count <= V9_BRANCH_THRESHOLD)
    return 0;

  unsigned wval = V9_BRANCH_BASE | (*count >> 2);
  write_word_endian(p, wval);
  *count -= INSTRUCTION_SIZE;
  return INSTRUCTION_SIZE;
}

static void
write_nop_instruction(char *p)
{
  #define NOP_INSTRUCTION 0x01000000
  write_word_endian(p, NOP_INSTRUCTION);
}

static void
write_word_endian(char *p, unsigned value)
{
  #define WORD_SIZE 4
  if (INSN_BIG_ENDIAN)
    number_to_chars_bigendian(p, value, WORD_SIZE);
  else
    number_to_chars_littleendian(p, value, WORD_SIZE);
}

/* Some special processing for a Sparc ELF file.  */

void
set_memory_model_flags(void)
{
    switch (sparc_memory_model)
    {
    case MM_RMO:
        elf_elfheader(stdoutput)->e_flags |= EF_SPARCV9_RMO;
        break;
    case MM_PSO:
        elf_elfheader(stdoutput)->e_flags |= EF_SPARCV9_PSO;
        break;
    default:
        break;
    }
}

void
set_32bit_architecture_flags(void)
{
    if (current_architecture >= SPARC_OPCODE_ARCH_V9)
        elf_elfheader(stdoutput)->e_flags |= EF_SPARC_32PLUS;
}

void
set_v9_architecture_flags(void)
{
    if (current_architecture == SPARC_OPCODE_ARCH_V9A)
        elf_elfheader(stdoutput)->e_flags |= EF_SPARC_SUN_US1;
    else if (current_architecture == SPARC_OPCODE_ARCH_V9B)
        elf_elfheader(stdoutput)->e_flags |= EF_SPARC_SUN_US1 | EF_SPARC_SUN_US3;
}

void
sparc_elf_final_processing(void)
{
    const int SPARC_64BIT_SIZE = 64;
    
    if (sparc_arch_size == SPARC_64BIT_SIZE)
    {
        set_memory_model_flags();
    }
    else
    {
        set_32bit_architecture_flags();
    }
    
    set_v9_architecture_flags();
}

const char *
sparc_cons (expressionS *exp, int size)
{
  char *save;
  const char *sparc_cons_special_reloc = NULL;

  SKIP_WHITESPACE ();
  save = input_line_pointer;
  
  if (!is_special_reloc_prefix())
    {
      expression (exp);
      return sparc_cons_special_reloc;
    }

  sparc_cons_special_reloc = parse_reloc_type(size);
  
  if (!sparc_cons_special_reloc)
    {
      expression (exp);
      return sparc_cons_special_reloc;
    }

  if (!validate_size_suffix(size))
    {
      report_size_mismatch_error(sparc_cons_special_reloc, size);
      input_line_pointer = save;
      expression (exp);
      return NULL;
    }

  input_line_pointer += 2;
  
  if (!parse_reloc_arguments(exp, sparc_cons_special_reloc, size))
    {
      input_line_pointer = save;
      expression (exp);
      return NULL;
    }

  return sparc_cons_special_reloc;
}

static int
is_special_reloc_prefix (void)
{
  return input_line_pointer[0] == '%' &&
         input_line_pointer[1] == 'r' &&
         input_line_pointer[2] == '_';
}

static const char *
parse_reloc_type (int size)
{
  if (startswith (input_line_pointer + 3, "disp"))
    {
      input_line_pointer += 7;
      return "disp";
    }
  
  if (startswith (input_line_pointer + 3, "plt"))
    {
      if (!is_valid_data_size(size))
        {
          as_bad (_("Illegal operands: %%r_plt in %d-byte data field"), size);
          return NULL;
        }
      input_line_pointer += 6;
      return "plt";
    }
  
  if (startswith (input_line_pointer + 3, "tls_dtpoff"))
    {
      if (!is_valid_data_size(size))
        {
          as_bad (_("Illegal operands: %%r_tls_dtpoff in %d-byte data field"), size);
          return NULL;
        }
      input_line_pointer += 13;
      return "tls_dtpoff";
    }
  
  return NULL;
}

static int
is_valid_data_size (int size)
{
  return size == 4 || size == 8;
}

static int
validate_size_suffix (int size)
{
  switch (size)
    {
    case 1:
      if (*input_line_pointer != '8')
        return 0;
      input_line_pointer--;
      return 1;
    case 2:
      return input_line_pointer[0] == '1' && input_line_pointer[1] == '6';
    case 4:
      return input_line_pointer[0] == '3' && input_line_pointer[1] == '2';
    case 8:
      return input_line_pointer[0] == '6' && input_line_pointer[1] == '4';
    default:
      return 0;
    }
}

static void
report_size_mismatch_error (const char *reloc_type, int size)
{
  as_bad (_("Illegal operands: Only %%r_%s%d allowed in %d-byte data fields"),
          reloc_type, size * 8, size);
}

static int
parse_reloc_arguments (expressionS *exp, const char *reloc_type, int size)
{
  if (*input_line_pointer != '(')
    {
      as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
              reloc_type, size * 8);
      return 0;
    }
  
  char *end = find_closing_paren(++input_line_pointer);
  
  if (!end)
    {
      as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
              reloc_type, size * 8);
      return 0;
    }
  
  return parse_expression_in_parens(exp, end, reloc_type, size);
}

static char *
find_closing_paren (char *start)
{
  int npar = 0;
  char *end = start;
  int c;
  
  while (!is_end_of_stmt(c = *end))
    {
      if (c == '(')
        npar++;
      else if (c == ')')
        {
          if (!npar)
            return end;
          npar--;
        }
      end++;
    }
  
  return NULL;
}

static int
parse_expression_in_parens (expressionS *exp, char *end, const char *reloc_type, int size)
{
  char saved_char = *end;
  *end = '\0';
  expression (exp);
  *end = saved_char;
  
  if (input_line_pointer != end)
    {
      as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
              reloc_type, size * 8);
      return 0;
    }
  
  input_line_pointer++;
  SKIP_WHITESPACE ();
  
  return validate_trailing_chars(reloc_type, size);
}

static int
validate_trailing_chars (const char *reloc_type, int size)
{
  int c = *input_line_pointer;
  
  if (!is_end_of_stmt(c) && c != ',')
    {
      as_bad (_("Illegal operands: garbage after %%r_%s%d()"),
              reloc_type, size * 8);
      return 0;
    }
  
  return 1;
}

/* This is called by emit_expr via TC_CONS_FIX_NEW when creating a
   reloc for a cons.  We could use the definition there, except that
   we want to handle little endian relocs specially.  */

static bfd_reloc_code_real_type get_base_reloc(unsigned int nbytes)
{
    switch (nbytes) {
        case 1: return BFD_RELOC_8;
        case 2: return BFD_RELOC_16;
        case 4: return BFD_RELOC_32;
        case 8: return BFD_RELOC_64;
        default: return BFD_RELOC_64;
    }
}

static bfd_reloc_code_real_type get_pcrel_reloc(unsigned int nbytes)
{
    switch (nbytes) {
        case 1: return BFD_RELOC_8_PCREL;
        case 2: return BFD_RELOC_16_PCREL;
        case 4: return BFD_RELOC_32_PCREL;
        case 8: return BFD_RELOC_64_PCREL;
        default: abort();
    }
}

static bfd_reloc_code_real_type get_plt_reloc(unsigned int nbytes)
{
    switch (nbytes) {
        case 4: return BFD_RELOC_SPARC_PLT32;
        case 8: return BFD_RELOC_SPARC_PLT64;
        default: return BFD_RELOC_NONE;
    }
}

static bfd_reloc_code_real_type get_tls_dtpoff_reloc(unsigned int nbytes)
{
    switch (nbytes) {
        case 4: return BFD_RELOC_SPARC_TLS_DTPOFF32;
        case 8: return BFD_RELOC_SPARC_TLS_DTPOFF64;
        default: return BFD_RELOC_NONE;
    }
}

static bfd_reloc_code_real_type get_unaligned_reloc(unsigned int nbytes)
{
    switch (nbytes) {
        case 2: return BFD_RELOC_SPARC_UA16;
        case 4: return BFD_RELOC_SPARC_UA32;
#ifdef TE_SOLARIS
        case 8: return sparc_arch_size == 64 ? BFD_RELOC_SPARC_UA64 : BFD_RELOC_SPARC_UA32;
#else
        case 8: return BFD_RELOC_SPARC_UA64;
#endif
        default: abort();
    }
}

static bfd_reloc_code_real_type handle_special_reloc(unsigned int nbytes, char special_char)
{
    if (special_char == 'd')
        return get_pcrel_reloc(nbytes);
    if (special_char == 'p')
        return get_plt_reloc(nbytes);
    return get_tls_dtpoff_reloc(nbytes);
}

static int needs_unaligned_access(void)
{
    return sparc_no_align_cons || strcmp(now_seg->name, ".eh_frame") == 0;
}

static bfd_reloc_code_real_type adjust_for_solaris(bfd_reloc_code_real_type r)
{
#ifdef TE_SOLARIS
    if (!target_little_endian_data && sparc_arch_size != 64 && r == BFD_RELOC_64)
        return BFD_RELOC_32;
#endif
    return r;
}

void cons_fix_new_sparc(fragS *frag,
                        int where,
                        unsigned int nbytes,
                        expressionS *exp,
                        const char *sparc_cons_special_reloc)
{
    bfd_reloc_code_real_type r = get_base_reloc(nbytes);

    if (target_little_endian_data && nbytes == 4 && now_seg->flags & SEC_ALLOC)
        r = BFD_RELOC_SPARC_REV32;

    r = adjust_for_solaris(r);

    if (sparc_cons_special_reloc)
        r = handle_special_reloc(nbytes, *sparc_cons_special_reloc);
    else if (needs_unaligned_access())
        r = get_unaligned_reloc(nbytes);

    fix_new_exp(frag, where, nbytes, exp, 0, r);
}

void
sparc_cfi_frame_initial_instructions (void)
{
  #define SPARC64_CFA_OFFSET 0x7ff
  #define SPARC32_CFA_OFFSET 0
  #define CFA_REGISTER 14
  #define SPARC64_ARCH_SIZE 64
  
  int cfa_offset = (sparc_arch_size == SPARC64_ARCH_SIZE) ? SPARC64_CFA_OFFSET : SPARC32_CFA_OFFSET;
  cfi_add_CFA_def_cfa (CFA_REGISTER, cfa_offset);
}

#define SPARC_REGISTER_GROUP_SIZE 8
#define SPARC_SP_REGISTER 14
#define SPARC_FP_REGISTER 30
#define SPARC_F_REGISTER_OFFSET 32
#define SPARC_MAX_R_REGISTER 32
#define SPARC_MAX_F_REGISTER_V9 64
#define SPARC_MAX_F_REGISTER 32

static int get_register_group_index(char prefix)
{
    switch (prefix)
    {
    case 'g': return 0;
    case 'o': return 1;
    case 'l': return 2;
    case 'i': return 3;
    default: return -1;
    }
}

static int is_valid_register_suffix(const char *suffix)
{
    return suffix[0] >= '0' && suffix[0] <= '8' && !suffix[1];
}

static int parse_grouped_register(const char *regname)
{
    int group_index = get_register_group_index(regname[0]);
    if (group_index == -1)
        return -1;
    
    if (!is_valid_register_suffix(regname + 1))
        return -1;
    
    return group_index * SPARC_REGISTER_GROUP_SIZE + regname[1] - '0';
}

static int parse_special_register(const char *regname)
{
    if (regname[0] == 's' && regname[1] == 'p' && !regname[2])
        return SPARC_SP_REGISTER;
    
    if (regname[0] == 'f' && regname[1] == 'p' && !regname[2])
        return SPARC_FP_REGISTER;
    
    return -1;
}

static int get_max_f_register(void)
{
    return SPARC_OPCODE_ARCH_V9_P(max_architecture) ? SPARC_MAX_F_REGISTER_V9 : SPARC_MAX_F_REGISTER;
}

static int parse_numbered_register(const char *regname)
{
    char *end_ptr;
    unsigned int regnum;
    int max_register;
    
    if (regname[0] != 'f' && regname[0] != 'r')
        return -1;
    
    regnum = strtoul(regname + 1, &end_ptr, 10);
    if (end_ptr == NULL || *end_ptr)
        return -1;
    
    max_register = (regname[0] == 'f') ? get_max_f_register() : SPARC_MAX_R_REGISTER;
    if (regnum >= max_register)
        return -1;
    
    if (regname[0] == 'f')
    {
        regnum += SPARC_F_REGISTER_OFFSET;
        if (regnum >= SPARC_MAX_F_REGISTER_V9 && (regnum & 1))
            return -1;
    }
    
    return regnum;
}

int
sparc_regname_to_dw2regnum(char *regname)
{
    int result;
    
    if (!regname[0])
        return -1;
    
    result = parse_grouped_register(regname);
    if (result != -1)
        return result;
    
    result = parse_special_register(regname);
    if (result != -1)
        return result;
    
    return parse_numbered_register(regname);
}

void
sparc_cfi_emit_pcrel_expr (expressionS *exp, unsigned int nbytes)
{
  sparc_no_align_cons = 1;
  emit_expr_with_reloc (exp, nbytes, "disp");
  sparc_no_align_cons = 0;
}

