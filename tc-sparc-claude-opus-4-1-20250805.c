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
  if (name == NULL)
    return NULL;

  for (struct sparc_arch *sa = &sparc_arch_table[0]; sa->name != NULL; sa++)
    {
      if (strcmp (sa->name, name) == 0)
        return sa;
    }
  
  return NULL;
}

/* Initialize the default opcode arch and word size from the default
   architecture name.  */

static void init_default_arch(void)
{
    struct sparc_arch *sa = lookup_arch(default_arch);

    if (sa == NULL) {
        as_fatal(_("Invalid default architecture, broken assembler."));
        return;
    }

    if (sa->default_arch_size == 0) {
        as_fatal(_("Invalid default architecture, broken assembler."));
        return;
    }

    max_architecture = sparc_opcode_lookup_arch(sa->opcode_arch);
    if (max_architecture == SPARC_OPCODE_ARCH_BAD) {
        as_fatal(_("Bad opcode table, broken assembler."));
        return;
    }

    default_arch_size = sa->default_arch_size;
    sparc_arch_size = sa->default_arch_size;
    default_arch_type = sa->arch_type;
    default_init_p = 1;
}

/* Called by TARGET_MACH.  */

unsigned long
sparc_mach (void)
{
  if (!default_init_p)
    init_default_arch ();

  if (sparc_arch_size == 64)
    return bfd_mach_sparc_v9;
  
  return bfd_mach_sparc;
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

  if (sparc_arch_size == 64)
    return ELF64_TARGET_FORMAT;
  
  return ELF_TARGET_FORMAT;
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
      warn_on_bump = 1;
      warn_after_architecture = SPARC_OPCODE_ARCH_V6;
      return 1;

    case OPTION_XARCH:
      if (!handle_xarch_option(arg))
        return 0;
      return handle_architecture_option(arg, c);

    case 'A':
      return handle_architecture_option(arg, c);

    case OPTION_SPARC:
      return 1;

    case OPTION_ENFORCE_ALIGNED_DATA:
      enforce_aligned_data = 1;
      return 1;

#ifdef SPARC_BIENDIAN
    case OPTION_LITTLE_ENDIAN:
      return handle_little_endian_option();
    
    case OPTION_LITTLE_ENDIAN_DATA:
      return handle_little_endian_data_option();
    
    case OPTION_BIG_ENDIAN:
      target_big_endian = 1;
      return 1;
#endif

    case OPTION_32:
    case OPTION_64:
      return handle_arch_size_option(c);

    case OPTION_TSO:
      sparc_memory_model = MM_TSO;
      return 1;

    case OPTION_PSO:
      sparc_memory_model = MM_PSO;
      return 1;

    case OPTION_RMO:
      sparc_memory_model = MM_RMO;
      return 1;

    case 'V':
      print_version_id ();
      return 1;

    case 'Q':
    case 's':
    case 'q':
      return 1;

    case 'K':
      return handle_k_option(arg);

    case OPTION_NO_UNDECLARED_REGS:
      no_undeclared_regs = 1;
      return 1;

    case OPTION_UNDECLARED_REGS:
      no_undeclared_regs = 0;
      return 1;

    case OPTION_RELAX:
      sparc_relax = 1;
      return 1;

    case OPTION_NO_RELAX:
      sparc_relax = 0;
      return 1;

    case OPTION_DCTI_COUPLES_DETECT:
      dcti_couples_detect = 1;
      return 1;

    default:
      return 0;
    }
}

static int
handle_xarch_option(const char *arg)
{
  if (startswith (arg, "v9"))
    {
      md_parse_option (OPTION_64, NULL);
      return 1;
    }
  
  if (startswith (arg, "v8")
      || startswith (arg, "v7")
      || startswith (arg, "v6")
      || !strcmp (arg, "sparclet")
      || !strcmp (arg, "sparclite")
      || !strcmp (arg, "sparc86x"))
    {
      md_parse_option (OPTION_32, NULL);
    }
  
  return 1;
}

static int
handle_architecture_option(const char *arg, int option)
{
  struct sparc_arch *sa;
  enum sparc_opcode_arch_val opcode_arch;

  sa = lookup_arch (arg);
  if (sa == NULL || !sa->user_option_p)
    {
      if (option == OPTION_XARCH)
        as_bad (_("invalid architecture -xarch=%s"), arg);
      else
        as_bad (_("invalid architecture -A%s"), arg);
      return 0;
    }

  opcode_arch = sparc_opcode_lookup_arch (sa->opcode_arch);
  if (opcode_arch == SPARC_OPCODE_ARCH_BAD)
    {
      as_fatal (_("Bad opcode table, broken assembler."));
      return 0;
    }

  if (!architecture_requested || opcode_arch > max_architecture)
    max_architecture = opcode_arch;

  hwcap_allowed = compute_hwcap_allowed(opcode_arch, sa);
  architecture_requested = 1;
  
  return 1;
}

static uint64_t
compute_hwcap_allowed(enum sparc_opcode_arch_val opcode_arch, 
                      struct sparc_arch *sa)
{
  uint64_t result = hwcap_allowed;
  result |= ((uint64_t) sparc_opcode_archs[opcode_arch].hwcaps2 << 32);
  result |= ((uint64_t) sa->hwcap2_allowed << 32);
  result |= sparc_opcode_archs[opcode_arch].hwcaps;
  result |= sa->hwcap_allowed;
  return result;
}

#ifdef SPARC_BIENDIAN
static int
handle_little_endian_option(void)
{
  target_big_endian = 0;
  if (default_arch_type != sparclet)
    {
      as_fatal ("This target does not support -EL");
      return 0;
    }
  return 1;
}

static int
handle_little_endian_data_option(void)
{
  target_little_endian_data = 1;
  target_big_endian = 0;
  if (default_arch_type != sparc86x && default_arch_type != v9)
    {
      as_fatal ("This target does not support --little-endian-data");
      return 0;
    }
  return 1;
}
#endif

static int
handle_arch_size_option(int option)
{
  const char **list;
  const char **l;
  int found = 0;

  sparc_arch_size = (option == OPTION_32) ? 32 : 64;
  list = bfd_target_list ();
  
  if (list == NULL)
    {
      as_fatal (_("Cannot get target list"));
      return 0;
    }

  for (l = list; *l != NULL; l++)
    {
      if (sparc_arch_size == 32 && startswith (*l, "elf32-sparc"))
        {
          found = 1;
          break;
        }
      if (sparc_arch_size == 64 && startswith (*l, "elf64-sparc"))
        {
          found = 1;
          break;
        }
    }

  if (!found)
    as_fatal (_("No compiled in support for %d bit object file format"),
              sparc_arch_size);
  
  free (list);

  if (sparc_arch_size == 64 && max_architecture < SPARC_OPCODE_ARCH_V9)
    max_architecture = SPARC_OPCODE_ARCH_V9;

  return 1;
}

static int
handle_k_option(const char *arg)
{
  if (strcmp (arg, "PIC") != 0)
    {
      as_warn (_("Unrecognized option following -K"));
      return 1;
    }
  
  sparc_pic_code = 1;
  return 1;
}

void
md_show_usage (FILE *stream)
{
  const struct sparc_arch *arch;
  int column;

  if (!default_init_p)
    init_default_arch();

  fprintf(stream, _("SPARC options:\n"));
  
  column = 0;
  for (arch = &sparc_arch_table[0]; arch->name; arch++)
    {
      if (!arch->user_option_p)
        continue;
      
      if (arch != &sparc_arch_table[0])
        fprintf(stream, " | ");
      
      if (column + strlen(arch->name) > 70)
        {
          column = 0;
          fputc('\n', stream);
        }
      
      column += 5 + 2 + strlen(arch->name);
      fprintf(stream, "-A%s", arch->name);
    }
  
  for (arch = &sparc_arch_table[0]; arch->name; arch++)
    {
      if (!arch->user_option_p)
        continue;
      
      fprintf(stream, " | ");
      
      if (column + strlen(arch->name) > 65)
        {
          column = 0;
          fputc('\n', stream);
        }
      
      column += 5 + 7 + strlen(arch->name);
      fprintf(stream, "-xarch=%s", arch->name);
    }
  
  fprintf(stream, _("\n\
			specify variant of SPARC architecture\n\
-bump			warn when assembler switches architectures\n\
-sparc			ignored\n\
--enforce-aligned-data	force .long, etc., to be aligned correctly\n\
-relax			relax jumps and branches (default)\n\
-no-relax		avoid changing any jumps and branches\n"));
  
  fprintf(stream, _("\
-32			create 32 bit object file\n\
-64			create 64 bit object file\n"));
  
  fprintf(stream, _("\
			[default is %d]\n"), default_arch_size);
  
  fprintf(stream, _("\
-TSO			use Total Store Ordering\n\
-PSO			use Partial Store Ordering\n\
-RMO			use Relaxed Memory Ordering\n"));
  
  const char *memory_ordering = (default_arch_size == 64) ? "RMO" : "TSO";
  fprintf(stream, _("\
			[default is %s]\n"), memory_ordering);
  
  fprintf(stream, _("\
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
  fprintf(stream, _("\
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

  if (p == NULL || q == NULL)
    return 0;

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

void
md_begin (void)
{
  if (!default_init_p)
    init_default_arch ();

  sparc_cie_data_alignment = sparc_arch_size == 64 ? -8 : -4;
  op_hash = str_htab_create ();

  if (!op_hash)
    as_fatal (_("Failed to create opcode hash table"));

  if (!populate_opcode_hash())
    as_fatal (_("Broken assembler.  No assembly attempted."));

  if (!populate_native_opcodes())
    as_fatal (_("Broken assembler.  No assembly attempted."));

  sort_register_tables();
  setup_warning_architecture();
  populate_perc_table();
}

static int
populate_opcode_hash (void)
{
  unsigned int i = 0;

  while (i < (unsigned int) sparc_num_opcodes)
    {
      const char *name = sparc_opcodes[i].name;
      
      if (str_hash_insert (op_hash, name, &sparc_opcodes[i], 0) != NULL)
        {
          as_bad (_("duplicate %s"), name);
          return 0;
        }

      if (!validate_opcode_range(i, name))
        return 0;

      i = skip_duplicate_opcodes(i, name);
    }
  return 1;
}

static int
validate_opcode_range (unsigned int start_idx, const char *name)
{
  unsigned int i = start_idx;
  
  do
    {
      if (sparc_opcodes[i].match & sparc_opcodes[i].lose)
        {
          as_bad (_("Internal error: losing opcode: `%s' \"%s\"\n"),
                  sparc_opcodes[i].name, sparc_opcodes[i].args);
          return 0;
        }
      ++i;
    }
  while (i < (unsigned int) sparc_num_opcodes
         && !strcmp (sparc_opcodes[i].name, name));
  
  return 1;
}

static unsigned int
skip_duplicate_opcodes (unsigned int start_idx, const char *name)
{
  unsigned int i = start_idx;
  
  do
    {
      ++i;
    }
  while (i < (unsigned int) sparc_num_opcodes
         && !strcmp (sparc_opcodes[i].name, name));
  
  return i;
}

static int
populate_native_opcodes (void)
{
  unsigned int i;
  
  for (i = 0; native_op_table[i].name; i++)
    {
      const char *name = (sparc_arch_size == 32)
                        ? native_op_table[i].name32
                        : native_op_table[i].name64;
      
      const struct sparc_opcode *insn = str_hash_find (op_hash, name);
      
      if (insn == NULL)
        {
          as_bad (_("Internal error: can't find opcode `%s' for `%s'\n"),
                  name, native_op_table[i].name);
          return 0;
        }
      
      if (str_hash_insert (op_hash, native_op_table[i].name, insn, 0))
        {
          as_bad (_("duplicate %s"), native_op_table[i].name);
          return 0;
        }
    }
  return 1;
}

static void
sort_register_tables (void)
{
  qsort (priv_reg_table, 
         sizeof (priv_reg_table) / sizeof (priv_reg_table[0]),
         sizeof (priv_reg_table[0]), 
         cmp_reg_entry);
  
  qsort (hpriv_reg_table, 
         sizeof (hpriv_reg_table) / sizeof (hpriv_reg_table[0]),
         sizeof (hpriv_reg_table[0]), 
         cmp_reg_entry);
  
  qsort (v9a_asr_table, 
         sizeof (v9a_asr_table) / sizeof (v9a_asr_table[0]),
         sizeof (v9a_asr_table[0]), 
         cmp_reg_entry);
}

static void
setup_warning_architecture (void)
{
  if (warn_on_bump && architecture_requested)
    {
      warn_after_architecture = max_architecture;
    }

  if (warn_on_bump || !architecture_requested)
    {
      enum sparc_opcode_arch_val current_max = max_architecture;
      
      for (max_architecture = SPARC_OPCODE_ARCH_MAX;
           max_architecture > warn_after_architecture;
           --max_architecture)
        {
          if (!SPARC_OPCODE_CONFLICT_P (max_architecture, current_max))
            break;
        }
    }
}

static void
populate_perc_table (void)
{
  struct priv_reg_entry *reg_tables[] = 
    {priv_reg_table, hpriv_reg_table, v9a_asr_table, NULL};
  int entry = 0;

  entry = add_register_entries(reg_tables, entry);
  entry = add_pop_entries(entry);
  
  perc_table[entry].type = perc_entry_none;
  
  qsort (perc_table, 
         sizeof (perc_table) / sizeof (perc_table[0]),
         sizeof (perc_table[0]), 
         cmp_perc_entry);
}

static int
add_register_entries (struct priv_reg_entry **reg_tables, int entry)
{
  struct priv_reg_entry **reg_table;
  
  for (reg_table = reg_tables; *reg_table; reg_table++)
    {
      struct priv_reg_entry *reg;
      
      for (reg = *reg_table; reg->name; reg++)
        {
          struct perc_entry *p = &perc_table[entry++];
          p->type = perc_entry_reg;
          p->name = reg->name;
          p->len = strlen (reg->name);
          p->reg = reg;
        }
    }
  return entry;
}

static int
add_pop_entries (int entry)
{
  unsigned int i;
  
  for (i = 0; i < ARRAY_SIZE (pop_table); i++)
    {
      struct perc_entry *p = &perc_table[entry++];
      p->type = (pop_table[i].flags & F_POP_POSTFIX)
               ? perc_entry_post_pop 
               : perc_entry_imm_pop;
      p->name = pop_table[i].name;
      p->len = strlen (pop_table[i].name);
      p->pop = &pop_table[i];
    }
  return entry;
}

/* Called after all assembly has been done.  */

void
sparc_md_finish (void)
{
  unsigned long mach = determine_mach_value();
  bfd_set_arch_mach (stdoutput, bfd_arch_sparc, mach);

#ifndef TE_SOLARIS
  add_hardware_capabilities();
#endif
}

static unsigned long
determine_mach_value (void)
{
  if (sparc_arch_size == 64)
    return get_64bit_mach();
  return get_32bit_mach();
}

static unsigned long
get_64bit_mach (void)
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
get_32bit_mach (void)
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
static void
add_hardware_capabilities (void)
{
  int hwcaps = hwcap_seen & 0xffffffff;
  int hwcaps2 = hwcap_seen >> 32;

  if (hwcaps && !add_hwcaps_attribute(hwcaps, Tag_GNU_Sparc_HWCAPS))
    report_attribute_error();
  
  if (hwcaps2 && !add_hwcaps_attribute(hwcaps2, Tag_GNU_Sparc_HWCAPS2))
    report_attribute_error();
}

static int
add_hwcaps_attribute (int caps, int tag)
{
  return bfd_elf_add_obj_attr_int (stdoutput, OBJ_ATTR_GNU, tag, caps);
}

static void
report_attribute_error (void)
{
  as_fatal (_("error adding attribute: %s"), bfd_errmsg (bfd_get_error ()));
}
#endif

/* Return non-zero if VAL is in the range -(MAX+1) to MAX.  */

static inline int
in_signed_range (bfd_signed_vma val, bfd_signed_vma max)
{
  if (max <= 0)
    return 0;
    
  if (sparc_arch_size == 32)
    {
      const bfd_vma sign_bit = (bfd_vma) 1 << 31;
      const bfd_vma mask_32bit = 0xffffffffUL;
      val = ((val & mask_32bit) ^ sign_bit) - sign_bit;
    }
    
  bfd_signed_vma min = ~max;
  return (val >= min && val <= max) ? 1 : 0;
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
    return 0;
  
  bfd_signed_vma min = ~(max >> 1);
  return (val <= max && val >= min) ? 1 : 0;
}

static int sparc_ffs(unsigned int mask)
{
    if (mask == 0) {
        return -1;
    }
    
    int position = 0;
    while ((mask & 1) == 0) {
        mask >>= 1;
        position++;
    }
    
    return position;
}

/* Implement big shift right.  */
static bfd_vma
BSR (bfd_vma val, int amount)
{
  if (amount < 0)
    return val;
  
  if (sizeof (bfd_vma) <= 4 && amount >= 32)
    as_fatal (_("Support for 64-bit arithmetic not compiled in."));
  
  if (amount >= (int)(sizeof(bfd_vma) * 8))
    return 0;
  
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

static void
synthetize_setuw (const struct sparc_opcode *insn)
{
  int need_hi22_p = 0;
  int rd = (the_insn.opcode & RD (~0)) >> 25;
  int is_constant = (the_insn.exp.X_op == O_constant);
  offsetT value = the_insn.exp.X_add_number;

  if (is_constant)
    {
      if (SPARC_OPCODE_ARCH_V9_P (max_architecture))
	{
	  if (sizeof (offsetT) > 4 && (value < 0 || value > (offsetT) U0xffffffff))
	    as_warn (_("set: number not in 0..4294967295 range"));
	}
      else
	{
	  if (sizeof (offsetT) > 4 && 
	      (value < -(offsetT) U0x80000000 || value > (offsetT) U0xffffffff))
	    as_warn (_("set: number not in -2147483648..4294967295 range"));
	  the_insn.exp.X_add_number = (int32_t) value;
	  value = the_insn.exp.X_add_number;
	}
    }

  if (!is_constant || value >= (1 << 12) || value < -(1 << 12))
    {
      unsigned int hi_bits = is_constant ? ((value >> 10) & 0x3fffff) : 0;
      the_insn.opcode = SETHI_INSN | RD (rd) | hi_bits;
      the_insn.reloc = is_constant ? BFD_RELOC_NONE : BFD_RELOC_HI22;
      output_insn (insn, &the_insn);
      need_hi22_p = 1;
    }

  int has_low_bits = !is_constant || (value & 0x3FF) != 0;
  if (!is_constant || (need_hi22_p && has_low_bits) || !need_hi22_p)
    {
      unsigned int lo_bits = 0;
      if (is_constant)
        lo_bits = value & (need_hi22_p ? 0x3ff : 0x1fff);
      
      the_insn.opcode = OR_INSN | RD (rd) | IMMED | lo_bits;
      if (need_hi22_p)
        the_insn.opcode |= RS1 (rd);
      
      the_insn.reloc = is_constant ? BFD_RELOC_NONE : BFD_RELOC_LO10;
      output_insn (insn, &the_insn);
    }
}

/* Handle the setsw synthetic instruction.  */

static void
synthetize_setsw (const struct sparc_opcode *insn)
{
  int low32, rd, opc;

  rd = (the_insn.opcode & RD (~0)) >> 25;

  if (the_insn.exp.X_op != O_constant)
    {
      synthetize_setuw (insn);
      the_insn.opcode = (SRA_INSN | RS1 (rd) | RD (rd));
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
      return;
    }

  if (sizeof (offsetT) > 4)
    {
      if (the_insn.exp.X_add_number < -(offsetT) U0x80000000 ||
          the_insn.exp.X_add_number > (offsetT) U0xffffffff)
        {
          as_warn (_("setsw: number not in -2147483648..4294967295 range"));
        }
    }

  low32 = the_insn.exp.X_add_number;

  if (low32 >= 0)
    {
      synthetize_setuw (insn);
      return;
    }

  the_insn.reloc = BFD_RELOC_NONE;
  
  if (low32 < -(1 << 12))
    {
      the_insn.opcode = (SETHI_INSN | RD (rd) | 
                        (((~the_insn.exp.X_add_number) >> 10) & 0x3fffff));
      output_insn (insn, &the_insn);
      low32 = 0x1c00 | (low32 & 0x3ff);
      opc = RS1 (rd) | XOR_INSN;
    }
  else
    {
      opc = OR_INSN;
    }

  the_insn.opcode = (opc | RD (rd) | IMMED | (low32 & 0x1fff));
  output_insn (insn, &the_insn);
}

/* Handle the setx synthetic instruction.  */

static void
synthetize_setx (const struct sparc_opcode *insn)
{
  int upper32, lower32;
  int tmpreg = (the_insn.opcode & RS1 (~0)) >> 14;
  int dstreg = (the_insn.opcode & RD (~0)) >> 25;
  int upper_dstreg;
  int need_hh22_p = 0, need_hm10_p = 0, need_hi22_p = 0, need_lo10_p = 0;
  int need_xor10_p = 0;

  lower32 = ((the_insn.exp.X_add_number & U0xffffffff) ^ U0x80000000) - U0x80000000;
  upper32 = ((BSR (the_insn.exp.X_add_number, 32) & U0xffffffff) ^ U0x80000000) - U0x80000000;

  upper_dstreg = tmpreg;
  
  if (tmpreg == dstreg)
    as_warn (_("setx: temporary register same as destination register"));

  if (the_insn.exp.X_op != O_constant)
    {
      if (sparc_arch_size == 32)
	{
	  the_insn.exp.X_add_number &= 0xffffffff;
	  synthetize_setuw (insn);
	  return;
	}
      need_hh22_p = 1;
      need_hm10_p = 1;
      need_hi22_p = 1;
      need_lo10_p = 1;
      lower32 = 0;
      upper32 = 0;
    }
  else
    {
      the_insn.exp.X_add_number = 0;

      if (upper32 < -(1 << 12) || upper32 >= (1 << 12))
	need_hh22_p = 1;

      if ((need_hh22_p && (upper32 & 0x3ff) != 0)
	  || (!need_hh22_p && upper32 != 0 && upper32 != -1))
	need_hm10_p = 1;

      if (lower32 != 0 || (!need_hh22_p && !need_hm10_p))
	{
	  if (lower32 < -(1 << 12) || lower32 >= (1 << 12)
	      || (lower32 < 0 && upper32 != -1)
	      || (lower32 >= 0 && upper32 == -1))
	    need_hi22_p = 1;

	  if (need_hi22_p && upper32 == -1)
	    need_xor10_p = 1;
	  else if ((need_hi22_p && (lower32 & 0x3ff) != 0)
		   || (!need_hi22_p && (lower32 & 0x1fff) != 0)
		   || (!need_hi22_p && !need_hh22_p && !need_hm10_p))
	    need_lo10_p = 1;
	}
      else
	upper_dstreg = dstreg;
    }

  if (!upper_dstreg && dstreg)
    as_warn (_("setx: illegal temporary register g0"));

  if (need_hh22_p)
    {
      the_insn.opcode = SETHI_INSN | RD (upper_dstreg) | ((upper32 >> 10) & 0x3fffff);
      the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_SPARC_HH22 : BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

  if (need_hi22_p)
    {
      int value = need_xor10_p ? ~lower32 : lower32;
      the_insn.opcode = SETHI_INSN | RD (dstreg) | ((value >> 10) & 0x3fffff);
      the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_SPARC_LM22 : BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

  if (need_hm10_p)
    {
      int rs1_val = need_hh22_p ? RS1 (upper_dstreg) : 0;
      int imm_mask = need_hh22_p ? 0x3ff : 0x1fff;
      the_insn.opcode = OR_INSN | rs1_val | RD (upper_dstreg) | IMMED | (upper32 & imm_mask);
      the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_SPARC_HM10 : BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

  if (need_lo10_p)
    {
      int rs1_val = need_hi22_p ? RS1 (dstreg) : 0;
      int imm_mask = need_hi22_p ? 0x3ff : 0x1fff;
      the_insn.opcode = OR_INSN | rs1_val | RD (dstreg) | IMMED | (lower32 & imm_mask);
      the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_LO10 : BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

  if (need_hh22_p || need_hm10_p)
    {
      the_insn.opcode = SLLX_INSN | RS1 (upper_dstreg) | RD (upper_dstreg) | IMMED | 32;
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

  if (need_xor10_p)
    {
      the_insn.opcode = XOR_INSN | RS1 (dstreg) | RD (dstreg) | IMMED | 0x1c00 | (lower32 & 0x3ff);
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }
  else if ((need_hh22_p || need_hm10_p) && (need_hi22_p || need_lo10_p))
    {
      the_insn.opcode = OR_INSN | RS1 (dstreg) | RS2 (upper_dstreg) | RD (dstreg);
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }
}

/* Main entry point to assemble one instruction.  */

void
md_assemble (char *str)
{
  const struct sparc_opcode *insn;
  int special_case;

  if (!str)
    return;

  special_case = sparc_ip (str, &insn);
  if (insn == NULL)
    return;

  if (last_insn != NULL && (last_insn->flags & F_DELAYED) != 0)
    {
      if (dcti_couples_detect && (insn->flags & F_DELAYED) != 0)
        {
          int is_pre_v9_condbr = (max_architecture < SPARC_OPCODE_ARCH_V9 && 
                                   (last_insn->flags & F_CONDBR) != 0);
          int is_v9c_or_later = (max_architecture >= SPARC_OPCODE_ARCH_V9C);
          
          if (is_pre_v9_condbr || is_v9c_or_later)
            as_warn (_("unpredictable DCTI couple"));
        }

      if ((insn->flags & F_FBR) != 0)
        {
          int is_annullable = ((last_insn->flags & (F_UNBR | F_CONDBR | F_FBR)) != 0);
          int is_annulled = ((last_opcode & ANNUL) != 0);
          
          if (!is_annullable || !is_annulled)
            as_warn (_("FP branch in delay slot"));
        }
    }

  if (max_architecture < SPARC_OPCODE_ARCH_V9 && last_insn != NULL)
    {
      int is_fp_branch = ((insn->flags & F_FBR) != 0);
      int is_fp_compare = ((last_insn->flags & F_FLOAT) != 0 && 
                           (last_insn->match & OP3 (0x35)) == OP3 (0x35));
      
      if (is_fp_branch && is_fp_compare)
        {
          struct sparc_it nop_insn;
          nop_insn.opcode = NOP_INSN;
          nop_insn.reloc = BFD_RELOC_NONE;
          output_insn (insn, &nop_insn);
          as_warn (_("FP branch preceded by FP compare; NOP inserted"));
        }
    }

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
      {
        int rd = (the_insn.opcode >> 25) & 0x1f;
        output_insn (insn, &the_insn);
        gas_assert (the_insn.reloc == BFD_RELOC_NONE);
        the_insn.opcode = FMOVS_INSN | rd | RD (rd);
        output_insn (insn, &the_insn);
      }
      break;

    default:
      as_fatal (_("failed special case insn sanity check"));
    }
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
    {((uint64_t)HWCAP2_FJATHPLUS) << 32, "fjathplus"},
    {((uint64_t)HWCAP2_VIS3B) << 32, "vis3b"},
    {((uint64_t)HWCAP2_ADP) << 32, "adp"},
    {((uint64_t)HWCAP2_SPARC5) << 32, "sparc5"},
    {((uint64_t)HWCAP2_MWAIT) << 32, "mwait"},
    {((uint64_t)HWCAP2_XMPMUL) << 32, "xmpmul"},
    {((uint64_t)HWCAP2_XMONT) << 32, "xmont"},
    {((uint64_t)HWCAP2_NSEC) << 32, "nsec"},
    {((uint64_t)HWCAP2_SPARC6) << 32, "sparc6"},
    {((uint64_t)HWCAP2_ONADDSUB) << 32, "onaddsub"},
    {((uint64_t)HWCAP2_ONMUL) << 32, "onmul"},
    {((uint64_t)HWCAP2_ONDIV) << 32, "ondiv"},
    {((uint64_t)HWCAP2_DICTUNP) << 32, "dictunp"},
    {((uint64_t)HWCAP2_FPCMPSHL) << 32, "fpcmpshl"},
    {((uint64_t)HWCAP2_RLE) << 32, "rle"},
    {((uint64_t)HWCAP2_SHA3) << 32, "sha3"}
  };

  for (size_t i = 0; i < sizeof(hwcap_map) / sizeof(hwcap_map[0]); i++) {
    if (mask & hwcap_map[i].flag) {
      return hwcap_map[i].name;
    }
  }

  return "UNKNOWN";
}

/* Subroutine of md_assemble to do the actual parsing.  */

static int
sparc_ip (char *str, const struct sparc_opcode **pinsn)
{
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
  if (ISLOWER (*s))
    {
      do
	++s;
      while (ISLOWER (*s) || ISDIGIT (*s) || *s == '_');
    }

  switch (*s)
    {
    case '\0':
      break;

    case ',':
      comma = 1;
      *s++ = '\0';
      break;

    default:
      if (is_whitespace (*s))
	{
	  *s++ = '\0';
	  break;
	}
      as_bad (_("Unknown opcode: `%s'"), str);
      *pinsn = NULL;
      return special_case;
    }
  insn = str_hash_find (op_hash, str);
  *pinsn = insn;
  if (insn == NULL)
    {
      as_bad (_("Unknown opcode: `%s'"), str);
      return special_case;
    }
  if (comma)
    {
      *--s = ',';
    }

  argsStart = s;
  for (;;)
    {
      opcode = insn->match;
      memset (&the_insn, '\0', sizeof (the_insn));
      the_insn.reloc = BFD_RELOC_NONE;
      v9_arg_p = 0;

      for (args = insn->args;; ++args)
	{
	  switch (*args)
	    {
	    case 'K':
	      if (parse_membar_mask(&s, &opcode, &error_message))
		continue;
	      goto error;

	    case '3':
	      if (parse_siam_mode(&s, &opcode, &error_message))
		continue;
	      goto error;

	    case '*':
	      if (parse_prefetch_function(&s, &opcode, &error_message))
		continue;
	      goto error;

	    case '!':
	    case '?':
	      if (parse_priv_register(&s, priv_reg_table, *args, opcode, &error_message))
		continue;
	      goto error;

	    case '$':
	    case '%':
	      if (parse_priv_register(&s, hpriv_reg_table, *args, opcode, &error_message))
		continue;
	      goto error;

	    case '_':
	    case '/':
	      if (parse_priv_register(&s, v9a_asr_table, *args, opcode, &error_message))
		continue;
	      goto error;

	    case 'M':
	    case 'm':
	      if (parse_asr_register(&s, *args, &opcode, &error_message))
		continue;
	      goto error;

	    case 'I':
	      the_insn.reloc = BFD_RELOC_SPARC_11;
	      goto immediate;

	    case 'j':
	      the_insn.reloc = BFD_RELOC_SPARC_10;
	      goto immediate;

	    case ')':
	      if (parse_crypto_immediate(&s, &opcode, &error_message))
		continue;
	      goto error;

	    case 'X':
	      if (SPARC_OPCODE_ARCH_V9_P (max_architecture))
		the_insn.reloc = BFD_RELOC_SPARC_5;
	      else
		the_insn.reloc = BFD_RELOC_SPARC13;
	      goto immediate;

	    case 'Y':
	      if (SPARC_OPCODE_ARCH_V9_P (max_architecture))
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
	      if (*s == 'p' && s[1] == 'n')
		{
		  s += 2;
		  continue;
		}
	      break;

	    case 'T':
	      if (*s == 'p' && s[1] == 't')
		{
		  s += 2;
		  continue;
		}
	      break;

	    case 'z':
	      if (parse_condition_register(&s, "%icc", "%ncc", 32))
		continue;
	      break;

	    case 'Z':
	      if (parse_condition_register(&s, "%xcc", "%ncc", 64))
		continue;
	      break;

	    case '6':
	    case '7':
	    case '8':
	    case '9':
	      if (parse_fcc_register(&s, *args - '6'))
		continue;
	      break;

	    case 'P':
	      if (startswith (s, "%pc"))
		{
		  s += 3;
		  continue;
		}
	      break;

	    case 'W':
	      if (startswith (s, "%tick"))
		{
		  s += 5;
		  continue;
		}
	      break;

	    case '\0':
	      if (parse_end_of_insn(&s, &special_case))
		{
		  match = 1;
		  break;
		}
	      if (*s == '\0')
		match = 1;
	      break;

	    case '+':
	      if (*s == '+')
		{
		  ++s;
		  continue;
		}
	      if (*s == '-')
		{
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
	      if (is_whitespace (*s++))
		continue;
	      break;

	    case '#':
	      if (ISDIGIT (*s++))
		{
		  while (ISDIGIT (*s))
		    {
		      ++s;
		    }
		  continue;
		}
	      break;

	    case 'C':
	      if (startswith (s, "%csr"))
		{
		  s += 4;
		  continue;
		}
	      break;

	    case 'b':
	    case 'c':
	    case 'D':
	      if (parse_coproc_register(&s, *args, &opcode))
		continue;
	      break;

	    case 'r':
	    case 'O':
	    case '1':
	    case '2':
	    case 'd':
	      if (parse_general_register(&s, *args, &opcode, &mask))
		continue;
	      break;

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
            case '^':
	      if (parse_float_register(&s, args, &opcode, &v9_arg_p, &error_message))
		continue;
	      goto error;

	    case 'F':
	      if (startswith (s, "%fsr"))
		{
		  s += 4;
		  continue;
		}
	      break;

	    case '(':
	      if (startswith (s, "%efsr"))
		{
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
	      if (parse_immediate_operand(&s, &v9_arg_p, &special_case, insn))
		continue;
	      goto error;

	    case 'a':
	      if (*s++ == 'a')
		{
		  opcode |= ANNUL;
		  continue;
		}
	      break;

	    case 'A':
	      if (parse_asi(&s, &opcode, &sasi, &error_message))
		continue;
	      goto error;

	    case 'p':
	      if (startswith (s, "%psr"))
		{
		  s += 4;
		  continue;
		}
	      break;

	    case 'q':
	      if (startswith (s, "%fq"))
		{
		  s += 3;
		  continue;
		}
	      break;

	    case 'Q':
	      if (startswith (s, "%cq"))
		{
		  s += 3;
		  continue;
		}
	      break;

	    case 'S':
	      if (parse_special_instruction(str, &special_case))
		continue;
	      break;

	    case 'o':
	      if (!startswith (s, "%asi"))
		break;
	      s += 4;
	      continue;

	    case 's':
	      if (!startswith (s, "%fprs"))
		break;
	      s += 5;
	      continue;

	    case '{':
	      if (!startswith (s, "%mcdper"))
		break;
	      s += 7;
	      continue;

            case '&':
              if (!startswith (s, "%entropy"))
                break;
              s += 8;
              continue;

	    case 'E':
	      if (!startswith (s, "%ccr"))
		break;
	      s += 4;
	      continue;

	    case 't':
	      if (!startswith (s, "%tbr"))
		break;
	      s += 4;
	      continue;

	    case 'w':
	      if (!startswith (s, "%wim"))
		break;
	      s += 4;
	      continue;

            case '|':
	      if (parse_imm2(&s, &opcode, &error_message))
		continue;
	      goto error;
              
	    case 'x':
	      if (parse_opf_immediate(&s, &opcode))
		continue;
	      break;

	    case 'y':
	      if (!startswith (s, "%y"))
		break;
	      s += 2;
	      continue;

	    case 'u':
	    case 'U':
	      if (parse_sparclet_cpreg(&s, *args, &opcode, &error_message))
		continue;
	      goto error;

	    default:
	      as_fatal (_("failed sanity check."));
	    }

	  break;
	}

    error:
      if (match == 0)
	{
	  if (&insn[1] - sparc_opcodes < sparc_num_opcodes
	      && (insn->name == insn[1].name
		  || !strcmp (insn->name, insn[1].name)))
	    {
	      ++insn;
	      s = argsStart;
	      continue;
	    }
	  else
	    {
	      as_bad (_("Illegal operands%s"), error_message);
	      return special_case;
	    }
	}
      else
	{
	  if (validate_architecture(insn, sasi, str, argsStart, v9_arg_p))
	    break;
	  return special_case;
	}
    }

  the_insn.opcode = opcode;
  return special_case;
}

static char *skip_over_keyword(char *q)
{
    if (q == NULL) {
        return NULL;
    }
    
    if (*q == '#' || *q == '%') {
        q++;
    }
    
    while (*q != '\0' && (ISALNUM(*q) || *q == '_')) {
        q++;
    }
    
    return q;
}

static int
parse_sparc_asi (char **input_pointer_p, const sparc_asi **value_p)
{
  char *p;
  char *q;
  char saved_char;
  const sparc_asi *value;

  if (input_pointer_p == NULL || *input_pointer_p == NULL || value_p == NULL)
    return 0;

  p = *input_pointer_p;
  q = skip_over_keyword(p);
  
  if (q == NULL || q == p)
    return 0;

  saved_char = *q;
  *q = '\0';
  
  value = sparc_encode_asi(p);
  
  *q = saved_char;
  
  if (value == NULL)
    return 0;
    
  *value_p = value;
  *input_pointer_p = q;
  
  return 1;
}

/* Parse an argument that can be expressed as a keyword.
   (eg: #StoreStore or %ccfr).
   The result is a boolean indicating success.
   If successful, INPUT_POINTER is updated.  */

static int parse_keyword_arg(int (*lookup_fn)(const char *), char **input_pointerP, int *valueP)
{
    if (lookup_fn == NULL || input_pointerP == NULL || *input_pointerP == NULL || valueP == NULL) {
        return 0;
    }

    char *start = *input_pointerP;
    char *end = skip_over_keyword(start);
    
    if (end == NULL || end == start) {
        return 0;
    }
    
    char saved_char = *end;
    *end = '\0';
    
    int lookup_result = lookup_fn(start);
    
    *end = saved_char;
    
    if (lookup_result == -1) {
        return 0;
    }
    
    *valueP = lookup_result;
    *input_pointerP = end;
    
    return 1;
}

/* Parse an argument that is a constant expression.
   The result is a boolean indicating success.  */

static int
parse_const_expr_arg (char **input_pointerP, int *valueP)
{
  char *save;
  expressionS exp;

  if (input_pointerP == NULL || *input_pointerP == NULL || valueP == NULL)
    return 0;

  save = input_line_pointer;
  input_line_pointer = *input_pointerP;

  if (*input_line_pointer == '%')
    {
      input_line_pointer = save;
      return 0;
    }

  expression (&exp);
  *input_pointerP = input_line_pointer;
  input_line_pointer = save;

  if (exp.X_op != O_constant)
    return 0;

  *valueP = exp.X_add_number;
  return 1;
}

/* Subroutine of sparc_ip to parse an expression.  */

static int get_expression(char *str)
{
    char *save_in;
    segT seg;

    if (str == NULL) {
        the_insn.error = _("invalid input");
        return 1;
    }

    save_in = input_line_pointer;
    input_line_pointer = str;
    seg = expression(&the_insn.exp);
    
    int is_valid_segment = (seg == absolute_section ||
                            seg == text_section ||
                            seg == data_section ||
                            seg == bss_section ||
                            seg == undefined_section);
    
    expr_parse_end = input_line_pointer;
    input_line_pointer = save_in;
    
    if (!is_valid_segment) {
        the_insn.error = _("bad segment");
        return 1;
    }
    
    return 0;
}

/* Subroutine of md_assemble to output one insn.  */

static void
output_insn (const struct sparc_opcode *insn, struct sparc_it *theinsn)
{
  char *toP;
  
  if (insn == NULL || theinsn == NULL) {
    return;
  }
  
  toP = frag_more (4);
  if (toP == NULL) {
    return;
  }

  if (INSN_BIG_ENDIAN) {
    number_to_chars_bigendian (toP, theinsn->opcode, 4);
  } else {
    number_to_chars_littleendian (toP, theinsn->opcode, 4);
  }

  if (theinsn->reloc != BFD_RELOC_NONE) {
    fixS *fixP = fix_new_exp (frag_now,
                             (toP - frag_now->fr_literal),
                             4,
                             &theinsn->exp,
                             theinsn->pcrel,
                             theinsn->reloc);
    if (fixP != NULL) {
      fixP->fx_no_overflow = 1;
      if (theinsn->reloc == BFD_RELOC_SPARC_OLO10) {
        fixP->tc_fix_data = theinsn->exp2.X_add_number;
      }
    }
  }

  last_insn = insn;
  last_opcode = theinsn->opcode;

  dwarf2_emit_insn (4);
}

const char *md_atof(int type, char *litP, int *sizeP)
{
    if (litP == NULL || sizeP == NULL) {
        return "Invalid parameters";
    }
    
    return ieee_md_atof(type, litP, sizeP, target_big_endian);
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

void
md_number_to_chars (char *buf, valueT val, int n)
{
  if (buf == NULL) {
    return;
  }

  if (target_big_endian) {
    number_to_chars_bigendian (buf, val, n);
    return;
  }

  if (!target_little_endian_data) {
    number_to_chars_littleendian (buf, val, n);
    return;
  }

  int is_debug_word = (n == 4 || n == 2) && 
                      now_seg != NULL && 
                      !(now_seg->flags & SEC_ALLOC);

  if (is_debug_word) {
    number_to_chars_bigendian (buf, val, n);
  } else {
    number_to_chars_littleendian (buf, val, n);
  }
}

/* Apply a fixS to the frags, now that we know the value it ought to
   hold.  */

void
md_apply_fix (fixS *fixP, valueT *valP, segT segment ATTRIBUTE_UNUSED)
{
  char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
  offsetT val = *valP;
  long insn;

  gas_assert (fixP->fx_r_type < BFD_RELOC_UNUSED);

  fixP->fx_addnumber = val;

  if (fixP->fx_addsy != NULL)
    {
      if (fixP->fx_r_type >= BFD_RELOC_SPARC_TLS_GD_HI22 &&
          fixP->fx_r_type <= BFD_RELOC_SPARC_TLS_TPOFF64)
        {
          S_SET_THREAD_LOCAL (fixP->fx_addsy);
        }
      return;
    }

  if (fixP->fx_r_type == BFD_RELOC_32_PCREL_S2 && fixP->fx_addsy)
    val += fixP->fx_where + fixP->fx_frag->fr_address;

  if (handle_data_relocation(fixP, buf, val))
    return;

  if (fixP->fx_r_type == BFD_RELOC_VTABLE_INHERIT ||
      fixP->fx_r_type == BFD_RELOC_VTABLE_ENTRY)
    {
      fixP->fx_done = 0;
      return;
    }

  insn = INSN_BIG_ENDIAN ? bfd_getb32 (buf) : bfd_getl32 (buf);

  if (fixP->fx_r_type == BFD_RELOC_32_PCREL_S2)
    {
      handle_pcrel_s2_relocation(fixP, buf, &insn, &val);
    }
  else
    {
      handle_instruction_relocation(fixP, &insn, val);
    }

  if (INSN_BIG_ENDIAN)
    bfd_putb32 (insn, buf);
  else
    bfd_putl32 (insn, buf);

  if (fixP->fx_addsy == 0 && !fixP->fx_pcrel)
    fixP->fx_done = 1;
}

static int
handle_data_relocation(fixS *fixP, char *buf, offsetT val)
{
  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_8:
      md_number_to_chars (buf, val, 1);
      return 1;
    case BFD_RELOC_16:
    case BFD_RELOC_SPARC_UA16:
      md_number_to_chars (buf, val, 2);
      return 1;
    case BFD_RELOC_32:
    case BFD_RELOC_SPARC_UA32:
    case BFD_RELOC_SPARC_REV32:
      md_number_to_chars (buf, val, 4);
      return 1;
    case BFD_RELOC_64:
    case BFD_RELOC_SPARC_UA64:
      md_number_to_chars (buf, val, 8);
      return 1;
    default:
      return 0;
    }
}

static void
handle_pcrel_s2_relocation(fixS *fixP, char *buf, long *insn, offsetT *val)
{
  *val = *val >> 2;
  
  if (!sparc_pic_code || fixP->fx_addsy == NULL || symbol_section_p (fixP->fx_addsy))
    ++(*val);

  *insn |= *val & 0x3fffffff;

  if (sparc_relax && fixP->fx_addsy == NULL &&
      fixP->fx_where + 8 <= fixP->fx_frag->fr_fix)
    {
      optimize_call_instruction(fixP, buf, insn, *val);
    }
}

static void
optimize_call_instruction(fixS *fixP, char *buf, long *insn, offsetT val)
{
#define G0		0
#define O7		15
#define XCC		(2 << 20)
#define COND(x)		(((x)&0xf)<<25)
#define CONDA		COND(0x8)
#define INSN_BPA	(F2(0,1) | CONDA | BPRED | XCC)
#define INSN_BA		(F2(0,2) | CONDA)
#define INSN_OR		F3(2, 0x2, 0)
#define INSN_NOP	F2(0,4)

  long delay;
  long setter;
  int reg;

  delay = INSN_BIG_ENDIAN ? bfd_getb32 (buf + 4) : bfd_getl32 (buf + 4);
  
  if ((*insn & OP (~0)) != OP (1) || (delay & OP (~0)) != OP (2))
    return;
    
  if ((delay & OP3 (~0)) != OP3 (0x3d) &&
      ((delay & OP3 (0x28)) != 0 || ((delay & RD (~0)) != RD (O7))))
    return;
    
  if ((delay & RS1 (~0)) == RS1 (O7) ||
      ((delay & F3I (~0)) == 0 && (delay & RS2 (~0)) == RS2 (O7)))
    return;
    
  if ((val & 0x3fe00000) && (val & 0x3fe00000) != 0x3fe00000)
    return;

  if (((val & 0x3c0000) == 0 || (val & 0x3c0000) == 0x3c0000) &&
      (sparc_arch_size == 64 || current_architecture >= SPARC_OPCODE_ARCH_V9))
    {
      *insn = INSN_BPA | (val & 0x7ffff);
    }
  else
    {
      *insn = INSN_BA | (val & 0x3fffff);
    }

  if (fixP->fx_where >= 4 &&
      ((delay & (0xffffffff ^ RS1 (~0))) == (INSN_OR | RD (O7) | RS2 (G0))))
    {
      setter = INSN_BIG_ENDIAN ? bfd_getb32 (buf - 4) : bfd_getl32 (buf - 4);
      
      if ((setter & (0xffffffff ^ RD (~0))) == (INSN_OR | RS1 (O7) | RS2 (G0)))
        {
          reg = (delay & RS1 (~0)) >> 14;
          if (reg == ((setter & RD (~0)) >> 25) && reg != G0 && reg != O7)
            {
              if (INSN_BIG_ENDIAN)
                bfd_putb32 (INSN_NOP, buf + 4);
              else
                bfd_putl32 (INSN_NOP, buf + 4);
            }
        }
    }
}

static void
handle_instruction_relocation(fixS *fixP, long *insn, offsetT val)
{
  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_SPARC_11:
      if (!in_signed_range (val, 0x7ff))
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      *insn |= val & 0x7ff;
      break;

    case BFD_RELOC_SPARC_10:
      if (!in_signed_range (val, 0x3ff))
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      *insn |= val & 0x3ff;
      break;

    case BFD_RELOC_SPARC_7:
      if (!in_bitfield_range (val, 0x7f))
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      *insn |= val & 0x7f;
      break;

    case BFD_RELOC_SPARC_6:
      if (!in_bitfield_range (val, 0x3f))
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      *insn |= val & 0x3f;
      break;

    case BFD_RELOC_SPARC_5:
      if (!in_bitfield_range (val, 0x1f))
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      *insn |= val & 0x1f;
      break;

    case BFD_RELOC_SPARC_WDISP10:
      if ((val & 3) || val >= 0x007fc || val <= -(offsetT) 0x808)
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      val = (val >> 2) + 1;
      *insn |= ((val & 0x300) << 11) | ((val & 0xff) << 5);
      break;

    case BFD_RELOC_SPARC_WDISP16:
      if ((val & 3) || val >= 0x1fffc || val <= -(offsetT) 0x20008)
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      val = (val >> 2) + 1;
      *insn |= ((val & 0xc000) << 6) | (val & 0x3fff);
      break;

    case BFD_RELOC_SPARC_WDISP19:
      if ((val & 3) || val >= 0xffffc || val <= -(offsetT) 0x100008)
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      val = (val >> 2) + 1;
      *insn |= val & 0x7ffff;
      break;

    case BFD_RELOC_SPARC_HH22:
      val = BSR (val, 32);
    case BFD_RELOC_SPARC_LM22:
    case BFD_RELOC_HI22:
      if (!fixP->fx_addsy)
        *insn |= (val >> 10) & 0x3fffff;
      else
        *insn &= ~0xffff;
      break;

    case BFD_RELOC_SPARC22:
      if (val & ~0x003fffff)
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      *insn |= (val & 0x3fffff);
      break;

    case BFD_RELOC_SPARC_HM10:
      val = BSR (val, 32);
    case BFD_RELOC_LO10:
      if (!fixP->fx_addsy)
        *insn |= val & 0x3ff;
      else
        *insn &= ~0xff;
      break;

    case BFD_RELOC_SPARC_OLO10:
      val &= 0x3ff;
      val += fixP->tc_fix_data;
    case BFD_RELOC_SPARC13:
      if (!in_signed_range (val, 0x1fff))
        as_bad_where (fixP->fx_file, fixP->fx_line, _("relocation overflow"));
      *insn |= val & 0x1fff;
      break;

    case BFD_RELOC_SPARC_WDISP22:
      val = (val >> 2) + 1;
    case BFD_RELOC_SPARC_BASE22:
      *insn |= val & 0x3fffff;
      break;

    case BFD_RELOC_SPARC_H34:
      if (!fixP->fx_addsy)
        {
          bfd_vma tval = val;
          tval >>= 12;
          *insn |= tval & 0x3fffff;
        }
      break;

    case BFD_RELOC_SPARC_H44:
      if (!fixP->fx_addsy)
        {
          bfd_vma tval = val;
          tval >>= 22;
          *insn |= tval & 0x3fffff;
        }
      break;

    case BFD_RELOC_SPARC_M44:
      if (!fixP->fx_addsy)
        *insn |= (val >> 12) & 0x3ff;
      break;

    case BFD_RELOC_SPARC_L44:
      if (!fixP->fx_addsy)
        *insn |= val & 0xfff;
      break;

    case BFD_RELOC_SPARC_HIX22:
      if (!fixP->fx_addsy)
        {
          val ^= ~(offsetT) 0;
          *insn |= (val >> 10) & 0x3fffff;
        }
      break;

    case BFD_RELOC_SPARC_LOX10:
      if (!fixP->fx_addsy)
        *insn |= 0x1c00 | (val & 0x3ff);
      break;

    case BFD_RELOC_NONE:
      break;

    default:
      as_bad_where (fixP->fx_file, fixP->fx_line,
                    _("bad or unhandled relocation type: 0x%02x"),
                    fixP->fx_r_type);
      break;
    }
}

/* Translate internal representation of relocation info to BFD target
   format.  */

arelent **
tc_gen_reloc (asection *section, fixS *fixp)
{
  static arelent *relocs[3];
  arelent *reloc;
  bfd_reloc_code_real_type code;

  reloc = notes_alloc (sizeof (arelent));
  if (!reloc)
    return NULL;
  
  reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  if (!reloc->sym_ptr_ptr)
    return NULL;
    
  relocs[0] = reloc;
  relocs[1] = NULL;
  *reloc->sym_ptr_ptr = symbol_get_bfdsym (fixp->fx_addsy);
  reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;

  code = handle_reloc_type(fixp);
  if (code == BFD_RELOC_NONE)
    return NULL;

  if (sparc_pic_code)
    code = adjust_pic_reloc_code(code, fixp);

  if (bfd_section_flags (section) & SEC_DEBUGGING)
    code = adjust_debug_reloc_code(code);

  if (code == BFD_RELOC_SPARC_OLO10)
    reloc->howto = bfd_reloc_type_lookup (stdoutput, BFD_RELOC_LO10);
  else
    reloc->howto = bfd_reloc_type_lookup (stdoutput, code);
    
  if (!reloc->howto)
    {
      as_bad_where (fixp->fx_file, fixp->fx_line,
                    _("internal error: can't export reloc type %d (`%s')"),
                    fixp->fx_r_type, bfd_get_reloc_code_name (code));
      relocs[0] = NULL;
      return relocs;
    }

  set_reloc_addend(reloc, fixp, code, section);

  if (code == BFD_RELOC_SPARC_OLO10)
    {
      if (!create_olo10_secondary_reloc(relocs, fixp))
        return NULL;
    }

  return relocs;
}

static bfd_reloc_code_real_type
handle_reloc_type(fixS *fixp)
{
  bfd_reloc_code_real_type code;
  
  switch (fixp->fx_r_type)
    {
    case BFD_RELOC_8:
    case BFD_RELOC_16:
    case BFD_RELOC_32:
    case BFD_RELOC_64:
      if (fixp->fx_pcrel)
        {
          code = get_pcrel_code(fixp);
          if (code != BFD_RELOC_NONE && fixp->fx_pcrel)
            fixp->fx_addnumber = fixp->fx_offset;
        }
      else
        code = fixp->fx_r_type;
      break;
      
    case BFD_RELOC_HI22:
    case BFD_RELOC_LO10:
    case BFD_RELOC_32_PCREL_S2:
    case BFD_RELOC_SPARC13:
    case BFD_RELOC_SPARC22:
    case BFD_RELOC_SPARC_PC22:
    case BFD_RELOC_SPARC_PC10:
    case BFD_RELOC_SPARC_BASE13:
    case BFD_RELOC_SPARC_WDISP10:
    case BFD_RELOC_SPARC_WDISP16:
    case BFD_RELOC_SPARC_WDISP19:
    case BFD_RELOC_SPARC_WDISP22:
    case BFD_RELOC_SPARC_5:
    case BFD_RELOC_SPARC_6:
    case BFD_RELOC_SPARC_7:
    case BFD_RELOC_SPARC_10:
    case BFD_RELOC_SPARC_11:
    case BFD_RELOC_SPARC_HH22:
    case BFD_RELOC_SPARC_HM10:
    case BFD_RELOC_SPARC_LM22:
    case BFD_RELOC_SPARC_PC_HH22:
    case BFD_RELOC_SPARC_PC_HM10:
    case BFD_RELOC_SPARC_PC_LM22:
    case BFD_RELOC_SPARC_H34:
    case BFD_RELOC_SPARC_H44:
    case BFD_RELOC_SPARC_M44:
    case BFD_RELOC_SPARC_L44:
    case BFD_RELOC_SPARC_HIX22:
    case BFD_RELOC_SPARC_LOX10:
    case BFD_RELOC_SPARC_REV32:
    case BFD_RELOC_SPARC_OLO10:
    case BFD_RELOC_SPARC_UA16:
    case BFD_RELOC_SPARC_UA32:
    case BFD_RELOC_SPARC_UA64:
    case BFD_RELOC_8_PCREL:
    case BFD_RELOC_16_PCREL:
    case BFD_RELOC_32_PCREL:
    case BFD_RELOC_64_PCREL:
    case BFD_RELOC_SPARC_PLT32:
    case BFD_RELOC_SPARC_PLT64:
    case BFD_RELOC_VTABLE_ENTRY:
    case BFD_RELOC_VTABLE_INHERIT:
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
    case BFD_RELOC_SPARC_TLS_DTPOFF32:
    case BFD_RELOC_SPARC_TLS_DTPOFF64:
    case BFD_RELOC_SPARC_GOTDATA_OP_HIX22:
    case BFD_RELOC_SPARC_GOTDATA_OP_LOX10:
    case BFD_RELOC_SPARC_GOTDATA_OP:
      code = fixp->fx_r_type;
      break;
      
    default:
      abort ();
      return BFD_RELOC_NONE;
    }
    
  return code;
}

static bfd_reloc_code_real_type
get_pcrel_code(fixS *fixp)
{
  bfd_reloc_code_real_type code;
  
  switch (fixp->fx_size)
    {
    case 1:
      code = BFD_RELOC_8_PCREL;
      break;
    case 2:
      code = BFD_RELOC_16_PCREL;
      break;
    case 4:
      code = BFD_RELOC_32_PCREL;
      break;
#ifdef BFD64
    case 8:
      code = BFD_RELOC_64_PCREL;
      break;
#endif
    default:
      as_bad_where (fixp->fx_file, fixp->fx_line,
                    _("can not do %d byte pc-relative relocation"),
                    fixp->fx_size);
      code = fixp->fx_r_type;
      fixp->fx_pcrel = 0;
      break;
    }
    
  return code;
}

static bfd_reloc_code_real_type
adjust_pic_reloc_code(bfd_reloc_code_real_type code, fixS *fixp)
{
#define GOT_NAME "_GLOBAL_OFFSET_TABLE_"
#ifdef TE_VXWORKS
#define GOTT_BASE "__GOTT_BASE__"
#define GOTT_INDEX "__GOTT_INDEX__"
#endif

  switch (code)
    {
    case BFD_RELOC_32_PCREL_S2:
      if (generic_force_reloc (fixp))
        code = BFD_RELOC_SPARC_WPLT30;
      break;
      
    case BFD_RELOC_HI22:
      code = BFD_RELOC_SPARC_GOT22;
      if (fixp->fx_addsy != NULL)
        {
          if (strcmp (S_GET_NAME (fixp->fx_addsy), GOT_NAME) == 0)
            code = BFD_RELOC_SPARC_PC22;
#ifdef TE_VXWORKS
          if (strcmp (S_GET_NAME (fixp->fx_addsy), GOTT_BASE) == 0
              || strcmp (S_GET_NAME (fixp->fx_addsy), GOTT_INDEX) == 0)
            code = BFD_RELOC_HI22;
#endif
        }
      break;
      
    case BFD_RELOC_LO10:
      code = BFD_RELOC_SPARC_GOT10;
      if (fixp->fx_addsy != NULL)
        {
          if (strcmp (S_GET_NAME (fixp->fx_addsy), GOT_NAME) == 0)
            code = BFD_RELOC_SPARC_PC10;
#ifdef TE_VXWORKS
          if (strcmp (S_GET_NAME (fixp->fx_addsy), GOTT_BASE) == 0
              || strcmp (S_GET_NAME (fixp->fx_addsy), GOTT_INDEX) == 0)
            code = BFD_RELOC_LO10;
#endif
        }
      break;
      
    case BFD_RELOC_SPARC13:
      code = BFD_RELOC_SPARC_GOT13;
      break;
      
    default:
      break;
    }
    
  return code;
}

static bfd_reloc_code_real_type
adjust_debug_reloc_code(bfd_reloc_code_real_type code)
{
  switch (code)
    {
    case BFD_RELOC_16:
      return BFD_RELOC_SPARC_UA16;
    case BFD_RELOC_32:
      return BFD_RELOC_SPARC_UA32;
    case BFD_RELOC_64:
      return BFD_RELOC_SPARC_UA64;
    default:
      return code;
    }
}

static void
set_reloc_addend(arelent *reloc, fixS *fixp, bfd_reloc_code_real_type code, asection *section)
{
  if (code != BFD_RELOC_32_PCREL_S2
      && code != BFD_RELOC_SPARC_WDISP22
      && code != BFD_RELOC_SPARC_WDISP16
      && code != BFD_RELOC_SPARC_WDISP19
      && code != BFD_RELOC_SPARC_WDISP10
      && code != BFD_RELOC_SPARC_WPLT30
      && code != BFD_RELOC_SPARC_TLS_GD_CALL
      && code != BFD_RELOC_SPARC_TLS_LDM_CALL)
    {
      reloc->addend = fixp->fx_addnumber;
    }
  else if (symbol_section_p (fixp->fx_addsy))
    {
      reloc->addend = (section->vma
                       + fixp->fx_addnumber
                       + md_pcrel_from (fixp));
    }
  else
    {
      reloc->addend = fixp->fx_offset;
    }
}

static int
create_olo10_secondary_reloc(arelent **relocs, fixS *fixp)
{
  arelent *reloc;
  
  reloc = notes_alloc (sizeof (arelent));
  if (!reloc)
    return 0;
    
  reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  if (!reloc->sym_ptr_ptr)
    return 0;
    
  relocs[1] = reloc;
  relocs[2] = NULL;
  *reloc->sym_ptr_ptr = symbol_get_bfdsym (section_symbol (absolute_section));
  reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;
  reloc->howto = bfd_reloc_type_lookup (stdoutput, BFD_RELOC_SPARC13);
  reloc->addend = fixp->tc_fix_data;
  
  return 1;
}

/* We have no need to default values of symbols.  */

symbolS *
md_undefined_symbol (char *name ATTRIBUTE_UNUSED)
{
  return NULL;
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
  if (fixP == NULL) {
    return 0;
  }
  
  if (fixP->fx_frag == NULL) {
    return 0;
  }
  
  long ret = fixP->fx_where + fixP->fx_frag->fr_address;
  
  if (!sparc_pic_code) {
    ret += fixP->fx_size;
    return ret;
  }
  
  if (fixP->fx_addsy == NULL) {
    ret += fixP->fx_size;
    return ret;
  }
  
  if (symbol_section_p(fixP->fx_addsy)) {
    ret += fixP->fx_size;
  }
  
  return ret;
}

/* Return log2 (VALUE), or -1 if VALUE is not an exact positive power
   of two.  */

static int mylog2(int value)
{
    if (value <= 0) {
        return -1;
    }

    int shift = 0;
    while ((value & 1) == 0) {
        value >>= 1;
        shift++;
    }

    if (value == 1) {
        return shift;
    }
    
    return -1;
}

/* Sort of like s_lcomm.  */

static void
s_reserve (int ignore ATTRIBUTE_UNUSED)
{
  char *name;
  char *p;
  char c;
  int align;
  int size;
  symbolS *symbolP;

  c = get_symbol_name (&name);
  p = input_line_pointer;
  restore_line_pointer (c);
  SKIP_WHITESPACE ();

  if (*input_line_pointer != ',')
    {
      as_bad (_("Expected comma after name"));
      ignore_rest_of_line ();
      return;
    }

  ++input_line_pointer;
  size = get_absolute_expression ();
  
  if (size < 0)
    {
      as_bad (_("BSS length (%d.) <0! Ignored."), size);
      ignore_rest_of_line ();
      return;
    }

  *p = 0;
  symbolP = symbol_find_or_make (name);
  *p = c;

  if (!startswith (input_line_pointer, ",\"bss\"") &&
      !startswith (input_line_pointer, ",\".bss\""))
    {
      as_bad (_("bad .reserve segment -- expected BSS segment"));
      return;
    }

  input_line_pointer += (input_line_pointer[2] == '.') ? 7 : 6;
  SKIP_WHITESPACE ();

  align = 0;
  if (*input_line_pointer == ',')
    {
      ++input_line_pointer;
      SKIP_WHITESPACE ();
      
      if (*input_line_pointer == '\n')
        {
          as_bad (_("missing alignment"));
          ignore_rest_of_line ();
          return;
        }

      align = (int) get_absolute_expression ();

      if (align < 0)
        {
          as_bad (_("negative alignment"));
          ignore_rest_of_line ();
          return;
        }

      if (align != 0)
        {
          int temp = mylog2 (align);
          if (temp < 0)
            {
              as_bad (_("alignment not a power of 2"));
              ignore_rest_of_line ();
              return;
            }
          align = temp;
        }

      record_alignment (bss_section, align);
    }

  if (S_IS_DEFINED (symbolP))
    {
      as_warn (_("Ignoring attempt to re-define symbol %s"),
               S_GET_NAME (symbolP));
    }
  else if (!need_pass_2)
    {
      segT current_seg = now_seg;
      subsegT current_subseg = now_subseg;

      subseg_set (bss_section, 1);

      if (align)
        frag_align (align, 0, 0);

      if (S_GET_SEGMENT (symbolP) == bss_section)
        symbol_get_frag (symbolP)->fr_symbol = NULL;

      symbol_set_frag (symbolP, frag_now);
      char *pfrag = frag_var (rs_org, 1, 1, 0, symbolP, size, NULL);
      *pfrag = 0;

      S_SET_SEGMENT (symbolP, bss_section);
      subseg_set (current_seg, current_subseg);
      S_SET_SIZE (symbolP, size);
    }

  demand_empty_rest_of_line ();
}

static void
s_common (int ignore ATTRIBUTE_UNUSED)
{
  char *name;
  char c;
  char *p;
  offsetT temp, size;
  symbolS *symbolP;

  c = get_symbol_name (&name);
  p = input_line_pointer;
  restore_line_pointer (c);
  SKIP_WHITESPACE ();
  
  if (*input_line_pointer != ',')
    {
      as_bad (_("Expected comma after symbol-name"));
      ignore_rest_of_line ();
      return;
    }

  input_line_pointer++;
  temp = get_absolute_expression ();
  
  if (temp < 0)
    {
      as_bad (_(".COMMon length (%lu) out of range ignored"),
              (unsigned long) temp);
      ignore_rest_of_line ();
      return;
    }
  
  size = temp;
  *p = 0;
  symbolP = symbol_find_or_make (name);
  *p = c;
  
  if (S_IS_DEFINED (symbolP) && ! S_IS_COMMON (symbolP))
    {
      as_bad (_("Ignoring attempt to re-define symbol"));
      ignore_rest_of_line ();
      return;
    }
  
  if (S_GET_VALUE (symbolP) != 0 && S_GET_VALUE (symbolP) != (valueT) size)
    {
      as_warn (_("Length of .comm \"%s\" is already %ld. Not changed to %ld."),
               S_GET_NAME (symbolP), (long) S_GET_VALUE (symbolP), (long) size);
    }
  
  know (symbol_get_frag (symbolP) == &zero_address_frag);
  
  if (*input_line_pointer != ',')
    {
      as_bad (_("Expected comma after common length"));
      ignore_rest_of_line ();
      return;
    }
  
  input_line_pointer++;
  SKIP_WHITESPACE ();
  
  if (*input_line_pointer != '"')
    {
      temp = get_absolute_expression ();
      
      if (temp < 0)
        {
          as_bad (_("negative alignment"));
          ignore_rest_of_line ();
          return;
        }
      
      if (symbol_get_obj (symbolP)->local)
        {
          if (!handle_local_common (symbolP, size, temp))
            {
              ignore_rest_of_line ();
              return;
            }
        }
      else
        {
          setup_external_common (symbolP, size, temp);
        }
    }
  else
    {
      if (!handle_segment_specification (symbolP, size))
        {
          handle_bad_common_segment ();
          return;
        }
    }
  
  symbol_get_bfdsym (symbolP)->flags |= BSF_OBJECT;
  demand_empty_rest_of_line ();
}

static int
handle_local_common (symbolS *symbolP, offsetT size, offsetT temp)
{
  segT old_sec;
  int old_subsec;
  int align;
  char *p;
  
  old_sec = now_seg;
  old_subsec = now_subseg;
  
  align = (temp == 0) ? 0 : mylog2 (temp);
  
  if (align < 0)
    {
      as_bad (_("alignment not a power of 2"));
      return 0;
    }
  
  record_alignment (bss_section, align);
  subseg_set (bss_section, 0);
  
  if (align)
    frag_align (align, 0, 0);
  
  if (S_GET_SEGMENT (symbolP) == bss_section)
    symbol_get_frag (symbolP)->fr_symbol = 0;
  
  symbol_set_frag (symbolP, frag_now);
  p = frag_var (rs_org, 1, 1, 0, symbolP, size, NULL);
  *p = 0;
  
  S_SET_SEGMENT (symbolP, bss_section);
  S_CLEAR_EXTERNAL (symbolP);
  S_SET_SIZE (symbolP, size);
  
  subseg_set (old_sec, old_subsec);
  return 1;
}

static void
setup_external_common (symbolS *symbolP, offsetT size, offsetT temp)
{
  S_SET_VALUE (symbolP, size);
  S_SET_ALIGN (symbolP, temp);
  S_SET_SIZE (symbolP, size);
  S_SET_EXTERNAL (symbolP);
  S_SET_SEGMENT (symbolP, bfd_com_section_ptr);
}

static int
handle_segment_specification (symbolS *symbolP, offsetT size)
{
  input_line_pointer++;
  
  if (*input_line_pointer == '.')
    input_line_pointer++;
  
  if (!startswith (input_line_pointer, "bss\"") &&
      !startswith (input_line_pointer, "data\""))
    {
      while (*--input_line_pointer != '"')
        ;
      input_line_pointer--;
      return 0;
    }
  
  while (*input_line_pointer++ != '"')
    ;
  
  setup_external_common (symbolP, size, 0);
  return 1;
}

static void
handle_bad_common_segment (void)
{
  char *p = input_line_pointer;
  char c;
  
  while (*p && *p != '\n')
    p++;
  
  c = *p;
  *p = '\0';
  as_bad (_("bad .common segment %s"), input_line_pointer + 1);
  *p = c;
  input_line_pointer = p;
  ignore_rest_of_line ();
}

/* Handle the .empty pseudo-op.  This suppresses the warnings about
   invalid delay slot usage.  */

static void s_empty(int ignore ATTRIBUTE_UNUSED)
{
    last_insn = NULL;
}

static void
s_seg (int ignore ATTRIBUTE_UNUSED)
{
  static const struct {
    const char *name;
    size_t len;
    void (*handler)(void);
  } segments[] = {
    { "\"text\"", 6, NULL },
    { "\"data\"", 6, NULL },
    { "\"data1\"", 7, NULL },
    { "\"bss\"", 5, NULL }
  };

  for (size_t i = 0; i < sizeof(segments) / sizeof(segments[0]); i++)
  {
    if (startswith (input_line_pointer, segments[i].name))
    {
      input_line_pointer += segments[i].len;
      
      switch (i)
      {
        case 0:
          s_text (0);
          break;
        case 1:
          s_data (0);
          break;
        case 2:
          s_data1 ();
          break;
        case 3:
          subseg_set (data_section, 255);
          break;
      }
      return;
    }
  }

  as_bad (_("Unknown segment type"));
  demand_empty_rest_of_line ();
}

static void s_data1(void)
{
    subseg_set(data_section, 1);
    demand_empty_rest_of_line();
}

static void
s_proc (int ignore ATTRIBUTE_UNUSED)
{
  while (*input_line_pointer != '\0' && !is_end_of_stmt (*input_line_pointer))
    {
      ++input_line_pointer;
    }
  if (*input_line_pointer != '\0')
    {
      ++input_line_pointer;
    }
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
  int size = (sparc_arch_size == 32) ? 4 : 8;
  cons (size);
}

/* Handle the SPARC ELF .register pseudo-op.  This sets the binding of a
   global register.
   The syntax is:

   .register %g[2367],{#scratch|symbolname|#ignore}
*/

static void
s_register (int ignore ATTRIBUTE_UNUSED)
{
  char c;
  int reg;
  char *regname;

  if (!validate_register_syntax())
    {
      report_register_syntax_error();
      return;
    }

  reg = input_line_pointer[2] - '0';
  input_line_pointer += 4;

  c = parse_register_name(&regname);

  if (sparc_arch_size == 64)
    {
      process_global_register(reg, regname);
    }

  (void) restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

static int validate_register_syntax(void)
{
  return input_line_pointer[0] == '%'
      && input_line_pointer[1] == 'g'
      && ((input_line_pointer[2] & ~1) == '2'
          || (input_line_pointer[2] & ~1) == '6')
      && input_line_pointer[3] == ',';
}

static void report_register_syntax_error(void)
{
  as_bad (_("register syntax is .register %%g[2367],{#scratch|symbolname|#ignore}"));
}

static char parse_register_name(char **regname)
{
  char c;
  
  if (*input_line_pointer == '#')
    {
      ++input_line_pointer;
      c = get_symbol_name (regname);
      validate_special_register_name(*regname);
      if ((*regname)[0] == 'i')
        *regname = NULL;
      else
        *regname = (char *) "";
    }
  else
    {
      c = get_symbol_name (regname);
    }
  
  return c;
}

static void validate_special_register_name(const char *name)
{
  if (strcmp (name, "scratch") && strcmp (name, "ignore"))
    report_register_syntax_error();
}

static void process_global_register(int reg, char *regname)
{
  if (globals[reg])
    {
      validate_global_redefinition(reg, regname);
    }
  else
    {
      create_global_register(reg, regname);
    }
}

static void validate_global_redefinition(int reg, char *regname)
{
  int name_mismatch = regname && globals[reg] != (symbolS *) 1
                       && strcmp (S_GET_NAME (globals[reg]), regname);
  int type_mismatch = (regname != NULL) ^ (globals[reg] != (symbolS *) 1);
  
  if (name_mismatch || type_mismatch)
    as_bad (_("redefinition of global register"));
}

static void create_global_register(int reg, char *regname)
{
  if (regname == NULL)
    {
      globals[reg] = (symbolS *) 1;
    }
  else
    {
      create_register_symbol(reg, regname);
    }
}

static void create_register_symbol(int reg, char *regname)
{
  if (*regname && symbol_find (regname))
    {
      as_bad (_("Register symbol %s already defined."), regname);
      return;
    }

  globals[reg] = symbol_make (regname);
  setup_register_symbol_flags(reg, regname);
  setup_register_symbol_properties(reg);
}

static void setup_register_symbol_flags(int reg, char *regname)
{
  int flags = symbol_get_bfdsym (globals[reg])->flags;
  
  if (! *regname)
    flags = flags & ~(BSF_GLOBAL|BSF_LOCAL|BSF_WEAK);
  if (! (flags & (BSF_GLOBAL|BSF_LOCAL|BSF_WEAK)))
    flags |= BSF_GLOBAL;
    
  symbol_get_bfdsym (globals[reg])->flags = flags;
}

static void setup_register_symbol_properties(int reg)
{
  S_SET_VALUE (globals[reg], reg);
  S_SET_ALIGN (globals[reg], reg);
  S_SET_SIZE (globals[reg], 0);
  S_SET_SEGMENT (globals[reg], absolute_section);
  S_SET_OTHER (globals[reg], 0);
  
  elf_symbol (symbol_get_bfdsym (globals[reg]))->internal_elf_sym.st_info =
    ELF_ST_INFO(STB_GLOBAL, STT_REGISTER);
  elf_symbol (symbol_get_bfdsym (globals[reg]))->internal_elf_sym.st_shndx = SHN_UNDEF;
}

/* Adjust the symbol table.  We set undefined sections for STT_REGISTER
   symbols which need it.  */

void
sparc_adjust_symtab (void)
{
  symbolS *sym;

  for (sym = symbol_rootP; sym != NULL; sym = symbol_next (sym))
    {
      asymbol *bfdsym = symbol_get_bfdsym (sym);
      if (bfdsym == NULL)
        continue;

      elf_symbol_type *elfsym = elf_symbol (bfdsym);
      if (elfsym == NULL)
        continue;

      if (ELF_ST_TYPE (elfsym->internal_elf_sym.st_info) != STT_REGISTER)
        continue;

      if (elfsym->internal_elf_sym.st_shndx != SHN_UNDEF)
        continue;

      S_SET_SEGMENT (sym, undefined_section);
    }
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

void sparc_cons_align(int nbytes)
{
    int nalign;
    
    if (!enforce_aligned_data || sparc_no_align_cons)
        return;
    
    nalign = mylog2(nbytes);
    if (nalign <= 0)
        return;
    
    if (now_seg == absolute_section)
    {
        int alignment_mask = (1 << nalign) - 1;
        if ((abs_section_offset & alignment_mask) != 0)
            as_bad(_("misaligned data"));
        return;
    }
    
    frag_var(rs_align_test, 1, 1, 0, NULL, nalign, NULL);
    record_alignment(now_seg, nalign);
}

/* This is called from HANDLE_ALIGN in tc-sparc.h.  */

void
sparc_handle_align (fragS *fragp)
{
  int count;
  char *p;

  if (!fragp || !fragp->fr_next)
    return;

  count = fragp->fr_next->fr_address - fragp->fr_address - fragp->fr_fix;

  switch (fragp->fr_type)
    {
    case rs_align_test:
      if (count != 0)
        as_bad_where (fragp->fr_file, fragp->fr_line, _("misaligned data"));
      break;

    case rs_align_code:
      sparc_handle_align_code(fragp, count);
      break;

    default:
      break;
    }
}

static void
sparc_handle_align_code (fragS *fragp, int count)
{
  char *p;
  int fix = 0;

  p = fragp->fr_literal + fragp->fr_fix;

  fix = sparc_align_unaligned_bytes(p, &count);
  p += fix;

  if (SPARC_OPCODE_ARCH_V9_P (max_architecture) && count > 8)
    {
      sparc_emit_branch_instruction(p, count);
      p += 4;
      count -= 4;
      fix += 4;
    }

  sparc_emit_nop_instruction(p);

  fragp->fr_fix += fix;
  fragp->fr_var = 4;
}

static int
sparc_align_unaligned_bytes (char *p, int *count)
{
  int unaligned_bytes = *count & 3;
  
  if (unaligned_bytes == 0)
    return 0;

  memset (p, 0, unaligned_bytes);
  *count -= unaligned_bytes;
  
  return unaligned_bytes;
}

static void
sparc_emit_branch_instruction (char *p, int count)
{
  unsigned wval = 0x30680000 | (count >> 2);
  
  if (INSN_BIG_ENDIAN)
    number_to_chars_bigendian (p, wval, 4);
  else
    number_to_chars_littleendian (p, wval, 4);
}

static void
sparc_emit_nop_instruction (char *p)
{
  if (INSN_BIG_ENDIAN)
    number_to_chars_bigendian (p, 0x01000000, 4);
  else
    number_to_chars_littleendian (p, 0x01000000, 4);
}

/* Some special processing for a Sparc ELF file.  */

void sparc_elf_final_processing(void)
{
    Elf_Internal_Ehdr *ehdr = elf_elfheader(stdoutput);
    
    if (ehdr == NULL) {
        return;
    }
    
    if (sparc_arch_size == 64) {
        if (sparc_memory_model == MM_RMO) {
            ehdr->e_flags |= EF_SPARCV9_RMO;
        } else if (sparc_memory_model == MM_PSO) {
            ehdr->e_flags |= EF_SPARCV9_PSO;
        }
    } else if (current_architecture >= SPARC_OPCODE_ARCH_V9) {
        ehdr->e_flags |= EF_SPARC_32PLUS;
    }
    
    if (current_architecture == SPARC_OPCODE_ARCH_V9A) {
        ehdr->e_flags |= EF_SPARC_SUN_US1;
    } else if (current_architecture == SPARC_OPCODE_ARCH_V9B) {
        ehdr->e_flags |= EF_SPARC_SUN_US1 | EF_SPARC_SUN_US3;
    }
}

const char *
sparc_cons (expressionS *exp, int size)
{
  char *save;
  const char *sparc_cons_special_reloc = NULL;

  SKIP_WHITESPACE ();
  save = input_line_pointer;
  
  if (input_line_pointer[0] != '%' || 
      input_line_pointer[1] != 'r' || 
      input_line_pointer[2] != '_')
    {
      expression (exp);
      return NULL;
    }

  if (startswith (input_line_pointer + 3, "disp"))
    {
      input_line_pointer += 7;
      sparc_cons_special_reloc = "disp";
    }
  else if (startswith (input_line_pointer + 3, "plt"))
    {
      if (size != 4 && size != 8)
        {
          as_bad (_("Illegal operands: %%r_plt in %d-byte data field"), size);
          expression (exp);
          return NULL;
        }
      input_line_pointer += 6;
      sparc_cons_special_reloc = "plt";
    }
  else if (startswith (input_line_pointer + 3, "tls_dtpoff"))
    {
      if (size != 4 && size != 8)
        {
          as_bad (_("Illegal operands: %%r_tls_dtpoff in %d-byte data field"), size);
          expression (exp);
          return NULL;
        }
      input_line_pointer += 13;
      sparc_cons_special_reloc = "tls_dtpoff";
    }
  else
    {
      expression (exp);
      return NULL;
    }

  int expected_bits = size * 8;
  int valid = 0;
  
  if (size == 1 && *input_line_pointer == '8')
    {
      valid = 1;
      input_line_pointer--;
    }
  else if (size == 2 && input_line_pointer[0] == '1' && input_line_pointer[1] == '6')
    {
      valid = 1;
    }
  else if (size == 4 && input_line_pointer[0] == '3' && input_line_pointer[1] == '2')
    {
      valid = 1;
    }
  else if (size == 8 && input_line_pointer[0] == '6' && input_line_pointer[1] == '4')
    {
      valid = 1;
    }

  if (!valid)
    {
      as_bad (_("Illegal operands: Only %%r_%s%d allowed in %d-byte data fields"),
              sparc_cons_special_reloc, expected_bits, size);
      input_line_pointer = save;
      expression (exp);
      return NULL;
    }

  input_line_pointer += 2;
  
  if (*input_line_pointer != '(')
    {
      as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
              sparc_cons_special_reloc, expected_bits);
      input_line_pointer = save;
      expression (exp);
      return NULL;
    }

  char *end = ++input_line_pointer;
  int npar = 0;
  int c;

  while (!is_end_of_stmt (c = *end))
    {
      if (c == '(')
        npar++;
      else if (c == ')')
        {
          if (!npar)
            break;
          npar--;
        }
      end++;
    }

  if (c != ')')
    {
      as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
              sparc_cons_special_reloc, expected_bits);
      input_line_pointer = save;
      expression (exp);
      return NULL;
    }

  *end = '\0';
  expression (exp);
  *end = ')';
  
  if (input_line_pointer != end)
    {
      as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
              sparc_cons_special_reloc, expected_bits);
      input_line_pointer = save;
      expression (exp);
      return NULL;
    }

  input_line_pointer++;
  SKIP_WHITESPACE ();
  c = *input_line_pointer;
  
  if (!is_end_of_stmt (c) && c != ',')
    {
      as_bad (_("Illegal operands: garbage after %%r_%s%d()"),
              sparc_cons_special_reloc, expected_bits);
    }

  return sparc_cons_special_reloc;
}

/* This is called by emit_expr via TC_CONS_FIX_NEW when creating a
   reloc for a cons.  We could use the definition there, except that
   we want to handle little endian relocs specially.  */

void
cons_fix_new_sparc (fragS *frag,
		    int where,
		    unsigned int nbytes,
		    expressionS *exp,
		    const char *sparc_cons_special_reloc)
{
  bfd_reloc_code_real_type r;

  r = get_default_reloc(nbytes);

  if (target_little_endian_data
      && nbytes == 4
      && now_seg->flags & SEC_ALLOC)
    r = BFD_RELOC_SPARC_REV32;

#ifdef TE_SOLARIS
  if (!target_little_endian_data
      && sparc_arch_size != 64
      && r == BFD_RELOC_64)
    r = BFD_RELOC_32;
#endif

  if (sparc_cons_special_reloc)
    {
      r = get_special_reloc(sparc_cons_special_reloc, nbytes);
    }
  else if (sparc_no_align_cons
	   || (now_seg->name && strcmp (now_seg->name, ".eh_frame") == 0))
    {
      r = get_unaligned_reloc(nbytes);
   }

  fix_new_exp (frag, where, nbytes, exp, 0, r);
}

static bfd_reloc_code_real_type
get_default_reloc(unsigned int nbytes)
{
  switch (nbytes)
    {
    case 1: return BFD_RELOC_8;
    case 2: return BFD_RELOC_16;
    case 4: return BFD_RELOC_32;
    case 8: return BFD_RELOC_64;
    default: abort();
    }
}

static bfd_reloc_code_real_type
get_special_reloc(const char *special_reloc, unsigned int nbytes)
{
  if (!special_reloc)
    abort();

  if (*special_reloc == 'd')
    {
      switch (nbytes)
        {
        case 1: return BFD_RELOC_8_PCREL;
        case 2: return BFD_RELOC_16_PCREL;
        case 4: return BFD_RELOC_32_PCREL;
        case 8: return BFD_RELOC_64_PCREL;
        default: abort();
        }
    }
  else if (*special_reloc == 'p')
    {
      switch (nbytes)
        {
        case 4: return BFD_RELOC_SPARC_PLT32;
        case 8: return BFD_RELOC_SPARC_PLT64;
        default: return get_default_reloc(nbytes);
        }
    }
  else
    {
      switch (nbytes)
        {
        case 4: return BFD_RELOC_SPARC_TLS_DTPOFF32;
        case 8: return BFD_RELOC_SPARC_TLS_DTPOFF64;
        default: return get_default_reloc(nbytes);
        }
    }
}

static bfd_reloc_code_real_type
get_unaligned_reloc(unsigned int nbytes)
{
  switch (nbytes)
    {
    case 2: return BFD_RELOC_SPARC_UA16;
    case 4: return BFD_RELOC_SPARC_UA32;
    case 8:
#ifdef TE_SOLARIS
      return sparc_arch_size == 64 ? BFD_RELOC_SPARC_UA64 : BFD_RELOC_SPARC_UA32;
#else
      return BFD_RELOC_SPARC_UA64;
#endif
    default: abort();
    }
}

void sparc_cfi_frame_initial_instructions(void)
{
    const int offset = (sparc_arch_size == 64) ? 0x7ff : 0;
    cfi_add_CFA_def_cfa(14, offset);
}

int
sparc_regname_to_dw2regnum (char *regname)
{
  if (!regname || !regname[0])
    return -1;

  if (!regname[2]) {
    if (regname[0] == 's' && regname[1] == 'p')
      return 14;
    if (regname[0] == 'f' && regname[1] == 'p')
      return 30;
  }

  int base_offset = -1;
  switch (regname[0]) {
    case 'g': base_offset = 0; break;
    case 'o': base_offset = 8; break;
    case 'l': base_offset = 16; break;
    case 'i': base_offset = 24; break;
  }

  if (base_offset != -1) {
    if (regname[1] < '0' || regname[1] > '7' || regname[2])
      return -1;
    return base_offset + (regname[1] - '0');
  }

  if (regname[0] != 'f' && regname[0] != 'r')
    return -1;

  char *endptr;
  unsigned long regnum = strtoul(regname + 1, &endptr, 10);
  
  if (endptr == regname + 1 || *endptr)
    return -1;

  if (regname[0] == 'f') {
    unsigned int max_reg = SPARC_OPCODE_ARCH_V9_P(max_architecture) ? 64 : 32;
    if (regnum >= max_reg)
      return -1;
    regnum += 32;
    if (regnum >= 64 && (regnum & 1))
      return -1;
  } else {
    if (regnum >= 32)
      return -1;
  }

  return regnum;
}

void sparc_cfi_emit_pcrel_expr(expressionS *exp, unsigned int nbytes)
{
    if (exp == NULL) {
        return;
    }
    
    sparc_no_align_cons = 1;
    emit_expr_with_reloc(exp, nbytes, "disp");
    sparc_no_align_cons = 0;
}

