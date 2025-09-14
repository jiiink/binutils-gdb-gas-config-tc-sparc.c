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
  if (name == NULL) {
    return NULL;
  }

  struct sparc_arch *sa;

  for (sa = &sparc_arch_table[0]; sa->name != NULL; sa++) {
    if (strcmp (sa->name, name) == 0) {
      return sa;
    }
  }

  return NULL;
}

/* Initialize the default opcode arch and word size from the default
   architecture name.  */

static void
init_default_arch (void)
{
  struct sparc_arch *sa = lookup_arch (default_arch);

  if (sa == NULL || sa->default_arch_size == 0)
    as_fatal (_("Invalid default architecture, broken assembler."));

  max_architecture = sparc_opcode_lookup_arch (sa->opcode_arch);
  if (max_architecture == SPARC_OPCODE_ARCH_BAD)
    as_fatal (_("Bad opcode table, broken assembler."));
  default_arch_size = sparc_arch_size = sa->default_arch_size;
  default_init_p = 1;
  default_arch_type = sa->arch_type;
}

/* Called by TARGET_MACH.  */

#include <pthread.h>

static pthread_mutex_t sparc_init_mutex = PTHREAD_MUTEX_INITIALIZER;

unsigned long
sparc_mach (void)
{
  pthread_mutex_lock(&sparc_init_mutex);

  if (!default_init_p)
    {
      init_default_arch();
    }

  pthread_mutex_unlock(&sparc_init_mutex);

  return sparc_arch_size == 64 ? bfd_mach_sparc_v9 : bfd_mach_sparc;
}

/* Called by TARGET_FORMAT.  */

const char *
sparc_target_format (void)
{
  if (!default_init_p) {
    init_default_arch();
  }

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

static int
handle_architecture_option_logic (int c, const char *arg)
{
  struct sparc_arch *sa;
  enum sparc_opcode_arch_val opcode_arch;
  uint32_t opcode_hwcaps_low, opcode_hwcaps_high;
  uint32_t arch_hwcaps_low, arch_hwcaps_high;
  uint64_t combined_hwcaps_low, combined_hwcaps_high_shifted;

  sa = lookup_arch (arg);
  if (sa == NULL || !sa->user_option_p)
    {
      if (c == OPTION_XARCH)
	as_bad (_("invalid architecture -xarch=%s"), arg);
      else
	as_bad (_("invalid architecture -A%s"), arg);
      return 0;
    }

  opcode_arch = sparc_opcode_lookup_arch (sa->opcode_arch);
  if (opcode_arch == SPARC_OPCODE_ARCH_BAD)
    as_fatal (_("Bad opcode table, broken assembler."));

  if (!architecture_requested || opcode_arch > max_architecture)
    max_architecture = opcode_arch;

  opcode_hwcaps_low = sparc_opcode_archs[opcode_arch].hwcaps;
  opcode_hwcaps_high = sparc_opcode_archs[opcode_arch].hwcaps2;
  arch_hwcaps_low = sa->hwcap_allowed;
  arch_hwcaps_high = sa->hwcap2_allowed;

  combined_hwcaps_low = (uint64_t)opcode_hwcaps_low | arch_hwcaps_low;
  combined_hwcaps_high_shifted = ((uint64_t)opcode_hwcaps_high | arch_hwcaps_high) << 32;

  hwcap_allowed = hwcap_allowed | combined_hwcaps_high_shifted | combined_hwcaps_low;
  architecture_requested = 1;
  return 1;
}

int
md_parse_option (int c, const char *arg)
{
  if (! default_init_p)
    init_default_arch ();

  switch (c)
    {
    case OPTION_BUMP:
      warn_on_bump = 1;
      warn_after_architecture = SPARC_OPCODE_ARCH_V6;
      break;

    case OPTION_XARCH:
      if (startswith (arg, "v9"))
	md_parse_option (OPTION_64, NULL);
      else if (startswith (arg, "v8")
	      || startswith (arg, "v7")
	      || startswith (arg, "v6")
	      || !strcmp (arg, "sparclet")
	      || !strcmp (arg, "sparclite")
	      || !strcmp (arg, "sparc86x"))
	md_parse_option (OPTION_32, NULL);

      return handle_architecture_option_logic (c, arg);

    case 'A':
      return handle_architecture_option_logic (c, arg);

    case OPTION_SPARC:
      break;

    case OPTION_ENFORCE_ALIGNED_DATA:
      enforce_aligned_data = 1;
      break;

#ifdef SPARC_BIENDIAN
    case OPTION_LITTLE_ENDIAN:
      target_big_endian = 0;
      if (default_arch_type != sparclet)
	as_fatal ("This target does not support -EL");
      break;
    case OPTION_LITTLE_ENDIAN_DATA:
      target_little_endian_data = 1;
      target_big_endian = 0;
      if (default_arch_type != sparc86x
	  && default_arch_type != v9)
	as_fatal ("This target does not support --little-endian-data");
      break;
    case OPTION_BIG_ENDIAN:
      target_big_endian = 1;
      break;
#endif

    case OPTION_32:
    case OPTION_64:
      {
	const char **list;
	const char *target_prefix;

	sparc_arch_size = c == OPTION_32 ? 32 : 64;
	target_prefix = (sparc_arch_size == 32) ? "elf32-sparc" : "elf64-sparc";

	list = bfd_target_list ();
	for (const char **l = list; *l != NULL; l++)
	  {
	    if (startswith (*l, target_prefix))
	      {
		target_prefix = NULL;
		break;
	      }
	  }

	if (target_prefix != NULL)
	  as_fatal (_("No compiled in support for %d bit object file format"),
		    sparc_arch_size);
	free (list);

	if (sparc_arch_size == 64
	    && max_architecture < SPARC_OPCODE_ARCH_V9)
	  max_architecture = SPARC_OPCODE_ARCH_V9;
      }
      break;

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
      break;

    case 's':
      break;

    case 'q':
      break;

    case 'K':
      if (strcmp (arg, "PIC") != 0)
	as_warn (_("Unrecognized option following -K"));
      else
	sparc_pic_code = 1;
      break;

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

#include <stdio.h>
#include <string.h>
#include <stdbool.h>

// Assuming the following are declared/defined elsewhere as global or extern:
// extern bool default_init_p;
// extern void init_default_arch(void);
// extern const struct sparc_arch sparc_arch_table[];
// extern int default_arch_size;
// extern const char *_(const char *msgid); // For gettext localization

// Definition of struct sparc_arch, minimal for this function's usage
struct sparc_arch {
    const char *name;
    bool user_option_p;
    // ... other members not used in this function
};

// --- Constants for display formatting ---
#define DISPLAY_LINE_WIDTH 78 // Standard terminal width, provides good readability
#define OPTION_SEPARATOR " | "
#define OPTION_SEPARATOR_LEN (sizeof(OPTION_SEPARATOR) - 1) // Length of " | "

// Helper function to print an option with a prefix/suffix and manage column wrapping.
// Returns the updated column position.
// 'is_first_option_on_line' tracks if this is the very first option being printed
// on the current logical line of options.
static int
print_wrapped_option(FILE *stream, int current_column, const char *prefix, const char *option_name, const char *suffix, bool *is_first_option_on_line)
{
  size_t prefix_len = strlen(prefix);
  size_t option_name_len = strlen(option_name);
  size_t suffix_len = strlen(suffix);
  size_t option_full_len = prefix_len + option_name_len + suffix_len;
  size_t effective_len;

  // Calculate the total length this option will occupy, including the separator if needed.
  if (!*is_first_option_on_line) {
    effective_len = OPTION_SEPARATOR_LEN + option_full_len;
  } else {
    effective_len = option_full_len;
  }

  // If the current line is not empty and adding this option would exceed the display width,
  // print a newline and reset the column.
  if (current_column > 0 && current_column + effective_len > DISPLAY_LINE_WIDTH) {
    fputc('\n', stream);
    current_column = 0;
    *is_first_option_on_line = true; // Mark as first on the new line
  }

  // If this is not the first option on the *current* line segment, print the separator.
  if (!*is_first_option_on_line) {
    fprintf(stream, OPTION_SEPARATOR);
    current_column += OPTION_SEPARATOR_LEN;
  }

  // Print the option itself.
  fprintf(stream, "%s%s%s", prefix, option_name, suffix);
  current_column += option_full_len;
  *is_first_option_on_line = false; // Mark that an option has now been printed on this line segment.

  return current_column;
}


void
md_show_usage (FILE *stream)
{
  const struct sparc_arch *arch;
  int current_column;
  bool first_option_on_line; // Tracks if no options have been printed yet on the current logical line segment

  // Ensure default architecture settings are initialized before use.
  if (!default_init_p) {
    init_default_arch();
  }

  fprintf(stream, _("SPARC options:\n"));
  current_column = 0;
  first_option_on_line = true; // Start fresh for the first group of options

  // Print -A<arch> options
  for (arch = &sparc_arch_table[0]; arch->name; arch++) {
    if (!arch->user_option_p) {
	    continue;
    }
    current_column = print_wrapped_option(stream, current_column, "-A", arch->name, "", &first_option_on_line);
  }
  
  // Ensure a new line before the next distinct block of options, if the previous line wasn't empty.
  if (current_column > 0) {
      fputc('\n', stream);
  }
  current_column = 0; // Reset column for the new block of options
  first_option_on_line = true; // Reset for the new block of options

  // Print -xarch=<arch> options
  for (arch = &sparc_arch_table[0]; arch->name; arch++) {
    if (!arch->user_option_p) {
	    continue;
    }
    current_column = print_wrapped_option(stream, current_column, "-xarch=", arch->name, "", &first_option_on_line);
  }

  // Ensure a new line after the last block of options, if the final option didn't cause a wrap.
  if (current_column > 0) {
      fputc('\n', stream);
  }

  // Print static usage messages
  fprintf(stream, _("\
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
  fprintf(stream, _("\
			[default is %s]\n"), (default_arch_size == 64) ? "RMO" : "TSO");
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

  if (p->name == NULL) {
    if (q->name == NULL) {
      return 0;
    } else {
      return 1;
    }
  } else if (q->name == NULL) {
    return -1;
  } else {
    return strcmp(q->name, p->name);
  }
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

  const char *p_name = p->name;
  const char *q_name = q->name;

  if (p_name == NULL) {
    return (q_name == NULL) ? 0 : 1;
  }

  if (q_name == NULL) {
    return -1;
  }

  return strcmp (q_name, p_name);
}

/* This function is called once, at assembler startup time.  It should
   set up all the tables, etc. that the MD part of the assembler will
   need.  */

void
md_begin (void)
{
  int error_encountered = 0;
  unsigned int i = 0;

  if (!default_init_p)
    init_default_arch();

  sparc_cie_data_alignment = (sparc_arch_size == 64) ? -8 : -4;

  op_hash = str_htab_create();

  while (i < (unsigned int)sparc_num_opcodes)
    {
      const char *current_opcode_name = sparc_opcodes[i].name;
      if (str_hash_insert(op_hash, current_opcode_name, &sparc_opcodes[i], 0) != NULL)
	{
	  as_bad(_("duplicate %s"), current_opcode_name);
	  error_encountered = 1;
	}
      do
	{
	  if ((sparc_opcodes[i].match & sparc_opcodes[i].lose) != 0)
	    {
	      as_bad(_("Internal error: losing opcode: `%s' \"%s\"\n"),
		      sparc_opcodes[i].name, sparc_opcodes[i].args);
	      error_encountered = 1;
	    }
	  ++i;
	}
      while (i < (unsigned int)sparc_num_opcodes
	     && !strcmp(sparc_opcodes[i].name, current_opcode_name));
    }

  for (i = 0; native_op_table[i].name; i++)
    {
      const struct sparc_opcode *found_insn;
      const char *alias_name = ((sparc_arch_size == 32)
			  ? native_op_table[i].name32
			  : native_op_table[i].name64);
      found_insn = str_hash_find(op_hash, alias_name);
      if (found_insn == NULL)
	{
	  as_bad(_("Internal error: can't find opcode `%s' for `%s'\n"),
		  alias_name, native_op_table[i].name);
	  error_encountered = 1;
	}
      else if (str_hash_insert(op_hash, native_op_table[i].name, found_insn, 0) != NULL)
	{
	  as_bad(_("duplicate %s"), native_op_table[i].name);
	  error_encountered = 1;
	}
    }

  if (error_encountered)
    as_fatal(_("Broken assembler. No assembly attempted."));

  qsort(priv_reg_table, sizeof(priv_reg_table) / sizeof(priv_reg_table[0]),
	 sizeof(priv_reg_table[0]), cmp_reg_entry);
  qsort(hpriv_reg_table, sizeof(hpriv_reg_table) / sizeof(hpriv_reg_table[0]),
	 sizeof(hpriv_reg_table[0]), cmp_reg_entry);
  qsort(v9a_asr_table, sizeof(v9a_asr_table) / sizeof(v9a_asr_table[0]),
	 sizeof(v9a_asr_table[0]), cmp_reg_entry);
  
  {
    if (warn_on_bump
        && architecture_requested)
      {
        warn_after_architecture = max_architecture;
      }

    if (warn_on_bump
        || !architecture_requested)
    {
      enum sparc_opcode_arch_val initial_max_architecture = max_architecture;

      max_architecture = SPARC_OPCODE_ARCH_MAX;
      while (max_architecture > warn_after_architecture)
        {
          if (! SPARC_OPCODE_CONFLICT_P(max_architecture,
                                       initial_max_architecture))
            break;
          --max_architecture;
        }
    }
  }

  {
    struct priv_reg_entry *reg_tables[]
      = {priv_reg_table, hpriv_reg_table, v9a_asr_table, NULL};
    struct priv_reg_entry **table_ptr;
    struct perc_entry *current_perc_entry;
    int entry_idx = 0;

    for (table_ptr = reg_tables; *table_ptr != NULL; ++table_ptr)
      {
        for (struct priv_reg_entry *reg = *table_ptr; reg->name != NULL; ++reg)
          {
            current_perc_entry = &perc_table[entry_idx++];
            current_perc_entry->type = perc_entry_reg;
            current_perc_entry->name = reg->name;
            current_perc_entry->len = strlen(reg->name);
            current_perc_entry->reg = reg;
          }
      }

    for (i = 0; i < (sizeof(pop_table) / sizeof(pop_table[0])); i++)
      {
	current_perc_entry = &perc_table[entry_idx++];
	current_perc_entry->type = (pop_table[i].flags & F_POP_POSTFIX)
		   ? perc_entry_post_pop : perc_entry_imm_pop;
	current_perc_entry->name = pop_table[i].name;
	current_perc_entry->len = strlen(pop_table[i].name);
	current_perc_entry->pop = &pop_table[i];
      }

    perc_table[entry_idx].type = perc_entry_none;

    qsort(perc_table, sizeof(perc_table) / sizeof(perc_table[0]),
          sizeof(perc_table[0]), cmp_perc_entry);
  }
}

/* Called after all assembly has been done.  */

static unsigned long
get_sparc_bfd_mach_type(int current_arch, int is_64_bit_arch)
{
  unsigned long mach_type_val;

  if (is_64_bit_arch)
    {
      switch (current_arch)
        {
        case SPARC_OPCODE_ARCH_V9A: mach_type_val = bfd_mach_sparc_v9a; break;
        case SPARC_OPCODE_ARCH_V9B: mach_type_val = bfd_mach_sparc_v9b; break;
        case SPARC_OPCODE_ARCH_V9C: mach_type_val = bfd_mach_sparc_v9c; break;
        case SPARC_OPCODE_ARCH_V9D: mach_type_val = bfd_mach_sparc_v9d; break;
        case SPARC_OPCODE_ARCH_V9E: mach_type_val = bfd_mach_sparc_v9e; break;
        case SPARC_OPCODE_ARCH_V9V: mach_type_val = bfd_mach_sparc_v9v; break;
        case SPARC_OPCODE_ARCH_V9M: mach_type_val = bfd_mach_sparc_v9m; break;
        case SPARC_OPCODE_ARCH_M8:  mach_type_val = bfd_mach_sparc_v9m8; break;
        default: mach_type_val = bfd_mach_sparc_v9; break;
        }
    }
  else
    {
      switch (current_arch)
        {
        case SPARC_OPCODE_ARCH_SPARCLET: mach_type_val = bfd_mach_sparc_sparclet; break;
        case SPARC_OPCODE_ARCH_V9: mach_type_val = bfd_mach_sparc_v8plus; break;
        case SPARC_OPCODE_ARCH_V9A: mach_type_val = bfd_mach_sparc_v8plusa; break;
        case SPARC_OPCODE_ARCH_V9B: mach_type_val = bfd_mach_sparc_v8plusb; break;
        case SPARC_OPCODE_ARCH_V9C: mach_type_val = bfd_mach_sparc_v8plusc; break;
        case SPARC_OPCODE_ARCH_V9D: mach_type_val = bfd_mach_sparc_v8plusd; break;
        case SPARC_OPCODE_ARCH_V9E: mach_type_val = bfd_mach_sparc_v8pluse; break;
        case SPARC_OPCODE_ARCH_V9V: mach_type_val = bfd_mach_sparc_v8plusv; break;
        case SPARC_OPCODE_ARCH_V9M: mach_type_val = bfd_mach_sparc_v8plusm; break;
        case SPARC_OPCODE_ARCH_M8:  mach_type_val = bfd_mach_sparc_v8plusm8; break;
        default: mach_type_val = bfd_mach_sparc; break;
        }
    }
  return mach_type_val;
}

void
sparc_md_finish (void)
{
  unsigned long mach;

  mach = get_sparc_bfd_mach_type(current_architecture, sparc_arch_size == 64);
  bfd_set_arch_mach (stdoutput, bfd_arch_sparc, mach);

#ifndef TE_SOLARIS
  int hwcaps = (int)(hwcap_seen & 0xFFFFFFFFUL);
  int hwcaps2 = (int)(hwcap_seen >> 32);

  if ((hwcaps != 0
       && !bfd_elf_add_obj_attr_int (stdoutput, OBJ_ATTR_GNU,
				     Tag_GNU_Sparc_HWCAPS, hwcaps))
      || (hwcaps2 != 0
	  && !bfd_elf_add_obj_attr_int (stdoutput, OBJ_ATTR_GNU,
					Tag_GNU_Sparc_HWCAPS2, hwcaps2)))
    {
      as_fatal (_("error adding attribute: %s"),
                bfd_errmsg (bfd_get_error ()));
    }
#endif
}

/* Return non-zero if VAL is in the range -(MAX+1) to MAX.  */

static inline int
in_signed_range (bfd_signed_vma val, bfd_signed_vma max)
{
  if (max <= 0)
    abort ();

  if (sparc_arch_size == 32)
    {
      bfd_vma lower_32_bits = (bfd_vma)val & 0xFFFFFFFFU;
      bfd_vma sign_bit_32 = (bfd_vma)1 << 31;

      if (lower_32_bits & sign_bit_32)
        {
          val = (bfd_signed_vma) (lower_32_bits | ~0xFFFFFFFFU);
        }
      else
        {
          val = (bfd_signed_vma) lower_32_bits;
        }
    }

  if (val > max)
    return 0;
  if (val < -max)
    return 0;

  return 1;
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

  const bfd_signed_vma min_val_for_this_range = -((max >> 1) + 1);

  return (val <= max && val >= min_val_for_this_range);
}

static int
sparc_ffs (unsigned int mask)
{
  if (mask == 0)
    return -1;

  return __builtin_ctz(mask);
}

/* Implement big shift right.  */
static bfd_vma
BSR (bfd_vma val, int amount)
{
  const int vma_bits = (int)sizeof(bfd_vma) * CHAR_BIT;

  if (amount < 0 || amount >= vma_bits)
    {
      as_fatal (_("Invalid shift amount for bfd_vma."));
    }

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
  /* Constants for immediate values and masks */
  const int SETHI_SHIFT_AMOUNT = 10;
  const unsigned int SETHI_IMMEDIATE_MASK = 0x3fffffU; /* 22 bits */
  const unsigned int OR_LO10_MASK = 0x3ffU;   /* 10 bits for OR immediate if SETHI was used */
  const unsigned int OR_LO13_MASK = 0x1fffU;  /* 13 bits for OR immediate if no SETHI */
  const offsetT LO12_RANGE_MAX = (offsetT)(1 << 12); /* 4096 */
  const offsetT LO12_RANGE_MIN = -(offsetT)(1 << 12); /* -4096 */

  /* Warning range constants for 32-bit values */
  const offsetT SPARC_V9_MIN_IMM_WARN = 0;
  const offsetT SPARC_V9_MAX_IMM_WARN = (offsetT)0xFFFFFFFFU; /* Max unsigned 32-bit */
  const offsetT SPARC_V8_MIN_IMM_WARN_NEG = -(offsetT)2147483648LL; /* Min signed 32-bit */
  const offsetT SPARC_V8_MAX_IMM_WARN = (offsetT)0xFFFFFFFFU; /* Max unsigned 32-bit */

  int rd = (the_insn.opcode & RD (~0)) >> 25;

  /* Handle constant value range checks and potential truncation. */
  if (the_insn.exp.X_op == O_constant)
    {
      if (SPARC_OPCODE_ARCH_V9_P (max_architecture))
	{
	  /* V9: immediate must be in 0..4294967295 range (unsigned 32-bit). */
	  if (sizeof (offsetT) > 4
	      && (the_insn.exp.X_add_number < SPARC_V9_MIN_IMM_WARN
		  || the_insn.exp.X_add_number > SPARC_V9_MAX_IMM_WARN))
	    as_warn (_("set: number not in 0..4294967295 range"));
	}
      else /* SPARC V8 or earlier architectures */
	{
	  /* V8: immediate must be in -2147483648..4294967295 range (signed 32-bit min to unsigned 32-bit max). */
	  if (sizeof (offsetT) > 4
	      && (the_insn.exp.X_add_number < SPARC_V8_MIN_IMM_WARN_NEG
		  || the_insn.exp.X_add_number > SPARC_V8_MAX_IMM_WARN))
	    as_warn (_("set: number not in -2147483648..4294967295 range"));

	  /* Critical functional behavior: truncate to int32_t for V8 processing. */
	  the_insn.exp.X_add_number = (int32_t) the_insn.exp.X_add_number;
	}
    }

  /* Determine if a SETHI instruction is required.
     It's needed if the operand is not a constant,
     or if the constant value is outside the 12-bit signed immediate range. */
  int need_sethi = (the_insn.exp.X_op != O_constant
		    || the_insn.exp.X_add_number >= LO12_RANGE_MAX
		    || the_insn.exp.X_add_number < LO12_RANGE_MIN);

  if (need_sethi)
    {
      unsigned int sethi_immediate_value = 0;
      if (the_insn.exp.X_op == O_constant)
	{
	  /* For constants, extract the upper 22 bits (after shifting right by 10). */
	  sethi_immediate_value = (the_insn.exp.X_add_number >> SETHI_SHIFT_AMOUNT) & SETHI_IMMEDIATE_MASK;
	}
      /* If not a constant, sethi_immediate_value remains 0 and relocation handles the value. */

      the_insn.opcode = SETHI_INSN | RD (rd) | sethi_immediate_value;
      the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_HI22 : BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

  /* Determine if an OR instruction is required.
     An OR instruction is not needed only if:
     1. The operand IS a constant.
     2. A SETHI instruction WAS generated (`need_sethi` is true).
     3. The low 10 bits of the constant ARE zero.
     In all other cases, an OR instruction is generated. */
  int generate_or_insn = 0;
  if (the_insn.exp.X_op != O_constant)
    {
      generate_or_insn = 1; /* Relocation needed for OR. */
    }
  else if (!need_sethi) /* Is constant, and no SETHI was needed. */
    {
      generate_or_insn = 1; /* OR handles the full 12-bit value. */
    }
  else /* Is constant, and SETHI was needed. */
    {
      /* Check if low 10 bits are non-zero. */
      if ((the_insn.exp.X_add_number & OR_LO10_MASK) != 0)
	{
	  generate_or_insn = 1; /* OR handles the remaining low 10 bits. */
	}
    }

  if (generate_or_insn)
    {
      unsigned int or_immediate_value = 0;
      unsigned int or_immediate_mask_for_constant = 0;

      if (the_insn.exp.X_op != O_constant)
	{
	  or_immediate_mask_for_constant = 0; /* Relocation will fill this part. */
	}
      else if (need_sethi)
	{
	  or_immediate_mask_for_constant = OR_LO10_MASK; /* Extract low 10 bits. */
	}
      else /* Constant, and no SETHI needed. */
	{
	  or_immediate_mask_for_constant = OR_LO13_MASK; /* Extract all 13 bits for immediate. */
	}
      or_immediate_value = the_insn.exp.X_add_number & or_immediate_mask_for_constant;

      the_insn.opcode = (OR_INSN | (need_sethi ? RS1 (rd) : 0)
			 | RD (rd) | IMMED | or_immediate_value);
      the_insn.reloc = (the_insn.exp.X_op != O_constant) ? BFD_RELOC_LO10 : BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }
}

/* Handle the setsw synthetic instruction.  */

#include <stdint.h>

#define SPARC_RD_FIELD_SHIFT 25
#define SPARC_SETHI_HIGH_BITS_SHIFT 10
#define SPARC_SETHI_HIGH_BITS_MASK 0x3fffffU
#define SPARC_IMMLO_13BIT_MASK 0x1fffU
#define SPARC_IMMLO_XOR_LOWER_10BITS_MASK 0x3ffU
#define SPARC_IMMLO_MIN_VAL_FOR_SETHI (-(1 << 12))

static void
synthetize_setsw (const struct sparc_opcode *insn)
{
  int32_t imm32_val;
  int rd;

  rd = (the_insn.opcode & RD (~0)) >> SPARC_RD_FIELD_SHIFT;

  if (the_insn.exp.X_op != O_constant)
    {
      synthetize_setuw (insn);

      the_insn.opcode = (SRA_INSN | RS1 (rd) | RD (rd));
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
      return;
    }

  if (sizeof (offsetT) > sizeof (int32_t) &&
      (the_insn.exp.X_add_number < (offsetT)INT32_MIN ||
       the_insn.exp.X_add_number > (offsetT)UINT32_MAX))
    {
      as_warn (_("setsw: number not in -2147483648..4294967295 range"));
    }

  imm32_val = (int32_t)the_insn.exp.X_add_number;

  if (imm32_val >= 0)
    {
      synthetize_setuw (insn);
      return;
    }

  uint32_t alu_op_code = OR_INSN;
  the_insn.reloc = BFD_RELOC_NONE;

  if (imm32_val < SPARC_IMMLO_MIN_VAL_FOR_SETHI)
    {
      uint32_t sethi_high_part = (uint32_t)((~imm32_val) >> SPARC_SETHI_HIGH_BITS_SHIFT) & SPARC_SETHI_HIGH_BITS_MASK;
      the_insn.opcode = (SETHI_INSN | RD (rd) | sethi_high_part);
      output_insn (insn, &the_insn);

      imm32_val = 0x1c00 | (imm32_val & SPARC_IMMLO_XOR_LOWER_10BITS_MASK);
      alu_op_code = RS1 (rd) | XOR_INSN;
    }

  the_insn.opcode = (alu_op_code | RD (rd) | IMMED
                     | (imm32_val & SPARC_IMMLO_13BIT_MASK));
  output_insn (insn, &the_insn);
}

/* Handle the setx synthetic instruction.  */

static inline int
fits_in_simm13 (int32_t value)
{
  return value >= (-(1 << 12)) && value <= ((1 << 12) - 1);
}

static void
synthetize_setx (const struct sparc_opcode *insn)
{
  int32_t upper32, lower32;
  int tmpreg = (the_insn.opcode & RS1 (~0)) >> 14;
  int dstreg = (the_insn.opcode & RD (~0)) >> 25;
  int upper_dstreg;
  int need_hh22_p = 0, need_hm10_p = 0, need_hi22_p = 0, need_lo10_p = 0;
  int need_xor10_p = 0;

  /* Constants for SPARC immediate fields */
#define SPARC_IMM10_MASK               0x3ff
#define SPARC_IMM13_MASK               0x1fff
#define SPARC_SETHI_IMM_SHIFT          10
#define SPARC_SETHI_IMM_MASK           0x3fffff /* 22 bits */
#define SPARC_SLLX_SHIFT_AMOUNT        32
#define SPARC_XOR_NEG_CONST_IMM_HIGH_BITS 0x1c00 /* Specific for XOR negative constant handling */

  /* Extract and sign-extend 32-bit halves from the 64-bit constant.
     Assuming X_add_number is a uint64_t or similar 64-bit unsigned type. */
  lower32 = (int32_t)(the_insn.exp.X_add_number & 0xFFFFFFFFUL);
  upper32 = (int32_t)((the_insn.exp.X_add_number >> SPARC_SLLX_SHIFT_AMOUNT) & 0xFFFFFFFFUL);

  upper_dstreg = tmpreg;
  if (tmpreg == dstreg)
    as_warn (_("setx: temporary register same as destination register"));

  if (the_insn.exp.X_op != O_constant)
    {
      if (sparc_arch_size == 32)
	{
	  /* When arch size is 32, setx is equivalent to setuw for non-constants. */
	  the_insn.exp.X_add_number &= 0xffffffff; /* Truncate for 32-bit arch */
	  synthetize_setuw (insn);
	  return;
	}
      /* For non-constant 64-bit value on 64-bit arch, all components are
         needed for relocation and generated dynamically. */
      need_hh22_p = 1;
      need_hm10_p = 1;
      need_hi22_p = 1;
      need_lo10_p = 1;
      /* lower32 and upper32 are not used for direct instruction generation
         in this path; values come from relocations. */
      lower32 = 0;
      upper32 = 0;
    }
  else /* the_insn.exp.X_op == O_constant */
    {
      /* Reset X_add_number to prevent `fixup_segment` from complaining about
         an 8-byte value being used in a 4-byte field context. */
      the_insn.exp.X_add_number = 0;

      /* Determine needs for upper 32 bits (HH22 and HM10) */
      if (!fits_in_simm13(upper32))
	need_hh22_p = 1;

      /* Need HM10 if there are low bits in upper32 to set via OR instruction. */
      if ((need_hh22_p && (upper32 & SPARC_IMM10_MASK) != 0) ||
          (!need_hh22_p && upper32 != 0 && (upper32 & SPARC_IMM13_MASK) != 0))
	need_hm10_p = 1;

      /* Determine needs for lower 32 bits (HI22, LO10, XOR10) */
      /* Process lower 32 bits if `lower32` is non-zero, or if upper 32 bits
         were constructed (implying a full 64-bit constant). */
      if (lower32 != 0 || need_hh22_p || need_hm10_p)
	{
	  int lower32_is_negative = lower32 < 0;
	  int upper32_is_all_ones = upper32 == -1;

	  /* Need SETHI for lower 32 bits if it doesn't fit in simm13,
	     or special handling is required due to sign interaction with upper32. */
	  if (!fits_in_simm13(lower32) ||
	      (lower32_is_negative && !upper32_is_all_ones) ||
	      (!lower32_is_negative && upper32_is_all_ones))
	    need_hi22_p = 1;

	  /* Special XOR case for negative lower32 when upper32 is all ones.
	     This synthesizes a large negative 64-bit constant. */
	  if (need_hi22_p && upper32_is_all_ones)
	    need_xor10_p = 1;
	  /* Need LO10 (OR instruction) if there are low bits in lower32 to set,
	     or if `lower32` itself is the only non-zero component of the constant. */
	  else if ((need_hi22_p && (lower32 & SPARC_IMM10_MASK) != 0) ||
		   (!need_hi22_p && (lower32 & SPARC_IMM13_MASK) != 0))
	    need_lo10_p = 1;
	}
      else /* Constant is 0: lower32 is 0 AND no upper32 bits were needed. */
	{
	  /* If the constant is 0, no instructions are needed to construct it.
	     The destination register implicitly holds 0 (G0) or will be cleared.
	     Setting upper_dstreg to dstreg ensures that if any post-processing
	     (like a final OR) is still triggered, it operates on the correct register.
	     However, for a 0 constant, no further instructions will be generated. */
	  upper_dstreg = dstreg;
	}
    }

  /* Warn if the temporary register (if used) is g0, and the destination is not g0. */
  if (!upper_dstreg && dstreg)
    as_warn (_("setx: illegal temporary register g0"));

  /* Generate instructions based on the determined needs. */

  /* HH22: SETHI for upper 22 bits of upper32. */
  if (need_hh22_p)
    {
      the_insn.opcode = (SETHI_INSN | RD (upper_dstreg)
			 | ((upper32 >> SPARC_SETHI_IMM_SHIFT) & SPARC_SETHI_IMM_MASK));
      the_insn.reloc = (the_insn.exp.X_op != O_constant ? BFD_RELOC_SPARC_HH22 : BFD_RELOC_NONE);
      output_insn (insn, &the_insn);
    }

  /* HI22: SETHI for upper 22 bits of lower32. */
  if (need_hi22_p)
    {
      the_insn.opcode = (SETHI_INSN | RD (dstreg)
			 | (((need_xor10_p ? ~lower32 : lower32)
			     >> SPARC_SETHI_IMM_SHIFT) & SPARC_SETHI_IMM_MASK));
      the_insn.reloc = (the_insn.exp.X_op != O_constant ? BFD_RELOC_SPARC_LM22 : BFD_RELOC_NONE);
      output_insn (insn, &the_insn);
    }

  /* HM10: OR for lower 10/13 bits of upper32. */
  if (need_hm10_p)
    {
      the_insn.opcode = (OR_INSN
			 | (need_hh22_p ? RS1 (upper_dstreg) : 0) /* If HH22 was used, OR with upper_dstreg. */
			 | RD (upper_dstreg)
			 | IMMED
			 | (upper32 & (need_hh22_p ? SPARC_IMM10_MASK : SPARC_IMM13_MASK))); /* Mask depends on SETHI use. */
      the_insn.reloc = (the_insn.exp.X_op != O_constant ? BFD_RELOC_SPARC_HM10 : BFD_RELOC_NONE);
      output_insn (insn, &the_insn);
    }

  /* LO10: OR for lower 10/13 bits of lower32. */
  if (need_lo10_p)
    {
      /* FIXME: One nice optimization to do here is to OR the low part
	 with the highpart if hi22 isn't needed and the low part is
	 positive. */
      the_insn.opcode = (OR_INSN | (need_hi22_p ? RS1 (dstreg) : 0) /* If HI22 was used, OR with dstreg. */
			 | RD (dstreg)
			 | IMMED
			 | (lower32 & (need_hi22_p ? SPARC_IMM10_MASK : SPARC_IMM13_MASK))); /* Mask depends on SETHI use. */
      the_insn.reloc = (the_insn.exp.X_op != O_constant ? BFD_RELOC_LO10 : BFD_RELOC_NONE);
      output_insn (insn, &the_insn);
    }

  /* If upper part was built, shift it into place (SLLX by 32). */
  if (need_hh22_p || need_hm10_p)
    {
      the_insn.opcode = (SLLX_INSN | RS1 (upper_dstreg) | RD (upper_dstreg)
			 | IMMED | SPARC_SLLX_SHIFT_AMOUNT);
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

  /* Special XOR instruction for negative constants (upper32 == -1) where `~lower32` is used with SETHI. */
  if (need_xor10_p)
    {
      the_insn.opcode = (XOR_INSN | RS1 (dstreg) | RD (dstreg) | IMMED
			 | SPARC_XOR_NEG_CONST_IMM_HIGH_BITS | (lower32 & SPARC_IMM10_MASK));
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }
  /* If both upper and lower parts were built into different registers, OR them together. */
  else if ((need_hh22_p || need_hm10_p) && (need_hi22_p || need_lo10_p))
    {
      the_insn.opcode = (OR_INSN | RS1 (dstreg) | RS2 (upper_dstreg)
			 | RD (dstreg));
      the_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &the_insn);
    }

#undef SPARC_IMM10_MASK
#undef SPARC_IMM13_MASK
#undef SPARC_SETHI_IMM_SHIFT
#undef SPARC_SETHI_IMM_MASK
#undef SPARC_SLLX_SHIFT_AMOUNT
#undef SPARC_XOR_NEG_CONST_IMM_HIGH_BITS
}

/* Main entry point to assemble one instruction.  */

static inline int
is_in_delay_slot (void)
{
  return last_insn != NULL && (last_insn->flags & F_DELAYED) != 0;
}

static inline void
check_dcti_couple_warning (const struct sparc_opcode *insn)
{
  if (dcti_couples_detect
      && (insn->flags & F_DELAYED) != 0
      && ((max_architecture < SPARC_OPCODE_ARCH_V9
           && (last_insn->flags & F_CONDBR) != 0)
          || max_architecture >= SPARC_OPCODE_ARCH_V9C))
    {
      as_warn (_("unpredictable DCTI couple"));
    }
}

static inline void
check_fp_branch_in_delay_slot_warning (const struct sparc_opcode *insn)
{
  if ((insn->flags & F_FBR) != 0
      && ((last_insn->flags & (F_UNBR | F_CONDBR | F_FBR)) == 0
          || (last_opcode & ANNUL) == 0))
    {
      as_warn (_("FP branch in delay slot"));
    }
}

static inline void
handle_fp_compare_preceded_by_fp_branch (const struct sparc_opcode *insn)
{
  if (max_architecture < SPARC_OPCODE_ARCH_V9
      && last_insn != NULL
      && (insn->flags & F_FBR) != 0
      && (last_insn->flags & F_FLOAT) != 0
      && (last_insn->match & OP3 (0x35)) == OP3 (0x35))
    {
      struct sparc_it nop_insn;
      nop_insn.opcode = NOP_INSN;
      nop_insn.reloc = BFD_RELOC_NONE;
      output_insn (insn, &nop_insn);
      as_warn (_("FP branch preceded by FP compare; NOP inserted"));
    }
}

static inline void
handle_special_case_fdiv (const struct sparc_opcode *insn)
{
  int rd = (the_insn.opcode >> 25) & 0x1f;

  output_insn (insn, &the_insn);

  gas_assert (the_insn.reloc == BFD_RELOC_NONE);
  the_insn.opcode = FMOVS_INSN | rd | RD (rd);
  output_insn (insn, &the_insn);
}

void
md_assemble (char *str)
{
  const struct sparc_opcode *insn;
  int special_case;

  know (str);
  special_case = sparc_ip (str, &insn);

  if (insn == NULL)
    {
      return;
    }

  if (is_in_delay_slot ())
    {
      check_dcti_couple_warning (insn);
      check_fp_branch_in_delay_slot_warning (insn);
    }

  handle_fp_compare_preceded_by_fp_branch (insn);

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
      handle_special_case_fdiv (insn);
      return;

    default:
      as_fatal (_("failed special case insn sanity check"));
    }
}

#include <stdint.h>

typedef struct {
    uint64_t flag;
    const char *name;
} hwcap_entry_t;

static const hwcap_entry_t hwcap_map[] = {
    { HWCAP_MUL32, "mul32" },
    { HWCAP_DIV32, "div32" },
    { HWCAP_FSMULD, "fsmuld" },
    { HWCAP_V8PLUS, "v8plus" },
    { HWCAP_POPC, "popc" },
    { HWCAP_VIS, "vis" },
    { HWCAP_VIS2, "vis2" },
    { HWCAP_ASI_BLK_INIT, "ASIBlkInit" },
    { HWCAP_FMAF, "fmaf" },
    { HWCAP_VIS3, "vis3" },
    { HWCAP_HPC, "hpc" },
    { HWCAP_RANDOM, "random" },
    { HWCAP_TRANS, "trans" },
    { HWCAP_FJFMAU, "fjfmau" },
    { HWCAP_IMA, "ima" },
    { HWCAP_ASI_CACHE_SPARING, "cspare" },
    { HWCAP_AES, "aes" },
    { HWCAP_DES, "des" },
    { HWCAP_KASUMI, "kasumi" },
    { HWCAP_CAMELLIA, "camellia" },
    { HWCAP_MD5, "md5" },
    { HWCAP_SHA1, "sha1" },
    { HWCAP_SHA256, "sha256" },
    { HWCAP_SHA512, "sha512" },
    { HWCAP_MPMUL, "mpmul" },
    { HWCAP_MONT, "mont" },
    { HWCAP_PAUSE, "pause" },
    { HWCAP_CBCOND, "cbcond" },
    { HWCAP_CRC32C, "crc32c" },
    { (uint64_t)HWCAP2_FJATHPLUS << 32, "fjathplus" },
    { (uint64_t)HWCAP2_VIS3B << 32, "vis3b" },
    { (uint64_t)HWCAP2_ADP << 32, "adp" },
    { (uint64_t)HWCAP2_SPARC5 << 32, "sparc5" },
    { (uint64_t)HWCAP2_MWAIT << 32, "mwait" },
    { (uint64_t)HWCAP2_XMPMUL << 32, "xmpmul" },
    { (uint64_t)HWCAP2_XMONT << 32, "xmont" },
    { (uint64_t)HWCAP2_NSEC << 32, "nsec" },
    { (uint64_t)HWCAP2_SPARC6 << 32, "sparc6" },
    { (uint64_t)HWCAP2_ONADDSUB << 32, "onaddsub" },
    { (uint64_t)HWCAP2_ONMUL << 32, "onmul" },
    { (uint64_t)HWCAP2_ONDIV << 32, "ondiv" },
    { (uint64_t)HWCAP2_DICTUNP << 32, "dictunp" },
    { (uint64_t)HWCAP2_FPCMPSHL << 32, "fpcmpshl" },
    { (uint64_t)HWCAP2_RLE << 32, "rle" },
    { (uint64_t)HWCAP2_SHA3 << 32, "sha3" }
};

static const char *
get_hwcap_name (uint64_t mask)
{
  for (size_t i = 0; i < sizeof(hwcap_map) / sizeof(hwcap_map[0]); ++i)
    {
      if (mask & hwcap_map[i].flag)
        {
          return hwcap_map[i].name;
        }
    }
  return "UNKNOWN";
}

/* Subroutine of md_assemble to do the actual parsing.  */

static int
sparc_ip (char *str, const struct sparc_opcode **pinsn)
{
  const char *error_message = NULL;
  char *s = str;
  char *args_start_ptr;
  int comma_present = 0;
  const struct sparc_opcode *insn_candidate;
  int special_case = SPECIAL_CASE_NONE;

  // --- Phase 1: Parse opcode name and handle initial comma/whitespace ---
  char *opcode_name_end = s;
  if (ISLOWER (*opcode_name_end))
    {
      do
	++opcode_name_end;
      while (ISLOWER (*opcode_name_end) || ISDIGIT (*opcode_name_end) || *opcode_name_end == '_');
    }

  switch (*opcode_name_end)
    {
    case '\0':
      break; // No arguments, just the opcode name

    case ',':
      comma_present = 1;
      *opcode_name_end++ = '\0'; // Null-terminate opcode name, advance s
      s = opcode_name_end; // Update s to point to arguments
      break;

    default:
      if (is_whitespace (*opcode_name_end))
	{
	  *opcode_name_end++ = '\0'; // Null-terminate opcode name, advance s
	  s = opcode_name_end; // Update s to point to arguments
	  break;
	}
      as_bad (_("Unknown opcode: `%s'"), str);
      *pinsn = NULL;
      return special_case; // Error, return default special_case
    }

  // Lookup the opcode
  insn_candidate = str_hash_find (op_hash, str);
  if (insn_candidate == NULL)
    {
      as_bad (_("Unknown opcode: `%s'"), str);
      *pinsn = NULL;
      return special_case; // Error, return default special_case
    }

  // Restore comma if it was present, for argument parsing if needed by get_expression
  if (comma_present)
    {
      *--opcode_name_end = ',';
    }

  args_start_ptr = s; // Save start of arguments for retries if multiple variants exist

  // --- Phase 2: Parse arguments and find best matching instruction variant ---
  for (;; ++insn_candidate) // Loop through opcode variants with the same name
    {
      // Check if we went past the end of the table or to a new opcode name
      if (insn_candidate - sparc_opcodes >= sparc_num_opcodes
          || (insn_candidate != str_hash_find (op_hash, str) && strcmp (insn_candidate->name, str) != 0))
        {
          // No more variants for this opcode name, report the error from the last attempt.
          if (error_message)
            as_bad (_("Illegal operands%s: `%s %s'"), error_message, str, args_start_ptr);
          else
            as_bad (_("Illegal operands: `%s %s'"), str, args_start_ptr);
          *pinsn = NULL;
          return special_case;
        }

      unsigned long current_opcode = insn_candidate->match;
      char *current_s_ptr = args_start_ptr; // Reset argument pointer for each variant
      bool operands_match = true;
      int v9_arg_p = 0;
      const sparc_asi *sasi = NULL;

      memset (&the_insn, '\0', sizeof (the_insn)); // Reset instruction data for this attempt
      the_insn.reloc = BFD_RELOC_NONE;

      for (const char *args_def = insn_candidate->args; *args_def; ++args_def)
	{
	  char arg_code = *args_def;

	  // Skip whitespace before parsing operand
	  while (is_whitespace(*current_s_ptr))
	    ++current_s_ptr;

          switch (arg_code)
            {
            case 'K': // Membar mask
            case '3': // Siam mode
            case '*': // Prefetch function
            case 'A': // ASI
            case '|': // 2-bit immediate
              {
                int parsed_value = 0;
                if (arg_code == 'K') { // Membar mask
                  if (*current_s_ptr == '#') {
                    while (*current_s_ptr == '#') {
                      int jmask;
                      if (!parse_keyword_arg(sparc_encode_membar, &current_s_ptr, &jmask))
                        { error_message = _(": invalid membar mask name"); operands_match = false; break; }
                      parsed_value |= jmask;
                      while (is_whitespace(*current_s_ptr)) ++current_s_ptr;
                      if (*current_s_ptr == '|' || *current_s_ptr == '+') ++current_s_ptr;
                      while (is_whitespace(*current_s_ptr)) ++current_s_ptr;
                    }
                  } else {
                    if (!parse_const_expr_arg(&current_s_ptr, &parsed_value))
                      { error_message = _(": invalid membar mask expression"); operands_match = false; break; }
                    if (parsed_value < 0 || parsed_value > 127)
                      { error_message = _(": invalid membar mask number"); operands_match = false; break; }
                  }
                  current_opcode |= MEMBAR (parsed_value);
                } else if (arg_code == '3') { // Siam mode
                  if (!parse_const_expr_arg(&current_s_ptr, &parsed_value))
                    { error_message = _(": invalid siam mode expression"); operands_match = false; break; }
                  if (parsed_value < 0 || parsed_value > 7)
                    { error_message = _(": invalid siam mode number"); operands_match = false; break; }
                  current_opcode |= parsed_value;
                } else if (arg_code == '*') { // Prefetch function
                  if (*current_s_ptr == '#') {
                    if (!parse_keyword_arg(sparc_encode_prefetch, &current_s_ptr, &parsed_value))
                      { error_message = _(": invalid prefetch function name"); operands_match = false; break; }
                  } else {
                    if (!parse_const_expr_arg(&current_s_ptr, &parsed_value))
                      { error_message = _(": invalid prefetch function expression"); operands_match = false; break; }
                    if (parsed_value < 0 || parsed_value > 31)
                      { error_message = _(": invalid prefetch function number"); operands_match = false; break; }
                  }
                  current_opcode |= RD (parsed_value);
                } else if (arg_code == 'A') { // ASI
                  if (*current_s_ptr == '#') {
                    if (!parse_sparc_asi(&current_s_ptr, &sasi))
                      { error_message = _(": invalid ASI name"); operands_match = false; break; }
                    parsed_value = sasi->value;
                  } else {
                    if (!parse_const_expr_arg(&current_s_ptr, &parsed_value))
                      { error_message = _(": invalid ASI expression"); operands_match = false; break; }
                    if (parsed_value < 0 || parsed_value > 255)
                      { error_message = _(": invalid ASI number"); operands_match = false; break; }
                  }
                  current_opcode |= ASI (parsed_value);
                } else if (arg_code == '|') { // 2-bit immediate
                  if (!parse_const_expr_arg(&current_s_ptr, &parsed_value))
                    { error_message = _(": non-immdiate imm2 operand"); operands_match = false; break; }
                  if ((parsed_value & ~0x3) != 0)
                    { error_message = _(": imm2 immediate operand out of range (0-3)"); operands_match = false; break; }
                  current_opcode |= ((unsigned long)(parsed_value & 0x2) << 3) | (parsed_value & 0x1);
                }
              }
              if (!operands_match) break;
              break;

            case '!': case '?': // Privileged registers
            case '$': case '%': // Hyperprivileged registers
            case '_': case '/': // V9a ASR registers
              {
                const struct priv_reg_entry *table = NULL;
                unsigned int shift_amount;
                if (arg_code == '!' || arg_code == '?') { table = priv_reg_table; shift_amount = (arg_code == '?' ? 14 : 25); }
                else if (arg_code == '$' || arg_code == '%') { table = hpriv_reg_table; shift_amount = (arg_code == '$' ? 14 : 25); }
                else { table = v9a_asr_table; shift_amount = (arg_code == '/' ? 14 : 25); }

                if (*current_s_ptr != '%')
                  { error_message = _(": expecting '%' for privileged register"); operands_match = false; break; }
                current_s_ptr++; // Consume '%'

                const struct priv_reg_entry *p;
                unsigned int len = 0;
                bool found_reg = false;
                for (p = table; p->name; p++) {
                  if (p->name[0] == current_s_ptr[0]) {
                    len = strlen (p->name);
                    if (strncmp (p->name, current_s_ptr, len) == 0) { found_reg = true; break; }
                  }
                }

                if (!found_reg)
                  { error_message = _(": unrecognizable privileged register"); operands_match = false; break; }

                unsigned int expected_regnum_bits = ((insn_candidate->match >> shift_amount) & 0x1f);
                if (expected_regnum_bits != (unsigned) p->regnum)
                  { error_message = _(": unrecognizable privileged register (mismatch)"); operands_match = false; break; }

                current_s_ptr += len;
              }
              break;

            case 'M': case 'm': // %asrN
              if (startswith(current_s_ptr, "%asr")) {
                current_s_ptr += 4;
                if (!ISDIGIT(*current_s_ptr))
                  { error_message = _(": expecting %asrN"); operands_match = false; break; }

                long num = 0;
                while (ISDIGIT (*current_s_ptr)) { num = num * 10 + *current_s_ptr - '0'; ++current_s_ptr; }

                if (num < 0 || num > 31)
                  { error_message = _(": asr number must be between 0 and 31"); operands_match = false; break; }

                current_opcode |= (arg_code == 'M' ? RS1 (num) : RD (num));
              } else { operands_match = false; break; }
              break;

            case ')': // Crypto immediate
              {
                long num = 0;
                char *s_tmp = current_s_ptr;
                if (startswith(s_tmp, "0x") && ISXDIGIT(s_tmp[2])) {
                  s_tmp += 2;
                  while (ISXDIGIT(*s_tmp)) { num = (num << 4) | hex_value(*s_tmp); ++s_tmp; }
                } else if (ISDIGIT(*s_tmp)) {
                  while (ISDIGIT(*s_tmp)) { num = num * 10 + (*s_tmp - '0'); ++s_tmp; }
                } else { error_message = _(": expecting crypto immediate"); operands_match = false; break; }

                if (num < 0 || num > 31)
                  { error_message = _(": crypto immediate must be between 0 and 31"); operands_match = false; break; }

                current_opcode |= RS3 (num);
                current_s_ptr = s_tmp;
              }
              break;

            case 'I': case 'j': case 'X': case 'Y': case 'k':
            case '=': case 'G': case '0': case 'l': case 'L':
            case 'h': case 'n': case 'i': // Various immediates
              {
                bfd_reloc_code_real_type old_reloc_type = the_insn.reloc;
                const char *op_arg_name = NULL;
                expressionS op_exp_temp;
                memset(&op_exp_temp, 0, sizeof(op_exp_temp));

                // Set initial reloc type based on arg_code
                switch (arg_code) {
                  case 'I': the_insn.reloc = BFD_RELOC_SPARC_11; break;
                  case 'j': the_insn.reloc = BFD_RELOC_SPARC_10; break;
                  case 'X': the_insn.reloc = SPARC_OPCODE_ARCH_V9_P(max_architecture) ? BFD_RELOC_SPARC_5 : BFD_RELOC_SPARC13; break;
                  case 'Y': the_insn.reloc = SPARC_OPCODE_ARCH_V9_P(max_architecture) ? BFD_RELOC_SPARC_6 : BFD_RELOC_SPARC13; break;
                  case 'k': the_insn.reloc = BFD_RELOC_SPARC_WDISP16; the_insn.pcrel = 1; break;
                  case '=': the_insn.reloc = BFD_RELOC_SPARC_WDISP10; the_insn.pcrel = 1; break;
                  case 'G': the_insn.reloc = BFD_RELOC_SPARC_WDISP19; the_insn.pcrel = 1; break;
                  case '0': the_insn.reloc = BFD_RELOC_NONE; break; // Reloc handled elsewhere
                  case 'l': the_insn.reloc = BFD_RELOC_SPARC_WDISP22; the_insn.pcrel = 1; break;
                  case 'L': the_insn.reloc = BFD_RELOC_32_PCREL_S2; the_insn.pcrel = 1; break;
                  case 'h': case 'n': the_insn.reloc = BFD_RELOC_SPARC22; break;
                  case 'i': the_insn.reloc = BFD_RELOC_SPARC13; break;
                  default: operands_match = false; break;
                }
                if (!operands_match) break;

                // Check for %hi, %lo, etc.
                if (*current_s_ptr == '%') {
                  const struct perc_entry *p;
                  bool found_perc_entry = false;
                  for (p = perc_table; p->type != perc_entry_none; p++) {
                    if ((p->type == perc_entry_imm_pop || p->type == perc_entry_reg)
                        && strncmp (current_s_ptr + 1, p->name, p->len) == 0) {
                      found_perc_entry = true; break;
                    }
                  }
                  if (found_perc_entry && p->type == perc_entry_imm_pop) {
                    if (current_s_ptr[p->len + 1] != '(')
                      { error_message = _("Illegal operands: %%%s requires arguments in ()"); operands_match = false; break; }
                    op_arg_name = p->name;
                    the_insn.reloc = p->pop->reloc;
                    current_s_ptr += p->len + 2; // Advance past %perc(
                    v9_arg_p = p->pop->flags & F_POP_V9;
                  }
                }
                if (!operands_match) break;

                char *s1_expr_end;
                if (op_arg_name) {
                  int npar = 0;
                  s1_expr_end = current_s_ptr;
                  for (; *s1_expr_end && *s1_expr_end != ',' && *s1_expr_end != ']'; s1_expr_end++)
                    if (*s1_expr_end == '(') npar++;
                    else if (*s1_expr_end == ')') { if (!npar) break; npar--; }

                  if (*s1_expr_end != ')')
                    { error_message = _("Illegal operands: %%%s requires arguments in ()"); operands_match = false; break; }

                  *s1_expr_end = '\0'; // Temporarily null-terminate for get_expression
                  (void) get_expression (current_s_ptr);
                  *s1_expr_end = ')'; // Restore
                  if (expr_parse_end != s1_expr_end)
                    { error_message = _("Expression inside %%%s could not be parsed"); operands_match = false; break; }

                  current_s_ptr = s1_expr_end + 1;
                  if (*current_s_ptr == ',' || *current_s_ptr == ']' || *current_s_ptr == '\0') { /* OK, no trailing +%reg */ }
                  else if (*current_s_ptr != '+' && *current_s_ptr != '-')
                    { error_message = _("Illegal operands: Can't do arithmetics other than + and - involving %%%s()"); operands_match = false; break; }
                  else {
                    // Trailing +%reg, need to parse the second part
                    *s1_expr_end = '0'; // Restore original char (first char of %reg part), used by original for get_expression
                    current_s_ptr = s1_expr_end;
                    op_exp_temp = the_insn.exp;
                    memset (&the_insn.exp, 0, sizeof (the_insn.exp));
                  }
                }
                if (!operands_match) break;

                // Parse the main expression (or the trailing +%reg part)
                s1_expr_end = current_s_ptr;
                for (; *s1_expr_end && *s1_expr_end != ',' && *s1_expr_end != ']'; s1_expr_end++);

                if (s1_expr_end != current_s_ptr && ISDIGIT (s1_expr_end[-1])) {
                  char *reg_ptr_suffix = NULL;
                  if (s1_expr_end[-2] == '%' && s1_expr_end[-3] == '+') reg_ptr_suffix = s1_expr_end - 3;
                  else if (strchr ("golir0123456789", s1_expr_end[-2]) && s1_expr_end[-3] == '%' && s1_expr_end[-4] == '+') reg_ptr_suffix = s1_expr_end - 4;
                  else if (s1_expr_end[-3] == 'r' && s1_expr_end[-4] == '%' && s1_expr_end[-5] == '+') reg_ptr_suffix = s1_expr_end - 5;

                  if (reg_ptr_suffix) {
                    *reg_ptr_suffix = '\0'; // Temporarily null-terminate expression part
                    if (op_arg_name && reg_ptr_suffix == current_s_ptr + 1)
                      the_insn.exp.X_op = O_absent;
                    else
                      (void) get_expression (current_s_ptr);
                    *reg_ptr_suffix = '+'; // Restore
                    if (op_arg_name) *current_s_ptr = ')'; // Original code restores ')' here, not clear why '0' was used earlier. Assuming ')' is correct.
                    current_s_ptr = reg_ptr_suffix;
                  } else { // No trailing +%reg detected by heuristic, parse as full expression
                    (void) get_expression (current_s_ptr);
                    if (op_arg_name) *current_s_ptr = ')';
                    current_s_ptr = expr_parse_end;
                  }
                } else { // Simple expression or no recognized trailing +%reg
                  (void) get_expression (current_s_ptr);
                  if (op_arg_name) *current_s_ptr = ')';
                  current_s_ptr = expr_parse_end;
                }
                if (!operands_match) break;

                // Handle op_arg interactions (e.g., %hi(sym)+offset)
                if (op_arg_name) {
                  the_insn.exp2 = the_insn.exp;
                  the_insn.exp = op_exp_temp;
                  if (the_insn.exp2.X_op == O_absent) the_insn.exp2.X_op = O_illegal;
                  else if (the_insn.exp.X_op == O_absent) {
                    the_insn.exp = the_insn.exp2;
                    the_insn.exp2.X_op = O_illegal;
                  } else if (the_insn.exp.X_op == O_constant) {
                    valueT val = the_insn.exp.X_add_number;
                    switch (the_insn.reloc) {
                      case BFD_RELOC_SPARC_HH22: val = BSR (val, 32); /* Fall through. */
                      case BFD_RELOC_SPARC_LM22: case BFD_RELOC_HI22: val = (val >> 10) & 0x3fffff; break;
                      case BFD_RELOC_SPARC_HM10: val = BSR (val, 32); /* Fall through. */
                      case BFD_RELOC_LO10: val &= 0x3ff; break;
                      case BFD_RELOC_SPARC_H34: val >>= 12; val &= 0x3fffff; break;
                      case BFD_RELOC_SPARC_H44: val >>= 22; val &= 0x3fffff; break;
                      case BFD_RELOC_SPARC_M44: val >>= 12; val &= 0x3ff; break;
                      case BFD_RELOC_SPARC_L44: val &= 0xfff; break;
                      case BFD_RELOC_SPARC_HIX22: val = ~val; val = (val >> 10) & 0x3fffff; break;
                      case BFD_RELOC_SPARC_LOX10: val = (val & 0x3ff) | 0x1c00; break;
                      default: break;
                    }
                    the_insn.exp = the_insn.exp2;
                    the_insn.exp.X_add_number += val;
                    the_insn.exp2.X_op = O_illegal;
                    the_insn.reloc = old_reloc_type;
                  } else if (the_insn.exp2.X_op != O_constant) {
                    error_message = _("Illegal operands: Can't add non-constant expression to %%%s()"); operands_match = false; break;
                  } else {
                    if (!(old_reloc_type == BFD_RELOC_SPARC13 && the_insn.reloc == BFD_RELOC_LO10
                          && sparc_arch_size == 64 && !sparc_pic_code)) {
                      error_message = _("Illegal operands: Can't do arithmetics involving %%%s() of a relocatable symbol"); operands_match = false; break;
                    }
                    the_insn.reloc = BFD_RELOC_SPARC_OLO10;
                  }
                }
                if (!operands_match) break;

                // Final checks for constants
                if (the_insn.exp.X_op == O_constant && the_insn.exp.X_add_symbol == 0 && the_insn.exp.X_op_symbol == 0) {
                  if (the_insn.pcrel && the_insn.reloc == BFD_RELOC_32_PCREL_S2 && in_signed_range(the_insn.exp.X_add_number, 0x3fff))
                    { error_message = _(": PC-relative operand can't be a constant"); operands_match = false; break; }
                  if (the_insn.reloc >= BFD_RELOC_SPARC_TLS_GD_HI22 && the_insn.reloc <= BFD_RELOC_SPARC_TLS_TPOFF64)
                    { error_message = _(": TLS operand can't be a constant"); operands_match = false; break; }

                  if (the_insn.reloc == BFD_RELOC_SPARC_5 && ((insn_candidate->match & OP(0x3)) == 0)) {
                    valueT val = the_insn.exp.X_add_number;
                    the_insn.reloc = BFD_RELOC_NONE;
                    if (!in_bitfield_range(val, 0x1f))
                      { error_message = _(": Immediate value in cbcond is out of range."); operands_match = false; break; }
                    current_opcode |= val & 0x1f;
                  }
                }
              }
              if (!operands_match) break;
              break;

            case 'N': // 'pn' for prefetch_zero
              if (startswith(current_s_ptr, "pn")) { current_s_ptr += 2; break; }
              operands_match = false; break;

            case 'T': // 'pt' for prefetch_zero
              if (startswith(current_s_ptr, "pt")) { current_s_ptr += 2; break; }
              operands_match = false; break;

            case 'z': // %icc (32-bit %ncc)
              if (startswith(current_s_ptr, "%icc") || (sparc_arch_size == 32 && startswith(current_s_ptr, "%ncc")))
                { current_s_ptr += 4; break; }
              operands_match = false; break;

            case 'Z': // %xcc (64-bit %ncc)
              if (startswith(current_s_ptr, "%xcc") || (sparc_arch_size == 64 && startswith(current_s_ptr, "%ncc")))
                { current_s_ptr += 4; break; }
              operands_match = false; break;

            case '6': // %fcc0
              if (startswith(current_s_ptr, "%fcc0")) { current_s_ptr += 5; break; }
              operands_match = false; break;
            case '7': // %fcc1
              if (startswith(current_s_ptr, "%fcc1")) { current_s_ptr += 5; break; }
              operands_match = false; break;
            case '8': // %fcc2
              if (startswith(current_s_ptr, "%fcc2")) { current_s_ptr += 5; break; }
              operands_match = false; break;
            case '9': // %fcc3
              if (startswith(current_s_ptr, "%fcc3")) { current_s_ptr += 5; break; }
              operands_match = false; break;

            case 'P': // %pc
              if (startswith(current_s_ptr, "%pc")) { current_s_ptr += 3; break; }
              operands_match = false; break;

            case 'W': // %tick
              if (startswith(current_s_ptr, "%tick")) { current_s_ptr += 5; break; }
              operands_match = false; break;

            case '\0': // End of args definition. Check if input string is also at end or has special suffix.
              if (current_s_ptr[0] == ',' && current_s_ptr[1] == '%') { // Handle %perc(..) post-operands
                  char *s1_tmp = current_s_ptr;
                  const struct perc_entry *p;
                  bool found_perc_entry = false;

                  for (p = perc_table; p->type != perc_entry_none; p++) {
                    if ((p->type == perc_entry_post_pop || p->type == perc_entry_reg)
                        && strncmp (s1_tmp + 2, p->name, p->len) == 0) {
                      found_perc_entry = true; break;
                    }
                  }
                  if (!found_perc_entry || p->type == perc_entry_reg) { operands_match = false; break; }

                  if (s1_tmp[p->len + 2] != '(')
                    { error_message = _("Illegal operands: %%%s requires arguments in ()"); operands_match = false; break; }

                  if (! (p->pop->flags & F_POP_TLS_CALL) && the_insn.reloc != BFD_RELOC_NONE)
                    { error_message = _("Illegal operands: %%%s cannot be used together with other relocs in the insn ()"); operands_match = false; break; }

                  if ((p->pop->flags & F_POP_TLS_CALL)
                      && (the_insn.reloc != BFD_RELOC_32_PCREL_S2
                          || the_insn.exp.X_add_number != 0
                          || the_insn.exp.X_add_symbol != symbol_find_or_make ("__tls_get_addr")))
                    { error_message = _("Illegal operands: %%%s can be only used with call __tls_get_addr"); operands_match = false; break; }

                  the_insn.reloc = p->pop->reloc;
                  memset (&the_insn.exp, 0, sizeof (the_insn.exp));
                  current_s_ptr += p->len + 3; // Advance past ",%perc("

                  int npar = 0;
                  char *arg_end = current_s_ptr;
                  for (; *arg_end && *arg_end != ',' && *arg_end != ']'; arg_end++)
                    if (*arg_end == '(') npar++;
                    else if (*arg_end == ')') { if (!npar) break; npar--; }

                  if (*arg_end != ')')
                    { error_message = _("Illegal operands: %%%s requires arguments in ()"); operands_match = false; break; }

                  *arg_end = '\0'; // Temporarily null-terminate for get_expression
                  (void) get_expression (current_s_ptr);
                  *arg_end = ')'; // Restore
                  current_s_ptr = arg_end + 1;
                }
              if (*current_s_ptr == '\0') operands_match = true; // Matched all arguments
              else operands_match = false; // Extra characters at the end
              break;

            case '+': // Optional '+' or '-'
              if (*current_s_ptr == '+') { ++current_s_ptr; break; }
              if (*current_s_ptr == '-') { break; } // '-' is also allowed but doesn't consume it
              operands_match = false; break;

            case '[': case ']': case ',': // Exact character match
              if (*current_s_ptr == arg_code) { ++current_s_ptr; break; }
              operands_match = false; break;

            case ' ': // Whitespace
              if (!is_whitespace(*current_s_ptr)) { operands_match = false; break; }
              ++current_s_ptr; // Consume one whitespace character
              break;

            case '#': // Must be at least one digit
              if (ISDIGIT (*current_s_ptr)) {
                while (ISDIGIT (*current_s_ptr)) { ++current_s_ptr; }
                break;
              }
              operands_match = false; break;

            case 'b': case 'c': case 'D': // Coprocessor registers
              {
                unsigned int mask = 0;
                if (!(*current_s_ptr == '%' && current_s_ptr[1] == 'c' && ISDIGIT(current_s_ptr[2])))
                  { error_message = _(": expecting %cN for coprocessor register"); operands_match = false; break; }
                current_s_ptr += 2; // Move past %c

                mask = *current_s_ptr++ - '0';
                if (ISDIGIT (*current_s_ptr)) {
                  mask = mask * 10 + (*current_s_ptr - '0');
                  ++current_s_ptr;
                }
                if (mask >= 32)
                  { error_message = _(": coprocessor register number must be between 0 and 31"); operands_match = false; break; }

                switch (arg_code) {
                  case 'b': current_opcode |= mask << 14; break;
                  case 'c': current_opcode |= mask; break;
                  case 'D': current_opcode |= mask << 25; break;
                  default: break; // Should not happen
                }
              }
              break;

            case 'r': case 'O': case '1': case '2': case 'd': // General registers
              {
                unsigned int mask = 0;
                char reg_type_char;
                if (*current_s_ptr++ != '%') { error_message = _(": expecting '%' for general register"); operands_match = false; break; }
                reg_type_char = *current_s_ptr++;

                switch (reg_type_char) {
                  case 'f': if (*current_s_ptr++ != 'p') goto gpr_fail; mask = 0x1e; break;
                  case 'g': if (!isoctal(*current_s_ptr)) goto gpr_fail; mask = *current_s_ptr++ - '0'; break;
                  case 'i': if (!isoctal(*current_s_ptr)) goto gpr_fail; mask = *current_s_ptr++ - '0' + 24; break;
                  case 'l': if (!isoctal(*current_s_ptr)) goto gpr_fail; mask = (*current_s_ptr++ - '0' + 16); break;
                  case 'o': if (!isoctal(*current_s_ptr)) goto gpr_fail; mask = (*current_s_ptr++ - '0' + 8); break;
                  case 's': if (*current_s_ptr++ != 'p') goto gpr_fail; mask = 0xe; break;
                  case 'r': if (!ISDIGIT(*current_s_ptr)) goto gpr_fail; /* FALLTHROUGH */
                  case '0': case '1': case '2': case '3': case '4':
                  case '5': case '6': case '7': case '8': case '9': {
                    int c_val = (reg_type_char == 'r' ? *current_s_ptr++ : reg_type_char);
                    if (ISDIGIT(*current_s_ptr)) {
                      c_val = 10 * (c_val - '0') + (*current_s_ptr++ - '0');
                      if (c_val >= 32) goto gpr_fail;
                    } else { c_val -= '0'; }
                    mask = c_val;
                    break;
                  }
                  default: goto gpr_fail;
                }

                if ((mask & ~1) == 2 && sparc_arch_size == 64 && no_undeclared_regs && ! globals[mask])
                  as_bad (_("detected global register use not covered by .register pseudo-op"));

                switch (arg_code) {
                  case '1': current_opcode |= mask << 14; break;
                  case '2': current_opcode |= mask; break;
                  case 'd': current_opcode |= mask << 25; break;
                  case 'r': current_opcode |= (mask << 25) | (mask << 14); break;
                  case 'O': current_opcode |= (mask << 25) | (mask << 0); break;
                  default: break;
                }
                break;
                gpr_fail: error_message = _(": unrecognizable general purpose register"); operands_match = false; break;
              }

            case 'e': case 'v': case 'V': case ';': case 'f': case 'B': case 'R':
            case ':': case '\'': case '4': case '5': case 'g': case 'H': case 'J':
            case '}': case '^': // Floating point registers
              {
                unsigned int mask = 0; char format;
                if (!(*current_s_ptr++ == '%'
                      && ((format = *current_s_ptr) == 'f' || format == 'd' || format == 'q')
                      && ISDIGIT (*++current_s_ptr)))
                  { operands_match = false; break; }

                for (mask = 0; ISDIGIT (*current_s_ptr); ++current_s_ptr) mask = 10 * mask + (*current_s_ptr - '0');

                if ((arg_code == 'v' || arg_code == 'B' || arg_code == '5' || arg_code == 'H' || arg_code == '\'' || format == 'd') && (mask & 1))
                  { operands_match = false; break; }
                if ((arg_code == 'V' || arg_code == 'R' || arg_code == 'J' || format == 'q') && (mask & 3))
                  { operands_match = false; break; }
                if ((arg_code == ':' || arg_code == ';' || arg_code == '^') && (mask & 7))
                  { operands_match = false; break; }
                if (arg_code == '\'' && mask < 48)
                  { operands_match = false; break; } // Original break if mask < 48, implying error.

                if (mask >= 64) {
                  error_message = SPARC_OPCODE_ARCH_V9_P(max_architecture) ? _(": There are only 64 f registers; [0-63]") : _(": There are only 32 f registers; [0-31]");
                  operands_match = false; break;
                } else if (mask >= 32) {
                  if (SPARC_OPCODE_ARCH_V9_P(max_architecture)) {
                    if (arg_code == 'e' || arg_code == 'f' || arg_code == 'g')
                      { error_message = _(": There are only 32 single precision f registers; [0-31]"); operands_match = false; break; }
                    v9_arg_p = 1; mask -= 31;
                  } else {
                    error_message = _(": There are only 32 f registers; [0-31]"); operands_match = false; break;
                  }
                }
                switch (arg_code) {
                  case 'v': case 'V': case 'e': case ';': current_opcode |= RS1 (mask); break;
                  case 'f': case 'B': case 'R': case ':': current_opcode |= RS2 (mask); break;
                  case '\'': current_opcode |= RS2 (mask & 0xe); break;
                  case '4': case '5': current_opcode |= RS3 (mask); break;
                  case 'g': case 'H': case 'J': case '^': current_opcode |= RD (mask); break;
                  case '}':
                    if (RD (mask) != (current_opcode & RD (0x1f)))
                      { error_message = _(": Instruction requires frs2 and frsd must be the same register"); operands_match = false; break; }
                    break;
                  default: operands_match = false; break;
                }
              }
              break;

            case 'F': // %fsr
              if (startswith(current_s_ptr, "%fsr")) { current_s_ptr += 4; break; }
              operands_match = false; break;

            case '(': // %efsr
              if (startswith(current_s_ptr, "%efsr")) { current_s_ptr += 5; break; }
              operands_match = false; break;

            case 'S': // Special opcode names (set, fdiv). This char acts as a marker.
              if (strcmp(insn_candidate->name, "set") == 0 || strcmp(insn_candidate->name, "setuw") == 0)
                special_case = SPECIAL_CASE_SET;
              else if (strcmp(insn_candidate->name, "setsw") == 0)
                special_case = SPECIAL_CASE_SETSW;
              else if (strcmp(insn_candidate->name, "setx") == 0)
                special_case = SPECIAL_CASE_SETX;
              else if (startswith(insn_candidate->name, "fdiv"))
                special_case = SPECIAL_CASE_FDIV;
              else { error_message = _(": internal error, unexpected special opcode marker S"); operands_match = false; break; }
              break;

            case 'o': // %asi
              if (startswith(current_s_ptr, "%asi")) { current_s_ptr += 4; break; }
              operands_match = false; break;

            case 's': // %fprs
              if (startswith(current_s_ptr, "%fprs")) { current_s_ptr += 5; break; }
              operands_match = false; break;

            case '{': // %mcdper
              if (startswith(current_s_ptr, "%mcdper")) { current_s_ptr += 7; break; }
              operands_match = false; break;

            case '&': // %entropy
              if (startswith(current_s_ptr, "%entropy")) { current_s_ptr += 8; break; }
              operands_match = false; break;

            case 'E': // %ccr
              if (startswith(current_s_ptr, "%ccr")) { current_s_ptr += 4; break; }
              operands_match = false; break;

            case 't': // %tbr
              if (startswith(current_s_ptr, "%tbr")) { current_s_ptr += 4; break; }
              operands_match = false; break;

            case 'w': // %wim
              if (startswith(current_s_ptr, "%wim")) { current_s_ptr += 4; break; }
              operands_match = false; break;
              
            case 'x': // OPF immediate
              {
                char *push = input_line_pointer;
                expressionS e;
                input_line_pointer = current_s_ptr;
                expression (&e);
                if (e.X_op == O_constant) {
                  long n = e.X_add_number;
                  if (n < 0 || n > 0x1ff)
                    as_bad (_("OPF immediate operand out of range (0-0x1ff)"));
                  else
                    current_opcode |= ((unsigned long)n & 0x1ff) << 5;
                } else { as_bad (_("non-immediate OPF operand, ignored")); }
                current_s_ptr = input_line_pointer;
                input_line_pointer = push;
              }
              break;

            case 'y': // %y
              if (startswith(current_s_ptr, "%y")) { current_s_ptr += 2; break; }
              operands_match = false; break;

            case 'u': case 'U': // Sparclet cpreg
              {
                int cpreg_val;
                if (!parse_keyword_arg(sparc_encode_sparclet_cpreg, &current_s_ptr, &cpreg_val))
                  { error_message = _(": invalid cpreg name"); operands_match = false; break; }
                current_opcode |= (arg_code == 'U' ? RS1(cpreg_val) : RD(cpreg_val));
              }
              break;

            default:
              as_fatal (_("failed sanity check. Unhandled arg code: %c"), arg_code);
              operands_match = false; break;
            } // end switch (arg_code)

          if (!operands_match) // If current operand didn't match, break inner loop
            break;
        } // end for (args_def = ...)

      if (operands_match)
	{
	  // Arguments matched. Now check architecture and hwcaps.
	  const char *msg_str = str;
	  int needed_arch_mask = insn_candidate->architecture;

	  // Include the ASI architecture needed as well, taking the highest requirement
          if (sasi && sasi->architecture > needed_arch_mask) {
              needed_arch_mask = sasi->architecture;
              msg_str = sasi->name;
          } else if (sasi) { // Even if not higher, ensure it's part of the mask
              needed_arch_mask |= sasi->architecture;
          }

	  uint64_t hwcaps = ((uint64_t) insn_candidate->hwcaps2 << 32) | insn_candidate->hwcaps;
#ifndef TE_SOLARIS
	  if (hwcaps)
		  hwcap_seen |= hwcaps;
#endif
	  if (v9_arg_p)
	    {
	      // If a V9-specific argument was used, ensure V9 architecture is included.
	      needed_arch_mask &= ~(SPARC_OPCODE_ARCH_MASK (SPARC_OPCODE_ARCH_V9) - 1);
	      if (! needed_arch_mask)
		needed_arch_mask = SPARC_OPCODE_ARCH_MASK (SPARC_OPCODE_ARCH_V9);
	    }

	  if (needed_arch_mask & SPARC_OPCODE_SUPPORTED (current_architecture))
	    {
	      // Architecture OK.
	    }
	  else if (needed_arch_mask & SPARC_OPCODE_SUPPORTED (max_architecture))
	    {
	      // Can bump up architecture.
	      enum sparc_opcode_arch_val needed_architecture =
		sparc_ffs (SPARC_OPCODE_SUPPORTED (max_architecture) & needed_arch_mask);

	      gas_assert (needed_architecture <= SPARC_OPCODE_ARCH_MAX);
	      if (warn_on_bump && needed_architecture > warn_after_architecture)
		{
		  as_warn (_("architecture bumped from \"%s\" to \"%s\" on \"%s\""),
			   sparc_opcode_archs[current_architecture].name,
			   sparc_opcode_archs[needed_architecture].name,
			   msg_str);
		  warn_after_architecture = needed_architecture;
		}
	      current_architecture = needed_architecture;
	      hwcap_allowed = (hwcap_allowed | hwcaps
			       | ((uint64_t) sparc_opcode_archs[current_architecture].hwcaps2 << 32)
			       | sparc_opcode_archs[current_architecture].hwcaps);
	    }
	  else
	    {
	      // Architecture conflict.
	      int arch_idx, printed_one_p = 0;
	      char required_archs[SPARC_OPCODE_ARCH_MAX * 16]; // Max 16 chars per name, SPARC_OPCODE_ARCH_MAX archs
	      char *p_str = required_archs;

	      int current_bit_val = 1;
	      for (arch_idx = 1; arch_idx <= SPARC_OPCODE_ARCH_MAX; ++arch_idx)
	      {
		  if ((current_bit_val & needed_arch_mask) && (arch_idx < sizeof(sparc_opcode_archs)/sizeof(sparc_opcode_archs[0])))
		  {
		      if (printed_one_p) *p_str++ = '|';
		      const char *arch_name = sparc_opcode_archs[arch_idx].name;
		      size_t name_len = strlen(arch_name);
		      if (p_str + name_len < required_archs + sizeof(required_archs)) { // Prevent buffer overflow
			  strcpy(p_str, arch_name);
			  p_str += name_len;
			  printed_one_p = 1;
		      } else {
			  // Truncate or indicate error if buffer is too small
			  strcpy(p_str, "..."); // Indicate truncation
			  p_str += 3;
			  break;
		      }
		  }
		  current_bit_val <<= 1;
	      }
	      *p_str = '\0'; // Null-terminate the string

	      as_bad (_("Architecture mismatch on \"%s %s\"."), str, args_start_ptr);
	      as_tsktsk (_("(Requires %s; requested architecture is %s.)"),
			 required_archs,
			 sparc_opcode_archs[max_architecture].name);
	      *pinsn = NULL;
	      return special_case;
	    }

	  // Make sure the hwcaps used by the instruction are currently enabled.
	  if (hwcaps & ~hwcap_allowed)
	    {
	      const char *hwcap_name = get_hwcap_name(hwcaps & ~hwcap_allowed);

	      as_bad (_("Hardware capability \"%s\" not enabled for \"%s\"."),
		      hwcap_name, str);
	      *pinsn = NULL;
	      return special_case;
	    }

	  // All checks passed. This is the matched instruction.
	  the_insn.opcode = current_opcode;
	  *pinsn = insn_candidate;
	  return special_case;
	}
      // If operands_match is false, loop continues to next insn_candidate
    } // end for (;; ++insn_candidate)

  // This point should not be reached if the loop correctly handles all cases (match or no more variants).
  as_fatal (_("No matching opcode variant found for `%s'"), str);
  *pinsn = NULL;
  return special_case; // Fallback
}

static char *
skip_over_keyword (char *q)
{
  if (q == NULL) {
    return NULL;
  }

  if (*q == '#' || *q == '%') {
    q++;
  }

  while (*q != '\0' && (ISALNUM (*q) || *q == '_')) {
    q++;
  }

  return q;
}

static int
parse_sparc_asi (char **input_pointer_p, const sparc_asi **value_p)
{
  if (input_pointer_p == NULL || *input_pointer_p == NULL || value_p == NULL)
    {
      return 0;
    }

  char *start_of_keyword = *input_pointer_p;
  char *end_of_keyword = skip_over_keyword(start_of_keyword);

  if (end_of_keyword == NULL || end_of_keyword == start_of_keyword)
    {
      return 0;
    }

  char saved_char = *end_of_keyword;
  *end_of_keyword = '\0';

  const sparc_asi *parsed_asi_value = sparc_encode_asi(start_of_keyword);

  *end_of_keyword = saved_char;

  if (parsed_asi_value == NULL)
    {
      return 0;
    }

  *value_p = parsed_asi_value;
  *input_pointer_p = end_of_keyword;
  return 1;
}

/* Parse an argument that can be expressed as a keyword.
   (eg: #StoreStore or %ccfr).
   The result is a boolean indicating success.
   If successful, INPUT_POINTER is updated.  */

static int
parse_keyword_arg (int (*lookup_fn) (const char *),
		   char **input_pointer_ptr,
		   int *value_ptr)
{
  char *current_input_position;
  char *end_of_keyword;
  char char_after_keyword;
  int keyword_value;

  /* Input validation: Ensure required pointers are not NULL. */
  if (lookup_fn == NULL || input_pointer_ptr == NULL || *input_pointer_ptr == NULL || value_ptr == NULL)
    {
      return 0; /* Indicate failure due to invalid input */
    }

  current_input_position = *input_pointer_ptr;
  end_of_keyword = skip_over_keyword(current_input_position);

  /* Robustness check for the result of skip_over_keyword.
   * If it returns NULL, it indicates a critical failure and dereferencing would crash.
   * Returning 0 provides a graceful failure instead of a crash. */
  if (end_of_keyword == NULL)
    {
      return 0; /* Indicate parsing failure */
    }

  /* Temporarily null-terminate the keyword string for lookup_fn. */
  char_after_keyword = *end_of_keyword;
  *end_of_keyword = '\0';

  keyword_value = (*lookup_fn) (current_input_position);

  /* Restore the original character to prevent side effects on the input string. */
  *end_of_keyword = char_after_keyword;

  if (keyword_value == -1)
    {
      return 0; /* Keyword lookup failed */
    }

  /* Update output parameters and return success. */
  *value_ptr = keyword_value;
  *input_pointer_ptr = end_of_keyword;
  return 1;
}

/* Parse an argument that is a constant expression.
   The result is a boolean indicating success.  */

static int
parse_const_expr_arg (char **input_pointerP, int *valueP)
{
  char *saved_input_ptr = input_line_pointer;
  expressionS exp;
  int result = 0;

  input_line_pointer = *input_pointerP;

  if (*input_line_pointer == '%')
    {
      goto cleanup;
    }

  expression (&exp);

  *input_pointerP = input_line_pointer;

  if (exp.X_op == O_constant)
    {
      *valueP = exp.X_add_number;
      result = 1;
    }

cleanup:
  input_line_pointer = saved_input_ptr;
  return result;
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

static int
get_expression (char *str)
{
  char *save_input_line_pointer = input_line_pointer;
  segT seg;
  int ret_val = 0;

  input_line_pointer = str;

  seg = expression (&the_insn.exp);

  if (!is_valid_segment(seg))
    {
      the_insn.error = _("bad segment");
      ret_val = 1;
    }

  expr_parse_end = input_line_pointer;
  input_line_pointer = save_input_line_pointer;

  return ret_val;
}

/* Subroutine of md_assemble to output one insn.  */

static void
output_insn (const struct sparc_opcode *insn, struct sparc_it *theinsn)
{
  const int insn_size = 4;
  char *toP = frag_more (insn_size);
  if (toP == NULL)
    return;

  if (INSN_BIG_ENDIAN)
    number_to_chars_bigendian (toP, theinsn->opcode, insn_size);
  else
    number_to_chars_littleendian (toP, theinsn->opcode, insn_size);

  if (theinsn->reloc != BFD_RELOC_NONE)
    {
      long offset = toP - frag_now->fr_literal;
      fixS *fixP =  fix_new_exp (frag_now,
				 offset,
				 insn_size,
				 &theinsn->exp,
				 theinsn->pcrel,
				 theinsn->reloc);
      if (fixP == NULL)
        return;

      fixP->fx_no_overflow = 1;
      if (theinsn->reloc == BFD_RELOC_SPARC_OLO10)
	fixP->tc_fix_data = theinsn->exp2.X_add_number;
    }

  last_insn = insn;
  last_opcode = theinsn->opcode;

  dwarf2_emit_insn (insn_size);
}

const char *
md_atof (int type, const char *litP, int *sizeP)
{
  return ieee_md_atof (type, litP, sizeP, target_big_endian);
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

void
md_number_to_chars (char *buf, valueT val, int n)
{
  int use_big_endian;

  if (target_big_endian)
    {
      use_big_endian = 1;
    }
  else if (target_little_endian_data
           && (n == 4 || n == 2)
           && !(now_seg->flags & SEC_ALLOC))
    {
      use_big_endian = 1;
    }
  else
    {
      use_big_endian = 0;
    }

  if (use_big_endian)
    {
      number_to_chars_bigendian (buf, val, n);
    }
  else
    {
      number_to_chars_littleendian (buf, val, n);
    }
}

/* Apply a fixS to the frags, now that we know the value it ought to
   hold.  */

static void
apply_sparc_nop_optimization (fixS *fixP, char *buf, long delay)
{
  long setter;
  int reg;

  if (!(fixP->fx_where >= 4
        && ((delay & (0xffffffff ^ RS1 (~0)))
            == (INSN_OR | RD (O7) | RS2 (G0)))))
    {
      return;
    }

  if (INSN_BIG_ENDIAN)
    setter = bfd_getb32 (buf - 4);
  else
    setter = bfd_getl32 (buf - 4);

  if ((setter & (0xffffffff ^ RD (~0)))
      != (INSN_OR | RS1 (O7) | RS2 (G0)))
    {
      return;
    }

  reg = (delay & RS1 (~0)) >> 14;
  if (reg != ((setter & RD (~0)) >> 25)
      || reg == G0 || reg == O7)
    {
      return;
    }

  if (INSN_BIG_ENDIAN)
    bfd_putb32 (INSN_NOP, buf + 4);
  else
    bfd_putl32 (INSN_NOP, buf + 4);
}

static void
try_optimize_sparc_call (fixS *fixP, valueT val, char *buf, long *insn_ptr)
{
  long insn = *insn_ptr;
  long delay;

  if (INSN_BIG_ENDIAN)
    delay = bfd_getb32 (buf + 4);
  else
    delay = bfd_getl32 (buf + 4);

  if ((insn & OP (~0)) != OP (1) || (delay & OP (~0)) != OP (2))
    return;
  if ((delay & OP3 (~0)) != OP3 (0x3d) /* Restore.  */
      && ((delay & OP3 (0x28)) != 0 /* Arithmetic.  */
          || ((delay & RD (~0)) != RD (O7))))
    return;
  if ((delay & RS1 (~0)) == RS1 (O7)
      || ((delay & F3I (~0)) == 0
          && (delay & RS2 (~0)) == RS2 (O7)))
    return;
  /* Ensure the branch will fit into simm22.  */
  if ((val & 0x3fe00000)
      && (val & 0x3fe00000) != 0x3fe00000)
    return;
  /* Check if the arch is v9 and branch will fit
     into simm19.  */
  if (((val & 0x3c0000) == 0
       || (val & 0x3c0000) == 0x3c0000)
      && (sparc_arch_size == 64
          || current_architecture >= SPARC_OPCODE_ARCH_V9))
    /* ba,pt %xcc  */
    insn = INSN_BPA | (val & 0x7ffff);
  else
    /* ba  */
    insn = INSN_BA | (val & 0x3fffff);

  apply_sparc_nop_optimization (fixP, buf, delay);

  *insn_ptr = insn;
}

static void
apply_instruction_relocation (fixS *fixP, valueT val, char *buf)
{
  long insn;

  if (INSN_BIG_ENDIAN)
    insn = bfd_getb32 (buf);
  else
    insn = bfd_getl32 (buf);

  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_32_PCREL_S2:
      val = val >> 2;
      /* FIXME: This increment-by-one deserves a comment of why it's
         being done!  */
      if (!sparc_pic_code
          || fixP->fx_addsy == NULL
          || symbol_section_p (fixP->fx_addsy))
        ++val;

      insn |= val & 0x3fffffff;

      /* See if we have a delay slot.  In that case we attempt to
         optimize several cases transforming CALL instructions
         into branches.  But we can only do that if the relocation
         can be completely resolved here, i.e. if no undefined
         symbol is associated with it.  */
      if (sparc_relax && fixP->fx_addsy == NULL
          && fixP->fx_where + 8 <= fixP->fx_frag->fr_fix)
        {
          try_optimize_sparc_call (fixP, val, buf, &insn);
        }
      break;

    case BFD_RELOC_SPARC_11:
      if (!in_signed_range (val, 0x7ff))
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      insn |= val & 0x7ff;
      break;

    case BFD_RELOC_SPARC_10:
      if (!in_signed_range (val, 0x3ff))
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      insn |= val & 0x3ff;
      break;

    case BFD_RELOC_SPARC_7:
      if (!in_bitfield_range (val, 0x7f))
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      insn |= val & 0x7f;
      break;

    case BFD_RELOC_SPARC_6:
      if (!in_bitfield_range (val, 0x3f))
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      insn |= val & 0x3f;
      break;

    case BFD_RELOC_SPARC_5:
      if (!in_bitfield_range (val, 0x1f))
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      insn |= val & 0x1f;
      break;

    case BFD_RELOC_SPARC_WDISP10:
      if ((val & 3)
          || val >= 0x007fc
          || val <= -(offsetT) 0x808)
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      /* FIXME: The +1 deserves a comment.  */
      val = (val >> 2) + 1;
      insn |= ((val & 0x300) << 11)
        | ((val & 0xff) << 5);
      break;

    case BFD_RELOC_SPARC_WDISP16:
      if ((val & 3)
          || val >= 0x1fffc
          || val <= -(offsetT) 0x20008)
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      /* FIXME: The +1 deserves a comment.  */
      val = (val >> 2) + 1;
      insn |= ((val & 0xc000) << 6) | (val & 0x3fff);
      break;

    case BFD_RELOC_SPARC_WDISP19:
      if ((val & 3)
          || val >= 0xffffc
          || val <= -(offsetT) 0x100008)
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      /* FIXME: The +1 deserves a comment.  */
      val = (val >> 2) + 1;
      insn |= val & 0x7ffff;
      break;

    case BFD_RELOC_SPARC_HH22:
      val = BSR (val, 32);
      /* Fall through.  */

    case BFD_RELOC_SPARC_LM22:
    case BFD_RELOC_HI22:
      if (!fixP->fx_addsy)
        insn |= (val >> 10) & 0x3fffff;
      else
        /* FIXME: Need comment explaining why we do this.  */
        insn &= ~0xffff;
      break;

    case BFD_RELOC_SPARC22:
      if (val & ~0x003fffff)
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      insn |= (val & 0x3fffff);
      break;

    case BFD_RELOC_SPARC_HM10:
      val = BSR (val, 32);
      /* Fall through.  */

    case BFD_RELOC_LO10:
      if (!fixP->fx_addsy)
        insn |= val & 0x3ff;
      else
        /* FIXME: Need comment explaining why we do this.  */
        insn &= ~0xff;
      break;

    case BFD_RELOC_SPARC_OLO10:
      val &= 0x3ff;
      val += fixP->tc_fix_data;
      /* Fall through.  */

    case BFD_RELOC_SPARC13:
      if (!in_signed_range (val, 0x1fff))
        as_bad_where (fixP->fx_file, fixP->fx_line,
                      _("relocation overflow"));
      insn |= val & 0x1fff;
      break;

    case BFD_RELOC_SPARC_WDISP22:
      val = (val >> 2) + 1;
      /* Fall through.  */
    case BFD_RELOC_SPARC_BASE22:
      insn |= val & 0x3fffff;
      break;

    case BFD_RELOC_SPARC_H34:
      if (!fixP->fx_addsy)
        {
          bfd_vma tval = val;
          tval >>= 12;
          insn |= tval & 0x3fffff;
        }
      break;

    case BFD_RELOC_SPARC_H44:
      if (!fixP->fx_addsy)
        {
          bfd_vma tval = val;
          tval >>= 22;
          insn |= tval & 0x3fffff;
        }
      break;

    case BFD_RELOC_SPARC_M44:
      if (!fixP->fx_addsy)
        insn |= (val >> 12) & 0x3ff;
      break;

    case BFD_RELOC_SPARC_L44:
      if (!fixP->fx_addsy)
        insn |= val & 0xfff;
      break;

    case BFD_RELOC_SPARC_HIX22:
      if (!fixP->fx_addsy)
        {
          val ^= ~(offsetT) 0;
          insn |= (val >> 10) & 0x3fffff;
        }
      break;

    case BFD_RELOC_SPARC_LOX10:
      if (!fixP->fx_addsy)
        insn |= 0x1c00 | (val & 0x3ff);
      break;

    case BFD_RELOC_NONE:
    default:
      as_bad_where (fixP->fx_file, fixP->fx_line,
                    _("bad or unhandled relocation type: 0x%02x"),
                    fixP->fx_r_type);
      break;
    }

  if (INSN_BIG_ENDIAN)
    bfd_putb32 (insn, buf);
  else
    bfd_putl32 (insn, buf);
}

static int
apply_data_relocation (fixS *fixP, valueT val, char *buf)
{
  if (fixP->fx_r_type == BFD_RELOC_8)
    {
      md_number_to_chars (buf, val, 1);
      return 1;
    }
  else if (fixP->fx_r_type == BFD_RELOC_16
           || fixP->fx_r_type == BFD_RELOC_SPARC_UA16)
    {
      md_number_to_chars (buf, val, 2);
      return 1;
    }
  else if (fixP->fx_r_type == BFD_RELOC_32
           || fixP->fx_r_type == BFD_RELOC_SPARC_UA32
           || fixP->fx_r_type == BFD_RELOC_SPARC_REV32)
    {
      md_number_to_chars (buf, val, 4);
      return 1;
    }
  else if (fixP->fx_r_type == BFD_RELOC_64
           || fixP->fx_r_type == BFD_RELOC_SPARC_UA64)
    {
      md_number_to_chars (buf, val, 8);
      return 1;
    }
  else if (fixP->fx_r_type == BFD_RELOC_VTABLE_INHERIT
           || fixP->fx_r_type == BFD_RELOC_VTABLE_ENTRY)
    {
      fixP->fx_done = 0;
      return 1; /* Relocation handled (no data written, just fx_done set). */
    }
  return 0; /* Not a recognized data relocation type. */
}

void
md_apply_fix (fixS *fixP, valueT *valP, segT segment ATTRIBUTE_UNUSED)
{
  char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
  offsetT val = *valP;

  gas_assert (fixP->fx_r_type < BFD_RELOC_UNUSED);

  fixP->fx_addnumber = val;   /* Remember value for emit_reloc.  */

  /* SPARC ELF relocations don't use an addend in the data field.  */
  if (fixP->fx_addsy != NULL)
    {
      switch (fixP->fx_r_type)
        {
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
          S_SET_THREAD_LOCAL (fixP->fx_addsy);
          break; /* Break from switch; the function returns immediately after. */
        default:
          break; /* Break from switch; the function returns immediately after. */
        }
      return; /* Unconditionally return if fixP->fx_addsy is not NULL. */
    }

  /* This is a hack.  There should be a better way to
     handle this.  Probably in terms of howto fields, once
     we can look at these fixups in terms of howtos.  */
  /* Note: The condition `fixP->fx_addsy` here is unreachable due to the
     preceding `if (fixP->fx_addsy != NULL)` block. Preserving original logic. */
  if (fixP->fx_r_type == BFD_RELOC_32_PCREL_S2 && fixP->fx_addsy)
    val += fixP->fx_where + fixP->fx_frag->fr_address;

  /* If this is a data relocation, just output VAL.  */
  if (apply_data_relocation (fixP, val, buf))
    {
      return;
    }
  else
    {
      /* It's an instruction relocation.  */
      apply_instruction_relocation (fixP, val, buf);
    }

  /* Are we finished with this relocation now?  */
  if (fixP->fx_addsy == 0 && !fixP->fx_pcrel)
    fixP->fx_done = 1;
}

/* Translate internal representation of relocation info to BFD target
   format.  */

static inline bool is_addend_offset_or_section_relative(bfd_reloc_code_real_type code)
{
  switch (code)
    {
    case BFD_RELOC_32_PCREL_S2:
    case BFD_RELOC_SPARC_WDISP22:
    case BFD_RELOC_SPARC_WDISP16:
    case BFD_RELOC_SPARC_WDISP19:
    case BFD_RELOC_SPARC_WDISP10:
    case BFD_RELOC_SPARC_WPLT30:
    case BFD_RELOC_SPARC_TLS_GD_CALL:
    case BFD_RELOC_SPARC_TLS_LDM_CALL:
      return true;
    default:
      return false;
    }
}

arelent **
tc_gen_reloc (asection *section, fixS *fixp)
{
  static arelent *relocs[3];
  arelent *reloc;
  bfd_reloc_code_real_type code;

  // Initialize return array pointers to NULL for a clean state and error signaling.
  relocs[0] = NULL;
  relocs[1] = NULL;
  relocs[2] = NULL;

  reloc = notes_alloc (sizeof (arelent));
  if (reloc == NULL) {
      // Memory allocation failed for the first relocation entry.
      // Signal error by returning the static array with its first element as NULL.
      return relocs;
  }
  relocs[0] = reloc;

  reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
  if (reloc->sym_ptr_ptr == NULL) {
      // Memory allocation failed for symbol pointer.
      relocs[0] = NULL; // Invalidate the primary relocation entry
      return relocs;
  }
  *reloc->sym_ptr_ptr = symbol_get_bfdsym (fixp->fx_addsy);
  reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;

  code = fixp->fx_r_type; // Initialize 'code' with the original relocation type

  // Determine the final relocation 'code' based on the original type and specific conditions.
  // This switch also implicitly validates 'fixp->fx_r_type' against known types.
  switch (fixp->fx_r_type)
    {
    case BFD_RELOC_8:
    case BFD_RELOC_16:
    case BFD_RELOC_32:
    case BFD_RELOC_64:
      if (fixp->fx_pcrel)
	{
	  switch (fixp->fx_size)
	    {
	    case 1: code = BFD_RELOC_8_PCREL;  break;
	    case 2: code = BFD_RELOC_16_PCREL; break;
	    case 4: code = BFD_RELOC_32_PCREL; break;
#ifdef BFD64
	    case 8: code = BFD_RELOC_64_PCREL; break;
#endif
	    default:
	      // Unhandled PC-relative size, report error and disable PC-relative processing.
	      as_bad_where (fixp->fx_file, fixp->fx_line,
			    _("can not do %d byte pc-relative relocation"),
			    fixp->fx_size);
	      fixp->fx_pcrel = 0;
	      break;
	    }
	  // Only apply fx_addnumber if PC-relative processing was valid and enabled.
	  if (fixp->fx_pcrel)
	    fixp->fx_addnumber = fixp->fx_offset;
	}
      break; // Processing complete for these types, no fall-through.

    // These cases validate 'fixp->fx_r_type' as a known type without altering 'code',
    // as 'code' was already initialized to 'fixp->fx_r_type'.
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
    case BFD_RELOC_M44:
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
      // Code is already set, no further action required for these types.
      break;

    default:
      // If the original type is not in the recognized list, it's an unhandled internal error.
      as_bad_where (fixp->fx_file, fixp->fx_line,
		    _("internal error: unhandled original relocation type %d"),
		    (int) fixp->fx_r_type);
      relocs[0] = NULL; // Signal error
      return relocs;
    }

  // If generating PIC code, further transform 'code' based on specific rules.
#define GOT_NAME "_GLOBAL_OFFSET_TABLE_"
#ifdef TE_VXWORKS
#define GOTT_BASE "__GOTT_BASE__"
#define GOTT_INDEX "__GOTT_INDEX__"
#endif

  if (sparc_pic_code)
    {
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
    }

  // Adjust relocation types for DWARF debugging sections.
  if (bfd_section_flags (section) & SEC_DEBUGGING)
    {
      switch (code)
	{
	case BFD_RELOC_16: code = BFD_RELOC_SPARC_UA16; break;
	case BFD_RELOC_32: code = BFD_RELOC_SPARC_UA32; break;
	case BFD_RELOC_64: code = BFD_RELOC_SPARC_UA64; break;
	default: break;
	}
    }

  // Look up the final relocation 'howto' type.
  // R_SPARC_OLO10 maps to R_SPARC_LO10 for its 'howto' field.
  if (code == BFD_RELOC_SPARC_OLO10)
    reloc->howto = bfd_reloc_type_lookup (stdoutput, BFD_RELOC_LO10);
  else
    reloc->howto = bfd_reloc_type_lookup (stdoutput, code);

  if (reloc->howto == NULL) // bfd_reloc_type_lookup returns 0 (NULL) on failure
    {
      as_bad_where (fixp->fx_file, fixp->fx_line,
		    _("internal error: can't export reloc type %d (`%s')"),
		    fixp->fx_r_type, bfd_get_reloc_code_name (code));
      relocs[0] = NULL; // Signal error
      return relocs;
    }

  // Determine the addend value based on the final relocation 'code' and symbol information.
  if (is_addend_offset_or_section_relative(code))
    {
      if (symbol_section_p (fixp->fx_addsy))
	reloc->addend = (section->vma
		     + fixp->fx_addnumber
		     + md_pcrel_from (fixp));
      else
	reloc->addend = fixp->fx_offset;
    }
  else
    reloc->addend = fixp->fx_addnumber;

  // Handle the special case for BFD_RELOC_SPARC_OLO10, which requires a second relocation entry.
  if (code == BFD_RELOC_SPARC_OLO10)
    {
      arelent *second_reloc = notes_alloc (sizeof (arelent));
      if (second_reloc == NULL) {
          relocs[0] = NULL; // If secondary alloc fails, invalidate the primary entry.
          return relocs;
      }
      relocs[1] = second_reloc; // Store the second allocated reloc.
      relocs[2] = NULL; // Ensure null termination for the list.

      second_reloc->sym_ptr_ptr = notes_alloc (sizeof (asymbol *));
      if (second_reloc->sym_ptr_ptr == NULL) {
          relocs[0] = NULL; // Invalidate primary
          relocs[1] = NULL; // Invalidate secondary
          return relocs;
      }
      *second_reloc->sym_ptr_ptr
	= symbol_get_bfdsym (section_symbol (absolute_section));
      second_reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;
      second_reloc->howto = bfd_reloc_type_lookup (stdoutput, BFD_RELOC_SPARC13);
      // Original code assumes bfd_reloc_type_lookup for BFD_RELOC_SPARC13 does not fail.
      second_reloc->addend = fixp->tc_fix_data;
    }

  return relocs;
}

/* We have no need to default values of symbols.  */

symbolS *
md_undefined_symbol (const char *name ATTRIBUTE_UNUSED)
{
  return NULL;
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment, valueT size)
{
  (void)segment;
  return size;
}

/* Exactly what point is a PC-relative offset relative TO?
   On the sparc, they're relative to the address of the offset, plus
   its size.  This gets us to the following instruction.
   (??? Is this right?  FIXME-SOON)  */
long
md_pcrel_from (fixS *fixP)
{
  long result = fixP->fx_where + fixP->fx_frag->fr_address;

  _Bool apply_size_adjustment =
      !sparc_pic_code || fixP->fx_addsy == NULL || symbol_section_p(fixP->fx_addsy);

  if (apply_size_adjustment) {
    result += fixP->fx_size;
  }

  return result;
}

/* Return log2 (VALUE), or -1 if VALUE is not an exact positive power
   of two.  */

static int
mylog2 (int value)
{
  if (value <= 0) {
    return -1;
  }

  if ((value & (value - 1)) != 0) {
    return -1;
  }

  int shift = 0;
  for (shift = 0; (value & 1) == 0; value >>= 1) {
    ++shift;
  }

  return shift;
}

/* Sort of like s_lcomm.  */

static void
s_reserve (int ignore ATTRIBUTE_UNUSED)
{
  char *symbol_name;
  char *name_delimiter_ptr;
  char original_char_at_delimiter;
  int alignment = 0;
  int size_in_bytes;
  symbolS *symbol_entry_ptr;

  // 1. Parse the symbol name.
  // `get_symbol_name` is assumed to set `symbol_name`, advance `input_line_pointer`
  // to the delimiter character *after* the name, and return that delimiter character.
  original_char_at_delimiter = get_symbol_name (&symbol_name);
  name_delimiter_ptr = input_line_pointer; // `name_delimiter_ptr` points to the character after the name.

  // The sequence `restore_line_pointer` then `SKIP_WHITESPACE` is common in the assembler.
  // It is assumed to correctly position `input_line_pointer` at the comma *after* the symbol name,
  // before parsing the size expression, as inferred from the subsequent `if` condition.
  restore_line_pointer (original_char_at_delimiter);
  SKIP_WHITESPACE ();

  // 2. Expect a comma after the symbol name.
  if (*input_line_pointer != ',')
    {
      as_bad (_("Expected comma after symbol name"));
      ignore_rest_of_line ();
      return;
    }

  ++input_line_pointer; // Consume the comma.
  SKIP_WHITESPACE ();

  // 3. Parse the size expression.
  if ((size_in_bytes = get_absolute_expression ()) < 0)
    {
      as_bad (_("BSS length (%d) cannot be negative. Ignored."), size_in_bytes);
      ignore_rest_of_line ();
      return;
    }

  // Temporarily null-terminate the symbol name for `symbol_find_or_make`.
  *name_delimiter_ptr = 0;
  symbol_entry_ptr = symbol_find_or_make (symbol_name);
  *name_delimiter_ptr = original_char_at_delimiter; // Restore the original delimiter character.

  SKIP_WHITESPACE ();

  // 4. Expect the segment specifier (",\"bss\"" or ",\".bss\"").
  // The `startswith` function checks for the full string including the leading comma.
  if (!startswith (input_line_pointer, ",\"bss\"") && !startswith (input_line_pointer, ",\".bss\""))
    {
      as_bad (_("Bad .reserve segment -- expected \",\"bss\"\" or \",\".bss\"\""));
      ignore_rest_of_line ();
      return;
    }

  // Advance `input_line_pointer` past the segment string.
  // `input_line_pointer[2]` correctly distinguishes `,".bss"` from `,"bss"`.
  if (input_line_pointer[2] == '.') // Checks for `.` in `,".bss"`
    input_line_pointer += (sizeof (",\".bss\"") - 1); // Advance past ",\".bss\"" (7 characters)
  else // Must be `,"bss"`
    input_line_pointer += (sizeof (",\"bss\"") - 1); // Advance past ",\"bss\"" (6 characters)
  
  SKIP_WHITESPACE ();

  // 5. Parse optional alignment.
  if (*input_line_pointer == ',')
    {
      ++input_line_pointer; // Consume the comma.
      SKIP_WHITESPACE ();

      if (*input_line_pointer == '\n' || *input_line_pointer == '\0')
	{
	  as_bad (_("Missing alignment expression after comma"));
	  ignore_rest_of_line ();
	  return;
	}

      alignment = (int) get_absolute_expression ();

      if (alignment < 0)
	{
	  as_bad (_("Alignment value cannot be negative"));
	  ignore_rest_of_line ();
	  return;
	}

      if (alignment != 0)
	{
	  int log2_result = mylog2 (alignment);
	  if (log2_result < 0)
	    {
	      as_bad (_("Alignment must be a power of 2 (received %d)"), alignment);
	      ignore_rest_of_line ();
	      return;
	    }
	  alignment = log2_result; // Store log2 value as the internal alignment representation.
	}

      record_alignment (bss_section, alignment);
    }

  // 6. Define or warn about the symbol.
  if (!S_IS_DEFINED (symbol_entry_ptr))
    {
      if (! need_pass_2)
	{
	  segT current_seg_backup = now_seg;
	  subsegT current_subseg_backup = now_subseg;

	  // Switch to BSS section for symbol definition.
	  subseg_set (bss_section, 1);

	  if (alignment)
	    frag_align (alignment, 0, 0); // Apply alignment if specified.

	  // If the symbol was already associated with the bss section,
	  // ensure its old fragment reference is cleared to avoid dangling pointers.
	  if (S_GET_SEGMENT (symbol_entry_ptr) == bss_section)
	    symbol_get_frag (symbol_entry_ptr)->fr_symbol = NULL;

	  // Associate the symbol with the current fragment.
	  symbol_set_frag (symbol_entry_ptr, frag_now);
	  char *allocated_fragment_data_ptr = frag_var (rs_org, 1, 1, 0, symbol_entry_ptr, size_in_bytes, NULL);
	  *allocated_fragment_data_ptr = 0; // Initialize first byte of reserved memory to 0.

	  S_SET_SEGMENT (symbol_entry_ptr, bss_section);

	  // Restore previous segment context.
	  subseg_set (current_seg_backup, current_subseg_backup);

	  S_SET_SIZE (symbol_entry_ptr, size_in_bytes);
	}
    }
  else
    {
      // Warn if attempting to redefine an existing symbol.
      as_warn (_("Ignoring attempt to re-define symbol \"%s\""),
	       S_GET_NAME (symbol_entry_ptr));
    }

  // Ensure the rest of the line is empty.
  demand_empty_rest_of_line ();
}

static void
s_common (int ignore ATTRIBUTE_UNUSED)
{
  char *name = NULL;
  char char_after_name;
  char *ptr_after_name_in_input_line;
  offsetT size = 0;
  symbolS *symbolP = NULL;
  offsetT alignment_val = 0;
  int parsed_segment_string = 0; // Flag: 1 if alignment was a string like "bss", 0 if it was an expression

  char_after_name = get_symbol_name (&name);
  if (name == NULL || *name == '\0') {
      as_bad (_("Invalid or empty symbol name provided for .common directive."));
      ignore_rest_of_line ();
      return;
  }

  ptr_after_name_in_input_line = input_line_pointer;
  restore_line_pointer (char_after_name);
  SKIP_WHITESPACE ();

  if (*input_line_pointer != ',')
    {
      as_bad (_("Expected comma after symbol-name '%s' in .common directive."), name);
      ignore_rest_of_line ();
      return;
    }
  input_line_pointer++;
  SKIP_WHITESPACE ();

  size = get_absolute_expression ();
  if (size < 0)
    {
      as_bad (_(".COMMon length (%ld) out of range or invalid expression for symbol '%s'."), (long) size, name);
      ignore_rest_of_line ();
      return;
    }

  // Temporarily null-terminate the name string for symbol lookup, then restore the character.
  // This pattern assumes `name` points into `input_line_buffer`.
  *ptr_after_name_in_input_line = 0;
  symbolP = symbol_find_or_make (name);
  *ptr_after_name_in_input_line = char_after_name;

  if (symbolP == NULL) {
      as_bad (_("Internal error: Failed to create or find symbol '%s'."), name);
      ignore_rest_of_line ();
      return;
  }

  if (S_IS_DEFINED (symbolP) && !S_IS_COMMON (symbolP))
    {
      as_bad (_("Ignoring attempt to re-define symbol '%s' as .common, already defined elsewhere."), S_GET_NAME (symbolP));
      ignore_rest_of_line ();
      return;
    }

  if (S_GET_VALUE (symbolP) != 0)
    {
      if (S_GET_VALUE (symbolP) != (valueT) size)
	{
	  as_warn (_("Length of .comm \"%s\" is already %ld. Not changed to %ld."),
		   S_GET_NAME (symbolP), (long) S_GET_VALUE (symbolP), (long) size);
	}
    }
  know (symbol_get_frag (symbolP) == &zero_address_frag);

  SKIP_WHITESPACE ();

  if (*input_line_pointer != ',')
    {
      as_bad (_("Expected comma after common length for symbol '%s'."), S_GET_NAME (symbolP));
      ignore_rest_of_line ();
      return;
    }
  input_line_pointer++;
  SKIP_WHITESPACE ();

  if (*input_line_pointer == '"') // Segment name specified (e.g., "bss", "data")
    {
      parsed_segment_string = 1;
      input_line_pointer++; // Skip initial '"'
      char *segment_name_start_in_line = input_line_pointer;
      char *scan_ptr = input_line_pointer;

      if (*scan_ptr == '.')
	scan_ptr++;

      if (startswith (scan_ptr, "bss\""))
	{
	  input_line_pointer += (scan_ptr - input_line_pointer) + 4; // Advance past "bss\"" and any preceding '.'
	}
      else if (startswith (scan_ptr, "data\""))
	{
	  input_line_pointer += (scan_ptr - input_line_pointer) + 5; // Advance past "data\"" and any preceding '.'
	}
      else
	{
	  char *end_of_segment_name = segment_name_start_in_line;
	  while (*end_of_segment_name && *end_of_segment_name != '"' && *end_of_segment_name != '\n')
	    end_of_segment_name++;

	  char saved_char = *end_of_segment_name;
	  *end_of_segment_name = '\0'; // Temporarily null-terminate for error message
	  as_bad (_("Bad .common segment string '%s' for symbol '%s'."), segment_name_start_in_line, S_GET_NAME (symbolP));
	  *end_of_segment_name = saved_char; // Restore
	  ignore_rest_of_line ();
	  return;
	}
      alignment_val = 0; // For string-specified common, alignment is implicitly 0 or handled by bfd.
    }
  else // Alignment is an expression (e.g., .common foo, 16, 4)
    {
      alignment_val = get_absolute_expression ();

      if (alignment_val < 0)
	{
	  as_bad (_("Negative alignment value %ld for symbol '%s'."), (long)alignment_val, S_GET_NAME (symbolP));
	  ignore_rest_of_line ();
	  return;
	}
    }

  // Determine if this is a local or external common allocation.
  // External if symbol is not local, or if segment was explicitly specified as a string.
  int is_symbol_local = symbol_get_obj (symbolP)->local;

  if (!is_symbol_local || parsed_segment_string)
    {
      // External common allocation
      S_SET_VALUE (symbolP, size);
      S_SET_ALIGN (symbolP, alignment_val);
      S_SET_SIZE (symbolP, size);
      S_SET_EXTERNAL (symbolP);
      S_SET_SEGMENT (symbolP, bfd_com_section_ptr);
    }
  else
    {
      // Local common allocation
      segT old_sec;
      int old_subsec;
      int align_log2;

      old_sec = now_seg;
      old_subsec = now_subseg;

      if (alignment_val == 0)
	align_log2 = 0;
      else
	align_log2 = mylog2 (alignment_val);

      if (align_log2 < 0)
	{
	  as_bad (_("Alignment value %ld for symbol '%s' is not a power of 2."), (long)alignment_val, S_GET_NAME (symbolP));
	  ignore_rest_of_line ();
	  return;
	}

      record_alignment (bss_section, align_log2);
      subseg_set (bss_section, 0);
      if (align_log2)
	frag_align (align_log2, 0, 0);

      if (S_GET_SEGMENT (symbolP) == bss_section)
	symbol_get_frag (symbolP)->fr_symbol = 0;

      symbol_set_frag (symbolP, frag_now);

      char *frag_data_ptr = frag_var (rs_org, 1, 1, 0, symbolP, size, NULL);
      *frag_data_ptr = 0;

      S_SET_SEGMENT (symbolP, bss_section);
      S_CLEAR_EXTERNAL (symbolP);
      S_SET_SIZE (symbolP, size);

      subseg_set (old_sec, old_subsec);
    }

  symbol_get_bfdsym (symbolP)->flags |= BSF_OBJECT;

  demand_empty_rest_of_line ();
}

/* Handle the .empty pseudo-op.  This suppresses the warnings about
   invalid delay slot usage.  */

static void
s_empty (int ignore)
{
  (void)ignore;
  last_insn = NULL;
}

#ifndef ATTRIBUTE_UNUSED
# ifdef __GNUC__
#  define ATTRIBUTE_UNUSED __attribute__((__unused__))
# else
#  define ATTRIBUTE_UNUSED
# endif
#endif

#define ADVANCE_IF_STARTS_WITH(needle_str, len) \
    (startswith(input_line_pointer, (needle_str)) ? \
     (input_line_pointer += (len), 1) : 0)

static void
s_seg (int ignore ATTRIBUTE_UNUSED)
{
  const int TEXT_SEGMENT_LEN = 6;
  const int DATA_SEGMENT_LEN = 6;
  const int DATA1_SEGMENT_LEN = 7;
  const int BSS_SEGMENT_LEN = 5;

  const int BSS_SUBSEGMENT_ID = 255;

  if (ADVANCE_IF_STARTS_WITH("\"text\"", TEXT_SEGMENT_LEN))
    {
      s_text (0);
      return;
    }
  if (ADVANCE_IF_STARTS_WITH("\"data\"", DATA_SEGMENT_LEN))
    {
      s_data (0);
      return;
    }
  if (ADVANCE_IF_STARTS_WITH("\"data1\"", DATA1_SEGMENT_LEN))
    {
      s_data1 ();
      return;
    }
  if (ADVANCE_IF_STARTS_WITH("\"bss\"", BSS_SEGMENT_LEN))
    {
      /* We only support 2 segments -- text and data -- for now, so
	 things in the "bss segment" will have to go into data for now.
	 You can still allocate SEG_BSS stuff with .lcomm or .reserve.  */
      subseg_set (data_section, BSS_SUBSEGMENT_ID);	/* FIXME-SOMEDAY.  */
      return;
    }
  as_bad (_("Unknown segment type"));
  demand_empty_rest_of_line ();
}

#define DATA_SECTION_SUBSEGMENT_INDEX 1

static void
s_data1 (void)
{
  subseg_set (data_section, DATA_SECTION_SUBSEGMENT_INDEX);
  demand_empty_rest_of_line ();
}

static void
s_proc (int ignore ATTRIBUTE_UNUSED)
{
  if (input_line_pointer == NULL)
    {
      return; /* Handle null pointer defensively */
    }

  /* Advance the pointer until an end-of-statement character is found,
   * or the end of the string (null terminator) is reached,
   * preventing potential buffer overruns. */
  while (*input_line_pointer != '\0' && !is_end_of_stmt (*input_line_pointer))
    {
      ++input_line_pointer;
    }

  /* After the loop, if the pointer is not at the null terminator,
   * it means it's currently pointing at the end-of-statement character.
   * In this case, advance it one more time to move past the EOS.
   * If it's already at the null terminator, do not advance further
   * to maintain string integrity and prevent reading out of bounds. */
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
  /* Temporarily disable console alignment. */
  sparc_no_align_cons = 1;

  /* Call the core console function. */
  cons (bytes);

  /* Re-enable console alignment. */
  sparc_no_align_cons = 0;
}

/* This handles the native word allocation pseudo-op .nword.
   For sparc_arch_size 32 it is equivalent to .word,  for
   sparc_arch_size 64 it is equivalent to .xword.  */

#ifndef SPARC_ARCHITECTURE_32_BIT
#define SPARC_ARCHITECTURE_32_BIT 32
#endif

#ifndef CONSOLE_ARG_FOR_32_BIT_ARCH
#define CONSOLE_ARG_FOR_32_BIT_ARCH 4
#endif

#ifndef CONSOLE_ARG_FOR_64_BIT_ARCH
#define CONSOLE_ARG_FOR_64_BIT_ARCH 8
#endif

static void
s_ncons (int bytes ATTRIBUTE_UNUSED)
{
  cons(sparc_arch_size == SPARC_ARCHITECTURE_32_BIT ? CONSOLE_ARG_FOR_32_BIT_ARCH : CONSOLE_ARG_FOR_64_BIT_ARCH);
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
  char *regname_str = NULL;
  bool is_scratch_def = false;
  bool is_ignore_def = false;

  // 1. Input Validation and Register Extraction
  // Check for "%g[2367],"
  if (input_line_pointer[0] != '%' ||
      input_line_pointer[1] != 'g' ||
      (input_line_pointer[2] != '2' && input_line_pointer[2] != '3' &&
       input_line_pointer[2] != '6' && input_line_pointer[2] != '7') ||
      input_line_pointer[3] != ',')
    {
      as_bad (_("register syntax is .register %%g[2367],{#scratch|symbolname|#ignore}"));
      return;
    }

  reg = input_line_pointer[2] - '0';
  input_line_pointer += 4; // Advance past "%gX,"

  // 2. Determine Register Definition Type
  if (*input_line_pointer == '#')
    {
      ++input_line_pointer;
      c = get_symbol_name (&regname_str);
      // Validate that regname_str is "scratch" or "ignore"
      if (regname_str == NULL || (strcmp (regname_str, "scratch") != 0 && strcmp (regname_str, "ignore") != 0))
        {
          as_bad (_("register syntax is .register %%g[2367],{#scratch|symbolname|#ignore}"));
          (void) restore_line_pointer (c);
          return;
        }

      if (strcmp (regname_str, "ignore") == 0)
        {
          is_ignore_def = true;
        }
      else // strcmp (regname_str, "scratch") == 0
        {
          is_scratch_def = true;
        }
    }
  else
    {
      // A regular symbol name
      c = get_symbol_name (&regname_str);
      // A named symbol must have a non-empty name
      if (regname_str == NULL || *regname_str == '\0')
        {
            as_bad(_("missing symbol name for register definition"));
            (void) restore_line_pointer(c);
            return;
        }
    }

  // Early exit for 32-bit architecture if it's not supported by this block.
  // The original code has an empty body for sparc_arch_size != 64.
  // We still need to restore the line pointer and demand empty line.
  if (sparc_arch_size != 64)
    {
      (void) restore_line_pointer (c);
      demand_empty_rest_of_line ();
      return;
    }

  // 3. Handle 64-bit Register Definition/Redefinition
  symbolS *current_global_def = globals[reg];

  if (current_global_def != NULL) // If something is already defined (scratch, ignore, or named symbol)
    {
      // Check if current definition matches new definition
      bool redefinition_mismatch = false;

      if (current_global_def == (symbolS *) 1) // Old definition was #scratch
        {
          if (!is_scratch_def) redefinition_mismatch = true;
        }
      else if (current_global_def == (symbolS *) 2) // Old definition was #ignore (new sentinel value)
        {
          if (!is_ignore_def) redefinition_mismatch = true;
        }
      else // Old definition was a named symbol (current_global_def is a real symbolS*)
        {
          // New definition must also be a named symbol with the exact same name
          if (is_scratch_def || is_ignore_def || strcmp(S_GET_NAME(current_global_def), regname_str) != 0)
            redefinition_mismatch = true;
        }

      if (redefinition_mismatch)
        {
          as_bad (_("redefinition of global register"));
          (void) restore_line_pointer (c);
          return;
        }
      // If the new definition matches the existing one, it's a no-op.
    }
  else // Register not yet defined (globals[reg] is NULL)
    {
      if (is_ignore_def)
        {
          globals[reg] = (symbolS *) 2; // Set to #ignore sentinel
        }
      else if (is_scratch_def)
        {
          globals[reg] = (symbolS *) 1; // Set to #scratch sentinel
        }
      else // Named symbol (is_new_reg_symbol is true and regname_str is valid)
        {
          // Check if symbol already exists to prevent redefinition errors
          if (symbol_find (regname_str))
            {
              as_bad (_("Register symbol %s already defined."), regname_str);
              (void) restore_line_pointer (c);
              return;
            }

          symbolS *sym = symbol_make (regname_str);
          globals[reg] = sym;

          bfd_symbol *bsym = symbol_get_bfdsym (sym);
          int flags = bsym->flags;

          // Ensure it's marked as global if no other linkage is specified
          if (! (flags & (BSF_GLOBAL|BSF_LOCAL|BSF_WEAK)))
            flags |= BSF_GLOBAL;
          bsym->flags = flags;

          S_SET_VALUE (sym, reg);
          S_SET_ALIGN (sym, reg);
          S_SET_SIZE (sym, 0);
          S_SET_SEGMENT (sym, absolute_section);
          S_SET_OTHER (sym, 0);

          Elf_Internal_Sym *elf_isym = &elf_symbol(bsym)->internal_elf_sym;
          elf_isym->st_info = ELF_ST_INFO(STB_GLOBAL, STT_REGISTER);
          elf_isym->st_shndx = SHN_UNDEF;
        }
    }

  // 4. Clean up
  (void) restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

/* Adjust the symbol table.  We set undefined sections for STT_REGISTER
   symbols which need it.  */

void
sparc_adjust_symtab (void)
{
  symbolS *sym;

  for (sym = symbol_rootP; sym != NULL; sym = symbol_next (sym))
    {
      struct elf_internal_sym *elf_sym;

      elf_sym = elf_symbol (symbol_get_bfdsym (sym));

      if (ELF_ST_TYPE (elf_sym->st_info) == STT_REGISTER &&
          elf_sym->st_shndx == SHN_UNDEF)
        {
          S_SET_SEGMENT (sym, undefined_section);
        }
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

void
sparc_cons_align (int nbytes)
{
  int nalign;

  if (!enforce_aligned_data)
    return;

  if (sparc_no_align_cons)
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

static inline void write_word_endian_4bytes(char *ptr, unsigned int val)
{
  if (INSN_BIG_ENDIAN)
    number_to_chars_bigendian(ptr, val, 4);
  else
    number_to_chars_littleendian(ptr, val, 4);
}

void
sparc_handle_align (fragS *fragp)
{
  int padding_needed_bytes;
  char *current_write_ptr;
  int bytes_added_to_fr_fix;

  padding_needed_bytes = fragp->fr_next->fr_address - fragp->fr_address - fragp->fr_fix;

  switch (fragp->fr_type)
    {
    case rs_align_test:
      if (padding_needed_bytes != 0)
	as_bad_where(fragp->fr_file, fragp->fr_line, _("misaligned data"));
      break;

    case rs_align_code:
      current_write_ptr = fragp->fr_literal + fragp->fr_fix;
      bytes_added_to_fr_fix = 0;

      int initial_align_padding = padding_needed_bytes & 3;
      if (initial_align_padding != 0)
	{
	  memset(current_write_ptr, 0, initial_align_padding);
	  current_write_ptr += initial_align_padding;
	  padding_needed_bytes -= initial_align_padding;
	  bytes_added_to_fr_fix += initial_align_padding;
	}

      if (SPARC_OPCODE_ARCH_V9_P(max_architecture) && padding_needed_bytes > 8)
	{
	  unsigned int branch_instruction_word = (0x30680000 | (unsigned int)padding_needed_bytes >> 2);
	  write_word_endian_4bytes(current_write_ptr, branch_instruction_word);
	  current_write_ptr += 4;
	  padding_needed_bytes -= 4;
	  bytes_added_to_fr_fix += 4;
	}

      write_word_endian_4bytes(current_write_ptr, 0x01000000);

      fragp->fr_fix += bytes_added_to_fr_fix;
      fragp->fr_var = 4;
      break;

    default:
      break;
    }
}

/* Some special processing for a Sparc ELF file.  */

void
sparc_elf_final_processing (void)
{
  Elf_Internal_Ehdr *ehdr = elf_elfheader (stdoutput);

  if (ehdr == NULL)
    {
      return;
    }

  if (sparc_arch_size == 64)
    {
      switch (sparc_memory_model)
	{
	case MM_RMO:
	  ehdr->e_flags |= EF_SPARCV9_RMO;
	  break;
	case MM_PSO:
	  ehdr->e_flags |= EF_SPARCV9_PSO;
	  break;
	}
    }
  else if (current_architecture >= SPARC_OPCODE_ARCH_V9)
    {
      ehdr->e_flags |= EF_SPARC_32PLUS;
    }

  if (current_architecture == SPARC_OPCODE_ARCH_V9A)
    {
      ehdr->e_flags |= EF_SPARC_SUN_US1;
    }
  else if (current_architecture == SPARC_OPCODE_ARCH_V9B)
    {
      ehdr->e_flags |= EF_SPARC_SUN_US1|EF_SPARC_SUN_US3;
    }
}

const char *
sparc_cons (expressionS *exp, int size)
{
  char *save_input_ptr;
  const char *special_relocation_type = NULL;
  bool special_reloc_fully_parsed = false;

  SKIP_WHITESPACE ();
  save_input_ptr = input_line_pointer;

  if (input_line_pointer[0] == '%' && input_line_pointer[1] == 'r' && input_line_pointer[2] == '_')
    {
      input_line_pointer += 3;

      if (startswith (input_line_pointer, "disp"))
        {
          input_line_pointer += 4;
          special_relocation_type = "disp";
        }
      else if (startswith (input_line_pointer, "plt"))
        {
          if (size != 4 && size != 8)
            {
              as_bad (_("Illegal operands: %%r_plt in %d-byte data field"), size);
              goto finish_parsing;
            }
          input_line_pointer += 3;
          special_relocation_type = "plt";
        }
      else if (startswith (input_line_pointer, "tls_dtpoff"))
        {
          if (size != 4 && size != 8)
            {
              as_bad (_("Illegal operands: %%r_tls_dtpoff in %d-byte data field"), size);
              goto finish_parsing;
            }
          input_line_pointer += 10;
          special_relocation_type = "tls_dtpoff";
        }
      else
        {
          goto finish_parsing;
        }

      int expected_size_bits = size * 8;
      const char *suffix_str = NULL;
      size_t suffix_len = 0;

      switch (expected_size_bits)
        {
        case 8:  suffix_str = "8";  suffix_len = 1; break;
        case 16: suffix_str = "16"; suffix_len = 2; break;
        case 32: suffix_str = "32"; suffix_len = 2; break;
        case 64: suffix_str = "64"; suffix_len = 2; break;
        default: break;
        }
      
      if (!suffix_str || strncmp (input_line_pointer, suffix_str, suffix_len) != 0)
        {
          as_bad (_("Illegal operands: Only %%r_%s%d allowed in %d-byte data fields"),
                  special_relocation_type, size * 8, size);
          goto finish_parsing;
        }
      
      input_line_pointer += suffix_len;

      if (*input_line_pointer != '(')
        {
          as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
                  special_relocation_type, size * 8);
          goto finish_parsing;
        }

      input_line_pointer++;

      char *current_scan_ptr = input_line_pointer;
      int paren_nest_level = 0;
      int char_at_current_scan_ptr;

      while (!is_end_of_stmt (char_at_current_scan_ptr = *current_scan_ptr))
        {
          if (char_at_current_scan_ptr == '(')
            paren_nest_level++;
          else if (char_at_current_scan_ptr == ')')
            {
              if (paren_nest_level == 0)
                break;
              paren_nest_level--;
            }
          current_scan_ptr++;
        }

      if (char_at_current_scan_ptr != ')')
        {
          as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
                  special_relocation_type, size * 8);
          goto finish_parsing;
        }

      char saved_char_at_paren_end = *current_scan_ptr;
      *current_scan_ptr = '\0';
      expression (exp);
      *current_scan_ptr = saved_char_at_paren_end;

      if (input_line_pointer != current_scan_ptr)
        {
          as_bad (_("Illegal operands: %%r_%s%d requires arguments in ()"),
                  special_relocation_type, size * 8);
          goto finish_parsing;
        }

      input_line_pointer = current_scan_ptr + 1;

      SKIP_WHITESPACE ();
      int char_after_paren = *input_line_pointer;
      if (!is_end_of_stmt (char_after_paren) && char_after_paren != ',')
        {
          as_bad (_("Illegal operands: garbage after %%r_%s%d()"),
                  special_relocation_type, size * 8);
          goto finish_parsing;
        }

      special_reloc_fully_parsed = true;
    }

finish_parsing:
  if (!special_reloc_fully_parsed)
    {
      input_line_pointer = save_input_ptr;
      expression (exp);
      return NULL;
    }

  return special_relocation_type;
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

  switch (nbytes)
    {
    case 1: r = BFD_RELOC_8; break;
    case 2: r = BFD_RELOC_16; break;
    case 4: r = BFD_RELOC_32; break;
    case 8: r = BFD_RELOC_64; break;
    default:
      abort ();
    }

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
      char reloc_char = *sparc_cons_special_reloc;
      switch (reloc_char)
        {
        case 'd':
          switch (nbytes)
            {
            case 1: r = BFD_RELOC_8_PCREL; break;
            case 2: r = BFD_RELOC_16_PCREL; break;
            case 4: r = BFD_RELOC_32_PCREL; break;
            case 8: r = BFD_RELOC_64_PCREL; break;
            default:
              abort ();
            }
          break;
        case 'p':
          switch (nbytes)
            {
            case 4: r = BFD_RELOC_SPARC_PLT32; break;
            case 8: r = BFD_RELOC_SPARC_PLT64; break;
            default:
              abort ();
            }
          break;
        default:
          switch (nbytes)
            {
            case 4: r = BFD_RELOC_SPARC_TLS_DTPOFF32; break;
            case 8: r = BFD_RELOC_SPARC_TLS_DTPOFF64; break;
            default:
              abort ();
            }
          break;
        }
    }
  else if (sparc_no_align_cons
	   || strcmp (now_seg->name, ".eh_frame") == 0)
    {
      switch (nbytes)
	{
	case 2: r = BFD_RELOC_SPARC_UA16; break;
	case 4: r = BFD_RELOC_SPARC_UA32; break;
	case 8:
#ifdef TE_SOLARIS
          r = (sparc_arch_size == 64) ? BFD_RELOC_SPARC_UA64 : BFD_RELOC_SPARC_UA32;
#else
	  r = BFD_RELOC_SPARC_UA64;
#endif
	  break;
	default:
	  abort ();
	}
   }

  fix_new_exp (frag, where, nbytes, exp, 0, r);
}

#define SPARC_CFI_FRAME_POINTER_REG_NUM 14
#define SPARC_ARCH_BIT_WIDTH_64         64
#define SPARC_CFA_OFFSET_FOR_64BIT      0x7ff
#define SPARC_CFA_OFFSET_DEFAULT        0

void
sparc_cfi_frame_initial_instructions (void)
{
  const int cfa_offset = (sparc_arch_size == SPARC_ARCH_BIT_WIDTH_64)
                         ? SPARC_CFA_OFFSET_FOR_64BIT
                         : SPARC_CFA_OFFSET_DEFAULT;

  cfi_add_CFA_def_cfa (SPARC_CFI_FRAME_POINTER_REG_NUM, cfa_offset);
}

#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <limits.h>

enum {
    SP_DW2REGNUM = 14,
    FP_DW2REGNUM = 30,

    WINDOW_REG_MULTIPLIER = 8,
    G_REG_BASE = 0,
    O_REG_BASE = 1,
    L_REG_BASE = 2,
    I_REG_BASE = 3,
    MAX_WINDOW_REG_DIGIT = '8',

    F_R_DW2REGNUM_SHIFT = 32,
    F_R_INVALID_ODD_THRESHOLD = 64
};

int
sparc_regname_to_dw2regnum (char *regname)
{
  if (regname == NULL || regname[0] == '\0')
    {
      return -1;
    }

  int base_reg_value = -1;
  switch (regname[0])
    {
    case 'g': base_reg_value = G_REG_BASE; break;
    case 'o': base_reg_value = O_REG_BASE; break;
    case 'l': base_reg_value = L_REG_BASE; break;
    case 'i': base_reg_value = I_REG_BASE; break;
    default:
      break;
    }

  if (base_reg_value != -1)
    {
      if (regname[1] >= '0' && regname[1] <= MAX_WINDOW_REG_DIGIT && regname[2] == '\0')
        {
          return base_reg_value * WINDOW_REG_MULTIPLIER + (regname[1] - '0');
        }
      return -1;
    }

  if (strcmp(regname, "sp") == 0)
    {
      return SP_DW2REGNUM;
    }
  if (strcmp(regname, "fp") == 0)
    {
      return FP_DW2REGNUM;
    }

  if (regname[0] == 'f' || regname[0] == 'r')
    {
      char *endptr;
      errno = 0;

      unsigned long regnum_parsed = strtoul(regname + 1, &endptr, 10);

      if (endptr == regname + 1 || *endptr != '\0' || errno == ERANGE)
        {
          return -1;
        }

      if (regnum_parsed > INT_MAX)
        {
          return -1;
        }
      int regnum = (int)regnum_parsed;

      int max_allowed_regnum;
      if (regname[0] == 'f' && SPARC_OPCODE_ARCH_V9_P(max_architecture))
        {
          max_allowed_regnum = 63;
        }
      else
        {
          max_allowed_regnum = 31;
        }

      if (regnum < 0 || regnum > max_allowed_regnum)
        {
          return -1;
        }

      if (regname[0] == 'f')
        {
          regnum += F_R_DW2REGNUM_SHIFT;

          if (regnum >= F_R_INVALID_ODD_THRESHOLD && (regnum & 1))
            {
              return -1;
            }
        }
      return regnum;
    }

  return -1;
}

void
sparc_cfi_emit_pcrel_expr (expressionS *exp, unsigned int nbytes)
{
  sparc_no_align_cons = 1;

  emit_expr_with_reloc (exp, nbytes, "disp");

  /* Ensure sparc_no_align_cons is always reset to 0 before exiting
   * the function. This pattern explicitly marks the cleanup point,
   * improving maintainability and reliability, especially if error
   * handling or early exit conditions were to be added in the future. */
  sparc_no_align_cons = 0;
}

