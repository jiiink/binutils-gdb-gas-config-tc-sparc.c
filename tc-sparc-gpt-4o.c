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

static struct sparc_arch *lookup_arch(const char *name) {
    for (struct sparc_arch *sa = sparc_arch_table; sa->name != NULL; sa++) {
        if (strcmp(sa->name, name) == 0) {
            return sa;
        }
    }
    return NULL;
}

/* Initialize the default opcode arch and word size from the default
   architecture name.  */

#include <stdio.h>
#include <stdlib.h>

static void handle_error(const char *message) {
  fprintf(stderr, "%s\n", message);
  exit(EXIT_FAILURE);
}

static void init_default_arch(void) {
  struct sparc_arch *sa = lookup_arch(default_arch);

  if (!sa || sa->default_arch_size == 0) {
    handle_error("Invalid default architecture, broken assembler.");
  }

  max_architecture = sparc_opcode_lookup_arch(sa->opcode_arch);
  
  if (max_architecture == SPARC_OPCODE_ARCH_BAD) {
    handle_error("Bad opcode table, broken assembler.");
  }

  default_arch_size = sparc_arch_size = sa->default_arch_size;
  default_init_p = 1;
  default_arch_type = sa->arch_type;
}

/* Called by TARGET_MACH.  */

#include <stdbool.h>

static bool default_init_p = false;
static int sparc_arch_size = 0;
#define bfd_mach_sparc 1
#define bfd_mach_sparc_v9 2

void init_default_arch(void);

unsigned long sparc_mach(void) {
    if (!default_init_p) {
        init_default_arch();
    }
    return (sparc_arch_size == 64) ? bfd_mach_sparc_v9 : bfd_mach_sparc;
}

/* Called by TARGET_FORMAT.  */

const char *sparc_target_format(void) {
  if (!default_init_p) {
    init_default_arch();
  }

#ifdef TE_VXWORKS
  return "elf32-sparc-vxworks";
#else
  return (sparc_arch_size == 64) ? ELF64_TARGET_FORMAT : ELF_TARGET_FORMAT;
#endif
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

int md_parse_option(int c, const char *arg) {
    if (!default_init_p) {
        init_default_arch();
    }

    switch (c) {
        case OPTION_BUMP:
            warn_on_bump = 1;
            warn_after_architecture = SPARC_OPCODE_ARCH_V6;
            break;

        case OPTION_XARCH:
            if (startswith(arg, "v9")) {
                md_parse_option(OPTION_64, NULL);
            } else if (startswith(arg, "v8") || startswith(arg, "v7")
                       || startswith(arg, "v6") || !strcmp(arg, "sparclet")
                       || !strcmp(arg, "sparclite") || !strcmp(arg, "sparc86x")) {
                md_parse_option(OPTION_32, NULL);
            }
            // Fall through to case 'A'

        case 'A':
        {
            struct sparc_arch *sa = lookup_arch(arg);
            if (!sa || !sa->user_option_p) {
                if (c == OPTION_XARCH) {
                    as_bad(_("invalid architecture -xarch=%s"), arg);
                } else {
                    as_bad(_("invalid architecture -A%s"), arg);
                }
                return 0;
            }

            enum sparc_opcode_arch_val opcode_arch = sparc_opcode_lookup_arch(sa->opcode_arch);
            if (opcode_arch == SPARC_OPCODE_ARCH_BAD) {
                as_fatal(_("Bad opcode table, broken assembler."));
            }

            if (!architecture_requested || opcode_arch > max_architecture) {
                max_architecture = opcode_arch;
            }

            hwcap_allowed |= ((uint64_t)sparc_opcode_archs[opcode_arch].hwcaps2 << 32) |
                              ((uint64_t)sa->hwcap2_allowed << 32) |
                              sparc_opcode_archs[opcode_arch].hwcaps |
                              sa->hwcap_allowed;
            architecture_requested = 1;
            break;
        }

        case OPTION_SPARC:
            break;

        case OPTION_ENFORCE_ALIGNED_DATA:
            enforce_aligned_data = 1;
            break;

#ifdef SPARC_BIENDIAN
        case OPTION_LITTLE_ENDIAN:
            target_big_endian = 0;
            if (default_arch_type != sparclet) {
                as_fatal("This target does not support -EL");
            }
            break;

        case OPTION_LITTLE_ENDIAN_DATA:
            target_little_endian_data = 1;
            target_big_endian = 0;
            if (default_arch_type != sparc86x && default_arch_type != v9) {
                as_fatal("This target does not support --little-endian-data");
            }
            break;

        case OPTION_BIG_ENDIAN:
            target_big_endian = 1;
            break;
#endif

        case OPTION_32:
        case OPTION_64:
        {
            sparc_arch_size = (c == OPTION_32) ? 32 : 64;
            const char **list = bfd_target_list();
            if (!list) {
                as_fatal("Failed to retrieve target list");
            }

            const char *arch_prefix = (sparc_arch_size == 32) ? "elf32-sparc" : "elf64-sparc";
            int found = 0;

            for (const char **l = list; *l != NULL; l++) {
                if (startswith(*l, arch_prefix)) {
                    found = 1;
                    break;
                }
            }

            if (!found) {
                as_fatal(_("No compiled in support for %d bit object file format"), sparc_arch_size);
            }
            free(list);

            if (sparc_arch_size == 64 && max_architecture < SPARC_OPCODE_ARCH_V9) {
                max_architecture = SPARC_OPCODE_ARCH_V9;
            }
            break;
        }

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
            print_version_id();
            break;

        case 'Q':
        case 's':
        case 'q':
            break;

        case 'K':
            if (strcmp(arg, "PIC") == 0) {
                sparc_pic_code = 1;
            } else {
                as_warn(_("Unrecognized option following -K"));
            }
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

void md_show_usage(FILE *stream) {
    const struct sparc_arch *arch;
    int column = 0;

    if (!default_init_p) {
        init_default_arch();
    }

    fprintf(stream, "SPARC options:\n");

    for (arch = sparc_arch_table; arch->name; arch++) {
        if (arch->user_option_p) {
            if (column + strlen(arch->name) + 5 > 70) {
                column = 0;
                fputc('\n', stream);
            }
            fprintf(stream, "%s-A%s", (arch != sparc_arch_table) ? " | " : "", arch->name);
            column += strlen(arch->name) + 5;
        }
    }

    for (arch = sparc_arch_table; arch->name; arch++) {
        if (arch->user_option_p) {
            if (column + strlen(arch->name) + 9 > 65) {
                column = 0;
                fputc('\n', stream);
            }
            fprintf(stream, " | -xarch=%s", arch->name);
            column += strlen(arch->name) + 9;
        }
    }

    fprintf(stream, "\n"
                    "specify variant of SPARC architecture\n"
                    "-bump             warn when assembler switches architectures\n"
                    "-sparc            ignored\n"
                    "--enforce-aligned-data force .long, etc., to be aligned correctly\n"
                    "-relax            relax jumps and branches (default)\n"
                    "-no-relax         avoid changing any jumps and branches\n"
                    "-32               create 32 bit object file\n"
                    "-64               create 64 bit object file\n"
                    "                  [default is %d]\n"
                    "-TSO              use Total Store Ordering\n"
                    "-PSO              use Partial Store Ordering\n"
                    "-RMO              use Relaxed Memory Ordering\n"
                    "                  [default is %s]\n"
                    "-KPIC             generate PIC\n"
                    "-V                print assembler version number\n"
                    "-undeclared-regs  ignore application global register usage without appropriate .register directive (default)\n"
                    "-no-undeclared-regs force error on application global register usage without appropriate .register directive\n"
                    "--dcti-couples-detect warn when an unpredictable DCTI couple is found\n"
                    "-q                ignored\n"
                    "-Qy, -Qn          ignored\n"
                    "-s                ignored\n", default_arch_size, 
                    (default_arch_size == 64) ? "RMO" : "TSO");
    
#ifdef SPARC_BIENDIAN
    fprintf(stream,
            "-EL               generate code for a little endian machine\n"
            "-EB               generate code for a big endian machine\n"
            "--little-endian-data generate code for a machine having big endian instructions and little endian data.\n");
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

static int cmp_reg_entry(const void *parg, const void *qarg) {
    const struct priv_reg_entry *p = parg;
    const struct priv_reg_entry *q = qarg;
    
    if (p->name == q->name) return 0;
    if (p->name == NULL) return 1;
    if (q->name == NULL) return -1;
    
    return strcmp(q->name, p->name);
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

static int cmp_perc_entry(const void *parg, const void *qarg) {
    const struct perc_entry *p = parg;
    const struct perc_entry *q = qarg;

    if (p->name == q->name) return 0;
    if (p->name == NULL) return 1;
    if (q->name == NULL) return -1;
    return strcmp(q->name, p->name);
}

/* This function is called once, at assembler startup time.  It should
   set up all the tables, etc. that the MD part of the assembler will
   need.  */

void md_begin(void) {
    if (!default_init_p) {
        init_default_arch();
    }

    sparc_cie_data_alignment = (sparc_arch_size == 64) ? -8 : -4;
    op_hash = str_htab_create();

    if (!initialize_opcode_table()) {
        as_fatal(_("Broken assembler. No assembly attempted."));
    }

    qsort(priv_reg_table, ARRAY_SIZE(priv_reg_table), sizeof(priv_reg_table[0]), cmp_reg_entry);
    qsort(hpriv_reg_table, ARRAY_SIZE(hpriv_reg_table), sizeof(hpriv_reg_table[0]), cmp_reg_entry);
    qsort(v9a_asr_table, ARRAY_SIZE(v9a_asr_table), sizeof(v9a_asr_table[0]), cmp_reg_entry);

    set_max_architecture();
    prepare_pseudo_ops();
}

int initialize_opcode_table() {
    unsigned int i = 0;
    int lose = 0;

    for (; i < (unsigned int)sparc_num_opcodes; i++) {
        const char *name = sparc_opcodes[i].name;
        if (str_hash_insert(op_hash, name, &sparc_opcodes[i], 0) != NULL) {
            as_bad(_("duplicate %s"), name);
            lose = 1;
        }
        check_losing_opcode(&i, &lose, name);
    }

    for (i = 0; native_op_table[i].name; i++) {
        const char *name = (sparc_arch_size == 32) ? native_op_table[i].name32 : native_op_table[i].name64;
        if (!process_native_opcode(name, &native_op_table[i], &lose)) {
            as_bad(_("Internal error: can't find opcode `%s' for `%s'\n"), name, native_op_table[i].name);
            lose = 1;
        }
    }

    return !lose;
}

void check_losing_opcode(unsigned int *i, int *lose, const char *name) {
    do {
        if (sparc_opcodes[*i].match & sparc_opcodes[*i].lose) {
            as_bad(_("Internal error: losing opcode: `%s' \"%s\"\n"), sparc_opcodes[*i].name, sparc_opcodes[*i].args);
            *lose = 1;
        }
        ++(*i);
    } while (*i < (unsigned int)sparc_num_opcodes && !strcmp(sparc_opcodes[*i].name, name));
}

int process_native_opcode(const char *name, const struct native_op_entry *entry, int *lose) {
    const struct sparc_opcode *insn = str_hash_find(op_hash, name);
    if (insn && !str_hash_insert(op_hash, entry->name, insn, 0)) {
        as_bad(_("duplicate %s"), entry->name);
        *lose = 1;
        return 1;
    }
    return 0;
}

void set_max_architecture() {
    if (warn_on_bump && architecture_requested) {
        warn_after_architecture = max_architecture;
    }

    if (warn_on_bump || !architecture_requested) {
        enum sparc_opcode_arch_val current_max_architecture = max_architecture;
        for (max_architecture = SPARC_OPCODE_ARCH_MAX; max_architecture > warn_after_architecture; --max_architecture) {
            if (!SPARC_OPCODE_CONFLICT_P(max_architecture, current_max_architecture)) {
                break;
            }
        }
    }
}

void prepare_pseudo_ops() {
    struct priv_reg_entry *reg_tables[] = {priv_reg_table, hpriv_reg_table, v9a_asr_table, NULL};
    struct priv_reg_entry **reg_table;
    int entry = 0;
    unsigned int i;

    for (reg_table = reg_tables; *reg_table; reg_table++) {
        struct priv_reg_entry *reg;
        for (reg = *reg_table; reg->name; reg++) {
            populate_perc_entry(&perc_table[entry++], perc_entry_reg, reg->name, reg->name, reg);
        }
    }

    for (i = 0; i < ARRAY_SIZE(pop_table); i++) {
        populate_perc_entry(&perc_table[entry++],
                            (pop_table[i].flags & F_POP_POSTFIX) ? perc_entry_post_pop : perc_entry_imm_pop,
                            pop_table[i].name, pop_table[i].name, &pop_table[i]);
    }

    perc_table[entry].type = perc_entry_none;
    qsort(perc_table, ARRAY_SIZE(perc_table), sizeof(perc_table[0]), cmp_perc_entry);
}

void populate_perc_entry(struct perc_entry *p, enum perc_entry_type type, const char *name, const char *entry_name, void *data) {
    p->type = type;
    p->name = name;
    p->len = strlen(entry_name);
    p->reg = data;
}

/* Called after all assembly has been done.  */

void sparc_md_finish(void) {
    unsigned long mach;
    
    if (sparc_arch_size == 64) {
        switch (current_architecture) {
            case SPARC_OPCODE_ARCH_V9A: mach = bfd_mach_sparc_v9a; break;
            case SPARC_OPCODE_ARCH_V9B: mach = bfd_mach_sparc_v9b; break;
            case SPARC_OPCODE_ARCH_V9C: mach = bfd_mach_sparc_v9c; break;
            case SPARC_OPCODE_ARCH_V9D: mach = bfd_mach_sparc_v9d; break;
            case SPARC_OPCODE_ARCH_V9E: mach = bfd_mach_sparc_v9e; break;
            case SPARC_OPCODE_ARCH_V9V: mach = bfd_mach_sparc_v9v; break;
            case SPARC_OPCODE_ARCH_V9M: mach = bfd_mach_sparc_v9m; break;
            case SPARC_OPCODE_ARCH_M8:  mach = bfd_mach_sparc_v9m8; break;
            default: mach = bfd_mach_sparc_v9; break;
        }
    } else {
        switch (current_architecture) {
            case SPARC_OPCODE_ARCH_SPARCLET: mach = bfd_mach_sparc_sparclet; break;
            case SPARC_OPCODE_ARCH_V9: mach = bfd_mach_sparc_v8plus; break;
            case SPARC_OPCODE_ARCH_V9A: mach = bfd_mach_sparc_v8plusa; break;
            case SPARC_OPCODE_ARCH_V9B: mach = bfd_mach_sparc_v8plusb; break;
            case SPARC_OPCODE_ARCH_V9C: mach = bfd_mach_sparc_v8plusc; break;
            case SPARC_OPCODE_ARCH_V9D: mach = bfd_mach_sparc_v8plusd; break;
            case SPARC_OPCODE_ARCH_V9E: mach = bfd_mach_sparc_v8pluse; break;
            case SPARC_OPCODE_ARCH_V9V: mach = bfd_mach_sparc_v8plusv; break;
            case SPARC_OPCODE_ARCH_V9M: mach = bfd_mach_sparc_v8plusm; break;
            case SPARC_OPCODE_ARCH_M8:  mach = bfd_mach_sparc_v8plusm8; break;
            default: mach = bfd_mach_sparc; break;
        }
    }
    
    if (!bfd_set_arch_mach(stdoutput, bfd_arch_sparc, mach)) {
        as_fatal(_("error setting architecture: %s"), bfd_errmsg(bfd_get_error()));
    }

#ifndef TE_SOLARIS
    int hwcaps = hwcap_seen & 0xffffffff;
    int hwcaps2 = hwcap_seen >> 32;
    
    if ((hwcaps && !bfd_elf_add_obj_attr_int(stdoutput, OBJ_ATTR_GNU, Tag_GNU_Sparc_HWCAPS, hwcaps)) ||
        (hwcaps2 && !bfd_elf_add_obj_attr_int(stdoutput, OBJ_ATTR_GNU, Tag_GNU_Sparc_HWCAPS2, hwcaps2))) {
        as_fatal(_("error adding attribute: %s"), bfd_errmsg(bfd_get_error()));
    }
#endif
}

/* Return non-zero if VAL is in the range -(MAX+1) to MAX.  */

#include <stdlib.h>
#include <limits.h>

static inline int in_signed_range(bfd_signed_vma val, bfd_signed_vma max) {
    if (max <= 0) {
        abort();
    }

    if (sparc_arch_size == 32) {
        bfd_vma sign = (bfd_vma)1 << 31;
        val = (val ^ sign) - sign;
    }

    return val <= max && val >= -max ? 1 : 0;
}

/* Return non-zero if VAL is in the range 0 to MAX.  */

static inline int in_unsigned_range(bfd_vma val, bfd_vma max) {
    return val <= max;
}

/* Return non-zero if VAL is in the range -(MAX/2+1) to MAX.
   (e.g. -15 to +31).  */

#include <stdlib.h>

static inline int in_bitfield_range(bfd_signed_vma val, bfd_signed_vma max) {
    if (max <= 0) {
        abort();
    }
    
    if (val < ~(max >> 1) || val > max) {
        return 0;
    }
    
    return 1;
}

static int sparc_ffs(unsigned int mask) {
    if (mask == 0) return -1;

    int position = 0;
    while ((mask & 1) == 0) {
        mask >>= 1;
        position++;
    }
    return position;
}

/* Implement big shift right.  */
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static bfd_vma BSR(bfd_vma val, int amount) {
    if ((sizeof(bfd_vma) <= sizeof(uint32_t)) && (amount >= CHAR_BIT * sizeof(bfd_vma))) {
        fprintf(stderr, "Error: Amount exceeds supported bit size.\n");
        exit(EXIT_FAILURE);
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

static void synthetize_setuw(const struct sparc_opcode *insn) {
    int need_hi22_p = 0;
    int rd = (the_insn.opcode & RD(~0)) >> 25;
    int64_t add_number = the_insn.exp.X_add_number;

    if (the_insn.exp.X_op == O_constant) {
        if (SPARC_OPCODE_ARCH_V9_P(max_architecture)) {
            if (sizeof(offsetT) > 4 && (add_number < 0 || add_number > (offsetT)U0xffffffff)) {
                as_warn(_("set: number not in 0..4294967295 range"));
            }
        } else {
            if (sizeof(offsetT) > 4 && (add_number < -(offsetT)U0x80000000 || add_number > (offsetT)U0xffffffff)) {
                as_warn(_("set: number not in -2147483648..4294967295 range"));
            }
            add_number = (int32_t)add_number;
        }
    }

    if (the_insn.exp.X_op != O_constant || add_number >= (1 << 12) || add_number < -(1 << 12)) {
        the_insn.opcode = SETHI_INSN | RD(rd) | ((add_number >> 10) & (the_insn.exp.X_op == O_constant ? 0x3fffff : 0));
        the_insn.reloc = (the_insn.exp.X_op != O_constant ? BFD_RELOC_HI22 : BFD_RELOC_NONE);
        output_insn(insn, &the_insn);
        need_hi22_p = 1;
    }

    if (the_insn.exp.X_op != O_constant || (need_hi22_p && (add_number & 0x3FF) != 0) || !need_hi22_p) {
        the_insn.opcode = OR_INSN | (need_hi22_p ? RS1(rd) : 0) | RD(rd) | IMMED |
                          (add_number & (the_insn.exp.X_op != O_constant ? 0 : need_hi22_p ? 0x3ff : 0x1fff));
        the_insn.reloc = (the_insn.exp.X_op != O_constant ? BFD_RELOC_LO10 : BFD_RELOC_NONE);
        output_insn(insn, &the_insn);
    }
}

/* Handle the setsw synthetic instruction.  */

static void
synthetize_setsw(const struct sparc_opcode *insn)
{
    int low32, rd, opc;

    rd = (the_insn.opcode & RD(~0)) >> 25;

    if (the_insn.exp.X_op != O_constant)
    {
        synthetize_setuw(insn);
        the_insn.opcode = (SRA_INSN | RS1(rd) | RD(rd));
        the_insn.reloc = BFD_RELOC_NONE;
        output_insn(insn, &the_insn);
        return;
    }

    if (sizeof(offsetT) > 4 &&
        (the_insn.exp.X_add_number < -(offsetT)U0x80000000 ||
        the_insn.exp.X_add_number > (offsetT)U0xffffffff))
    {
        as_warn(_("setsw: number not in -2147483648..4294967295 range"));
    }

    low32 = the_insn.exp.X_add_number;

    if (low32 >= 0)
    {
        synthetize_setuw(insn);
        return;
    }

    opc = OR_INSN;
    the_insn.reloc = BFD_RELOC_NONE;

    if (low32 < -(1 << 12))
    {
        the_insn.opcode = (SETHI_INSN | RD(rd) |
                          (((~the_insn.exp.X_add_number) >> 10) & 0x3fffff));
        output_insn(insn, &the_insn);
        low32 = 0x1c00 | (low32 & 0x3ff);
        opc = RS1(rd) | XOR_INSN;
    }

    the_insn.opcode = (opc | RD(rd) | IMMED | (low32 & 0x1fff));
    output_insn(insn, &the_insn);
}

/* Handle the setx synthetic instruction.  */

static void handle_non_constant_sparc(const struct sparc_opcode *insn, int *lower32, int *upper32) {
    if (sparc_arch_size == 32) {
        the_insn.exp.X_add_number &= 0xffffffff;
        synthetize_setuw(insn);
        return;
    }
    *lower32 = 0;
    *upper32 = 0;
}

static void calculate_bits_needed(int upper32, int lower32, int *need_hh22_p, int *need_hm10_p, int *need_hi22_p, int *need_lo10_p, int *need_xor10_p) {
    if (upper32 < -(1 << 12) || upper32 >= (1 << 12)) {
        *need_hh22_p = 1;
    }
    if ((*need_hh22_p && (upper32 & 0x3ff) != 0) || (!*need_hh22_p && upper32 != 0 && upper32 != -1)) {
        *need_hm10_p = 1;
    }
    if (lower32 != 0 || (!*need_hh22_p && !*need_hm10_p)) {
        if (lower32 < -(1 << 12) || lower32 >= (1 << 12) || (lower32 < 0 && upper32 != -1) || (lower32 >= 0 && upper32 == -1)) {
            *need_hi22_p = 1;
        }
        if (*need_hi22_p && upper32 == -1) {
            *need_xor10_p = 1;
        } else if ((*need_hi22_p && (lower32 & 0x3ff) != 0) || (!*need_hi22_p && (lower32 & 0x1fff) != 0) || (!*need_hi22_p && !*need_hh22_p && !*need_hm10_p)) {
            *need_lo10_p = 1;
        }
    }
}

static void output_instruction(const struct sparc_opcode *insn, unsigned int opcode, int reloc_type) {
    the_insn.opcode = opcode;
    the_insn.reloc = reloc_type;
    output_insn(insn, &the_insn);
}

static void assemble_setx(const struct sparc_opcode *insn) {
    int upper32 = (the_insn.exp.X_add_number >> 32) & 0xffffffff;
    int lower32 = the_insn.exp.X_add_number & 0xffffffff;
    int tmpreg = (the_insn.opcode & RS1 (~0)) >> 14;
    int dstreg = (the_insn.opcode & RD (~0)) >> 25;
    int upper_dstreg = tmpreg;
    int need_hh22_p = 0, need_hm10_p = 0, need_hi22_p = 0, need_lo10_p = 0;
    int need_xor10_p = 0;

    if (the_insn.exp.X_op != O_constant) {
        handle_non_constant_sparc(insn, &lower32, &upper32);
    } else {
        the_insn.exp.X_add_number = 0;
        calculate_bits_needed(upper32, lower32, &need_hh22_p, &need_hm10_p, &need_hi22_p, &need_lo10_p, &need_xor10_p);

        if (lower32 == 0) {
            upper_dstreg = dstreg;
        }
    }

    if (!upper_dstreg && dstreg) {
        as_warn (_("setx: illegal temporary register g0"));
    }

    if (need_hh22_p) {
        output_instruction(insn, SETHI_INSN | RD(upper_dstreg) | ((upper32 >> 10) & 0x3fffff), BFD_RELOC_SPARC_HH22);
    }

    if (need_hi22_p) {
        output_instruction(insn, SETHI_INSN | RD(dstreg) | (((need_xor10_p ? ~lower32 : lower32) >> 10) & 0x3fffff), BFD_RELOC_SPARC_LM22);
    }

    if (need_hm10_p) {
        output_instruction(insn, OR_INSN | (need_hh22_p ? RS1(upper_dstreg) : 0) | RD(upper_dstreg) | IMMED | (upper32 & (need_hh22_p ? 0x3ff : 0x1fff)), BFD_RELOC_SPARC_HM10);
    }

    if (need_lo10_p) {
        output_instruction(insn, OR_INSN | (need_hi22_p ? RS1(dstreg) : 0) | RD(dstreg) | IMMED | (lower32 & (need_hi22_p ? 0x3ff : 0x1fff)), BFD_RELOC_LO10);
    }

    if (need_hh22_p || need_hm10_p) {
        output_instruction(insn, SLLX_INSN | RS1(upper_dstreg) | RD(upper_dstreg) | IMMED | 32, BFD_RELOC_NONE);
    }

    if (need_xor10_p) {
        output_instruction(insn, XOR_INSN | RS1(dstreg) | RD(dstreg) | IMMED | 0x1c00 | (lower32 & 0x3ff), BFD_RELOC_NONE);
    } else if ((need_hh22_p || need_hm10_p) && (need_hi22_p || need_lo10_p)) {
        output_instruction(insn, OR_INSN | RS1(dstreg) | RS2(upper_dstreg) | RD(dstreg), BFD_RELOC_NONE);
    }
}

static void synthetize_setx(const struct sparc_opcode *insn) {
    assemble_setx(insn);
}

/* Main entry point to assemble one instruction.  */

#include <stdbool.h>

void md_assemble(char *str) {
    const struct sparc_opcode *insn;
    int special_case;
    bool unpredictable_dcti_couple = false;
    bool fp_branch_delay_slot = false;

    know(str);
    special_case = sparc_ip(str, &insn);
    if (insn == NULL) {
        return;
    }

    if (last_insn != NULL && (last_insn->flags & F_DELAYED) != 0) {
        if (dcti_couples_detect && (insn->flags & F_DELAYED) != 0) {
            if ((max_architecture < SPARC_OPCODE_ARCH_V9 && (last_insn->flags & F_CONDBR) != 0) ||
                max_architecture >= SPARC_OPCODE_ARCH_V9C) {
                unpredictable_dcti_couple = true;
            }
        }

        if ((insn->flags & F_FBR) != 0 && ((last_insn->flags & (F_UNBR | F_CONDBR | F_FBR)) == 0 ||
           (last_opcode & ANNUL) == 0)) {
            fp_branch_delay_slot = true;
        }
    }

    if (unpredictable_dcti_couple) {
        as_warn(_("unpredictable DCTI couple"));
    }

    if (fp_branch_delay_slot) {
        as_warn(_("FP branch in delay slot"));
    }

    if (max_architecture < SPARC_OPCODE_ARCH_V9 && last_insn != NULL &&
        (insn->flags & F_FBR) != 0 && (last_insn->flags & F_FLOAT) != 0 &&
        (last_insn->match & OP3(0x35)) == OP3(0x35)) {
        struct sparc_it nop_insn;
        nop_insn.opcode = NOP_INSN;
        nop_insn.reloc = BFD_RELOC_NONE;
        output_insn(insn, &nop_insn);
        as_warn(_("FP branch preceded by FP compare; NOP inserted"));
    }

    switch (special_case) {
        case SPECIAL_CASE_NONE:
            output_insn(insn, &the_insn);
            break;
        case SPECIAL_CASE_SETSW:
            synthetize_setsw(insn);
            break;
        case SPECIAL_CASE_SET:
            synthetize_setuw(insn);
            break;
        case SPECIAL_CASE_SETX:
            synthetize_setx(insn);
            break;
        case SPECIAL_CASE_FDIV: {
            int rd = (the_insn.opcode >> 25) & 0x1f;
            output_insn(insn, &the_insn);
            gas_assert(the_insn.reloc == BFD_RELOC_NONE);
            the_insn.opcode = FMOVS_INSN | rd | RD(rd);
            output_insn(insn, &the_insn);
            return;
        }
        default:
            as_fatal(_("failed special case insn sanity check"));
    }
}

static const char *get_hwcap_name(uint64_t mask) {
    switch ((mask & 0xFFFFFFFF) ? mask : (mask >> 32)) {
        case HWCAP_MUL32: return "mul32";
        case HWCAP_DIV32: return "div32";
        case HWCAP_FSMULD: return "fsmuld";
        case HWCAP_V8PLUS: return "v8plus";
        case HWCAP_POPC: return "popc";
        case HWCAP_VIS: return "vis";
        case HWCAP_VIS2: return "vis2";
        case HWCAP_ASI_BLK_INIT: return "ASIBlkInit";
        case HWCAP_FMAF: return "fmaf";
        case HWCAP_VIS3: return "vis3";
        case HWCAP_HPC: return "hpc";
        case HWCAP_RANDOM: return "random";
        case HWCAP_TRANS: return "trans";
        case HWCAP_FJFMAU: return "fjfmau";
        case HWCAP_IMA: return "ima";
        case HWCAP_ASI_CACHE_SPARING: return "cspare";
        case HWCAP_AES: return "aes";
        case HWCAP_DES: return "des";
        case HWCAP_KASUMI: return "kasumi";
        case HWCAP_CAMELLIA: return "camellia";
        case HWCAP_MD5: return "md5";
        case HWCAP_SHA1: return "sha1";
        case HWCAP_SHA256: return "sha256";
        case HWCAP_SHA512: return "sha512";
        case HWCAP_MPMUL: return "mpmul";
        case HWCAP_MONT: return "mont";
        case HWCAP_PAUSE: return "pause";
        case HWCAP_CBCOND: return "cbcond";
        case HWCAP_CRC32C: return "crc32c";
        case HWCAP2_FJATHPLUS: return "fjathplus";
        case HWCAP2_VIS3B: return "vis3b";
        case HWCAP2_ADP: return "adp";
        case HWCAP2_SPARC5: return "sparc5";
        case HWCAP2_MWAIT: return "mwait";
        case HWCAP2_XMPMUL: return "xmpmul";
        case HWCAP2_XMONT: return "xmont";
        case HWCAP2_NSEC: return "nsec";
        case HWCAP2_SPARC6: return "sparc6";
        case HWCAP2_ONADDSUB: return "onaddsub";
        case HWCAP2_ONMUL: return "onmul";
        case HWCAP2_ONDIV: return "ondiv";
        case HWCAP2_DICTUNP: return "dictunp";
        case HWCAP2_FPCMPSHL: return "fpcmpshl";
        case HWCAP2_RLE: return "rle";
        case HWCAP2_SHA3: return "sha3";
        default: return "UNKNOWN";
    }
}

/* Subroutine of md_assemble to do the actual parsing.  */

static int sparc_ip(char *str, const struct sparc_opcode **pinsn) {
    const char *error_message = "";
    char *s, *argsStart;
    const struct sparc_opcode *insn;
    unsigned long opcode;
    int special_case = SPECIAL_CASE_NONE;
    const sparc_asi *sasi = NULL;
    int match = 0, comma = 0, v9_arg_p;

    s = str;
    while (ISLOWER(*s) || ISDIGIT(*s) || *s == '_') {
        ++s;
    }

    switch (*s) {
    case '\0':
    case ',':
        if (*s == ',') comma = 1;
        *s++ = '\0';
        break;
    default:
        if (is_whitespace(*s)) { *s++ = '\0'; break; }
        as_bad(_("Unknown opcode: `%s'"), str);
        *pinsn = NULL;
        return special_case;
    }

    insn = str_hash_find(op_hash, str);
    *pinsn = insn;
    if (!insn) {
        as_bad(_("Unknown opcode: `%s'"), str);
        return special_case;
    }
    if (comma) *--s = ',';

    argsStart = s;
    for (;;) {
        opcode = insn->match;
        memset(&the_insn, '\0', sizeof(the_insn));
        the_insn.reloc = BFD_RELOC_NONE;
        v9_arg_p = 0;

        const char *args;
        for (args = insn->args; *args; ++args) {
            switch (*args) {
            case 'K': {
                int kmask = 0;
                if (*s == '#') {
                    while (*s == '#') {
                        int jmask;
                        if (!parse_keyword_arg(sparc_encode_membar, &s, &jmask)) {
                            error_message = _(": invalid membar mask name");
                            goto error;
                        }
                        kmask |= jmask;
                        s = skip_white_and_or(s);
                    }
                } else {
                    if (!parse_const_expr_arg(&s, &kmask)) {
                        error_message = _(": invalid membar mask expression");
                        goto error;
                    }
                    if (kmask < 0 || kmask > 127) {
                        error_message = _(": invalid membar mask number");
                        goto error;
                    }
                }
                opcode |= MEMBAR(kmask);
                continue;
            }

            case '3': {
                int smask = 0;
                if (!parse_const_expr_arg(&s, &smask)) {
                    error_message = _(": invalid siam mode expression");
                    goto error;
                }
                if (smask < 0 || smask > 7) {
                    error_message = _(": invalid siam mode number");
                    goto error;
                }
                opcode |= smask;
                continue;
            }

            case '*': {
                int fcn = 0;
                if (*s == '#') {
                    if (!parse_keyword_arg(sparc_encode_prefetch, &s, &fcn)) {
                        error_message = _(": invalid prefetch function name");
                        goto error;
                    }
                } else {
                    if (!parse_const_expr_arg(&s, &fcn)) {
                        error_message = _(": invalid prefetch function expression");
                        goto error;
                    }
                    if (fcn < 0 || fcn > 31) {
                        error_message = _(": invalid prefetch function number");
                        goto error;
                    }
                }
                opcode |= RD(fcn);
                continue;
            }

            case 'r':
            case 'O':
            case '1':
            case '2':
            case 'd':
                if (parse_register(&s, &mask) && mask_valid(mask)) {
                    opcode = update_opcode(opcode, mask, *args);
                    continue;
                }
                break;

            case 'a':
                if (*s++ == 'a') { opcode |= ANNUL; continue; }
                break;

            default:
                break;
            }
            break;
        }

    error:
        if (!match) {
            if (insn_has_more_variants(insn)) {
                ++insn;
                s = argsStart;
                continue;
            } else {
                as_bad(_("Illegal operands%s"), error_message);
                return special_case;
            }
        } else {
            if (!is_architecture_supported(insn, sasi, &error_message)) {
                as_bad(_("Illegal operands%s"), error_message);
                return special_case;
            }
        }
        break;
    }

    the_insn.opcode = opcode;
    return special_case;
}

#include <ctype.h>

static char *skip_over_keyword(char *q) {
    if (*q == '#' || *q == '%') {
        q++;
    }
    while (isalnum((unsigned char)*q) || *q == '_') {
        q++;
    }
    return q;
}

#include <stdbool.h>

static bool parse_sparc_asi(char **input_pointer_p, const sparc_asi **value_p) {
    char *p = *input_pointer_p;
    char *q = skip_over_keyword(p);
    
    char saved_char = *q;
    *q = '\0';
    
    const sparc_asi *value = sparc_encode_asi(p);
    *q = saved_char;

    if (value == NULL) {
        return false;
    }

    *value_p = value;
    *input_pointer_p = q;
    return true;
}

/* Parse an argument that can be expressed as a keyword.
   (eg: #StoreStore or %ccfr).
   The result is a boolean indicating success.
   If successful, INPUT_POINTER is updated.  */

#include <stdbool.h>

static bool parse_keyword_arg(int (*lookup_fn)(const char *), char **input_pointerP, int *valueP) {
    if (!lookup_fn || !input_pointerP || !*input_pointerP || !valueP) {
        return false;
    }

    char *p = *input_pointerP;
    char *q = skip_over_keyword(p);
    if (!q) {
        return false;
    }

    char original_char = *q;
    *q = '\0';
    int value = lookup_fn(p);
    *q = original_char;

    if (value == -1) {
        return false;
    }

    *valueP = value;
    *input_pointerP = q;
    return true;
}

/* Parse an argument that is a constant expression.
   The result is a boolean indicating success.  */

#include <stdbool.h>

static bool parse_constant_expression(char **input_pointer, int *value) {
    char *original_input = *input_pointer;
    expressionS exp;

    if (**input_pointer == '%') {
        return false;
    }

    input_line_pointer = *input_pointer;
    expression(&exp);
    *input_pointer = input_line_pointer;
    input_line_pointer = original_input;

    if (exp.X_op != O_constant) {
        return false;
    }

    *value = exp.X_add_number;
    return true;
}

/* Subroutine of sparc_ip to parse an expression.  */

static int get_expression(char *str) {
    char *original_input = input_line_pointer;
    input_line_pointer = str;
    segT seg = expression(&the_insn.exp);

    int is_valid_segment = (seg == absolute_section) ||
                           (seg == text_section) ||
                           (seg == data_section) ||
                           (seg == bss_section) ||
                           (seg == undefined_section);

    if (!is_valid_segment) {
        the_insn.error = _("bad segment");
        expr_parse_end = input_line_pointer;
        input_line_pointer = original_input;
        return 1;
    }

    expr_parse_end = input_line_pointer;
    input_line_pointer = original_input;
    return 0;
}

/* Subroutine of md_assemble to output one insn.  */

static void output_insn(const struct sparc_opcode *insn, struct sparc_it *theinsn) {
    char *toP = frag_more(4);

    // Put out the opcode.
    if (INSN_BIG_ENDIAN) {
        number_to_chars_bigendian(toP, theinsn->opcode, 4);
    } else {
        number_to_chars_littleendian(toP, theinsn->opcode, 4);
    }

    // Put out the symbol-dependent stuff.
    if (theinsn->reloc != BFD_RELOC_NONE) {
        fixS *fixP = fix_new_exp(
            frag_now,                          // Which frag.
            (toP - frag_now->fr_literal),      // Where.
            4,                                 // Size.
            &theinsn->exp,
            theinsn->pcrel,
            theinsn->reloc
        );
        fixP->fx_no_overflow = 1;
        
        if (theinsn->reloc == BFD_RELOC_SPARC_OLO10) {
            fixP->tc_fix_data = theinsn->exp2.X_add_number;
        }
    }

    last_insn = insn;
    last_opcode = theinsn->opcode;

    dwarf2_emit_insn(4);
}

#include <stdbool.h>

const char *ieee_md_atof(int type, char *litP, int *sizeP, bool is_big_endian);

const char *md_atof(int type, char *litP, int *sizeP) {
    return ieee_md_atof(type, litP, sizeP, true);
}

/* Write a value out to the object file, using the appropriate
   endianness.  */

void md_number_to_chars(char *buf, valueT val, int n) {
    int isLittleEndianDebug = target_little_endian_data && (n == 4 || n == 2) && (~now_seg->flags & SEC_ALLOC);
    
    if (target_big_endian || isLittleEndianDebug) {
        number_to_chars_bigendian(buf, val, n);
    } else {
        number_to_chars_littleendian(buf, val, n);
    }
}

/* Apply a fixS to the frags, now that we know the value it ought to
   hold.  */

void md_apply_fix(fixS *fixP, valueT *valP, segT segment ATTRIBUTE_UNUSED) {
    char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;
    offsetT val = *valP;
    long insn;

    gas_assert(fixP->fx_r_type < BFD_RELOC_UNUSED);

    fixP->fx_addnumber = val;

    if (fixP->fx_addsy != NULL) {
        static const int sparc_tls_types[] = {
            BFD_RELOC_SPARC_TLS_GD_HI22, BFD_RELOC_SPARC_TLS_GD_LO10, BFD_RELOC_SPARC_TLS_GD_ADD,
            BFD_RELOC_SPARC_TLS_GD_CALL, BFD_RELOC_SPARC_TLS_LDM_HI22, BFD_RELOC_SPARC_TLS_LDM_LO10,
            BFD_RELOC_SPARC_TLS_LDM_ADD, BFD_RELOC_SPARC_TLS_LDM_CALL, BFD_RELOC_SPARC_TLS_LDO_HIX22,
            BFD_RELOC_SPARC_TLS_LDO_LOX10, BFD_RELOC_SPARC_TLS_LDO_ADD, BFD_RELOC_SPARC_TLS_IE_HI22,
            BFD_RELOC_SPARC_TLS_IE_LO10, BFD_RELOC_SPARC_TLS_IE_LD, BFD_RELOC_SPARC_TLS_IE_LDX,
            BFD_RELOC_SPARC_TLS_IE_ADD, BFD_RELOC_SPARC_TLS_LE_HIX22, BFD_RELOC_SPARC_TLS_LE_LOX10,
            BFD_RELOC_SPARC_TLS_DTPMOD32, BFD_RELOC_SPARC_TLS_DTPMOD64, BFD_RELOC_SPARC_TLS_DTPOFF32,
            BFD_RELOC_SPARC_TLS_DTPOFF64, BFD_RELOC_SPARC_TLS_TPOFF32, BFD_RELOC_SPARC_TLS_TPOFF64
        };

        for (unsigned int i = 0; i < sizeof(sparc_tls_types) / sizeof(sparc_tls_types[0]); ++i) {
            if (fixP->fx_r_type == sparc_tls_types[i]) {
                S_SET_THREAD_LOCAL(fixP->fx_addsy);
                return;
            }
        }
    }

    if (fixP->fx_addsy && fixP->fx_r_type == BFD_RELOC_32_PCREL_S2) {
        val += fixP->fx_where + fixP->fx_frag->fr_address;
    }

    switch (fixP->fx_r_type) {
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
        case BFD_RELOC_VTABLE_INHERIT:
        case BFD_RELOC_VTABLE_ENTRY:
            fixP->fx_done = 0;
            return;
        default:
            if (!process_instruction_relocation(buf, &insn, fixP->fx_r_type, val, fixP, fixP->fx_where, sparc_relax, sparc_arch_size, current_architecture)) {
                as_bad_where(fixP->fx_file, fixP->fx_line, "bad or unhandled relocation type: 0x%02x", fixP->fx_r_type);
            }
    }

    if (fixP->fx_addsy == 0 && !fixP->fx_pcrel) {
        fixP->fx_done = 1;
    }
}

bool process_instruction_relocation(char *buf, long *insn, int fx_r_type, offsetT val, fixS *fixP, char *fx_where, bool sparc_relax, int sparc_arch_size, int current_architecture) {
    if (INSN_BIG_ENDIAN)
        *insn = bfd_getb32(buf);
    else
        *insn = bfd_getl32(buf);

    switch (fx_r_type) {
        case BFD_RELOC_32_PCREL_S2:
            val = adjust_pcrel_value(val, fixP);
            process_pcrel32(buf, insn, val, sparc_relax, current_architecture, sparc_arch_size);
            break;
        case BFD_RELOC_SPARC_11:
            return apply_reloc_sparc_11(insn, val, fixP);
        case BFD_RELOC_SPARC_10:
            return apply_reloc_sparc_10(insn, val, fixP);
        case BFD_RELOC_SPARC_7:
            return apply_reloc_sparc_7(insn, val, fixP);
        case BFD_RELOC_SPARC_6:
            return apply_reloc_sparc_6(insn, val, fixP);
        case BFD_RELOC_SPARC_5:
            return apply_reloc_sparc_5(insn, val, fixP);
        case BFD_RELOC_SPARC_WDISP10:
            return apply_wdisp10_reloc(insn, val, fixP);
        default:
            handle_other_relocs(buf, insn, fx_r_type, val, fixP);
            break;
    }
    return true;
}

offsetT adjust_pcrel_value(offsetT val, fixS *fixP) {
    val = val >> 2;
    if (!sparc_pic_code || fixP->fx_addsy == NULL || symbol_section_p(fixP->fx_addsy))
        ++val;
    return val;
}

void process_pcrel32(char *buf, long *insn, offsetT val, bool sparc_relax, int current_architecture, int sparc_arch_size) {
    *insn |= val & 0x3fffffff;
    if (sparc_relax && should_optimize_pcrel(buf, *insn, val, current_architecture, sparc_arch_size)) {
        apply_pcrel_optimization(buf, insn, val);
    }
}

bool should_optimize_pcrel(char *buf, long insn, offsetT val, int current_architecture, int sparc_arch_size) {
    long delay = get_delay_slot(buf + 4);
    if ((insn & OP(~0)) != OP(1) || (delay & OP(~0)) != OP(2)
        || !is_delay_slot_optimized(delay, (val & 0x3c0000) != 0) || !is_branch_target_near(val)
        || (sparc_arch_size == 64 && (current_architecture < SPARC_OPCODE_ARCH_V9)))
        return false;
    return true;
}

bool is_delay_slot_optimized(long delay, bool arch_validation) {
    if ((delay & OP3(~0)) != OP3(0x3d)
        && ((delay & OP3(0x28)) != 0
            || ((delay & RD(~0)) != RD(15)))
        && (!arch_validation || ((delay & RS1(~0)) == RS1(15)
            || ((delay & F3I(~0)) == 0
                && (delay & RS2(~0)) == RS2(15)))))
        return false;
    return true;
}

bool is_branch_target_near(offsetT val) {
    if ((val & 0x3fe00000) && (val & 0x3fe00000) != 0x3fe00000)
        return false;
    return true;
}

void apply_pcrel_optimization(char *buf, long *insn, offsetT val) {
    if (INSN_BIG_ENDIAN)
        bfd_putb32(INSN_NOP, buf + 4);
    else
        bfd_putl32(INSN_NOP, buf + 4);

    if ((val & 0x3c0000) == 0) {
        *insn = INSN_BPA | (val & 0x7ffff);
    } else {
        *insn = INSN_BA | (val & 0x3fffff);
    }
}

long get_delay_slot(char *buf) {
    long delay;
    if (INSN_BIG_ENDIAN)
        delay = bfd_getb32(buf);
    else
        delay = bfd_getl32(buf);
    return delay;
}

bool apply_reloc_sparc_11(long *insn, offsetT val, fixS *fixP) {
    if (!in_signed_range(val, 0x7ff))
        return log_overflow_error(fixP);
    *insn |= val & 0x7ff;
    return true;
}

bool apply_reloc_sparc_10(long *insn, offsetT val, fixS *fixP) {
    if (!in_signed_range(val, 0x3ff))
        return log_overflow_error(fixP);
    *insn |= val & 0x3ff;
    return true;
}

void handle_other_relocs(char *buf, long *insn, int fx_r_type, offsetT val, fixS *fixP) {
    // Additional cases and pointers can be added here to handle different relocation types
}


/* Translate internal representation of relocation info to BFD target
   format.  */

arelent **tc_gen_reloc(asection *section, fixS *fixp) {
    static arelent *relocs[3];
    arelent *reloc;
    bfd_reloc_code_real_type code;
    const char *fx_addsy_name = (fixp->fx_addsy != NULL) ? S_GET_NAME(fixp->fx_addsy) : "";

    reloc = notes_alloc(sizeof(arelent));
    if (!reloc) {
        return NULL;
    }

    reloc->sym_ptr_ptr = notes_alloc(sizeof(asymbol *));
    if (!reloc->sym_ptr_ptr) {
        return NULL;
    }

    relocs[0] = reloc;
    relocs[1] = NULL;
    *reloc->sym_ptr_ptr = symbol_get_bfdsym(fixp->fx_addsy);
    reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;

    if (generic_force_reloc(fixp) && sparc_pic_code) {
        switch (fixp->fx_r_type) {
            case BFD_RELOC_HI22:
                if (strcmp(fx_addsy_name, "_GLOBAL_OFFSET_TABLE_") == 0) {
                    code = BFD_RELOC_SPARC_PC22;
                } else {
                    code = BFD_RELOC_SPARC_GOT22;
                }
                break;
            case BFD_RELOC_LO10:
                if (strcmp(fx_addsy_name, "_GLOBAL_OFFSET_TABLE_") == 0) {
                    code = BFD_RELOC_SPARC_PC10;
                } else {
                    code = BFD_RELOC_SPARC_GOT10;
                }
                break;
            case BFD_RELOC_SPARC13:
                code = BFD_RELOC_SPARC_GOT13;
                break;
            case BFD_RELOC_32_PCREL_S2:
                code = BFD_RELOC_SPARC_WPLT30;
                break;
            default:
                code = fixp->fx_r_type;
                break;
        }
    } else {
        code = fixp->fx_r_type;
    }

    switch (fixp->fx_r_type) {
        case BFD_RELOC_8:
        case BFD_RELOC_16:
        case BFD_RELOC_32:
        case BFD_RELOC_64:
            if (fixp->fx_pcrel) {
                code = fixp->fx_r_type + (BFD_RELOC_8_PCREL - BFD_RELOC_8) + (fixp->fx_size - 1);
                fixp->fx_addnumber = fixp->fx_offset;
            }
            break;
        default:
            if (code == BFD_RELOC_SPARC_OLO10) {
                relocs[1] = notes_alloc(sizeof(arelent));
                relocs[2] = NULL;
                if (!relocs[1] || !(relocs[1]->sym_ptr_ptr = notes_alloc(sizeof(asymbol *)))) {
                    return NULL;
                }
                *relocs[1]->sym_ptr_ptr = symbol_get_bfdsym(section_symbol(absolute_section));
                relocs[1]->address = fixp->fx_frag->fr_address + fixp->fx_where;
                relocs[1]->howto = bfd_reloc_type_lookup(stdoutput, BFD_RELOC_SPARC13);
                relocs[1]->addend = fixp->tc_fix_data;
            }
            break;
    }

    if (bfd_section_flags(section) & SEC_DEBUGGING) {
        switch (code) {
            case BFD_RELOC_16: code = BFD_RELOC_SPARC_UA16; break;
            case BFD_RELOC_32: code = BFD_RELOC_SPARC_UA32; break;
            case BFD_RELOC_64: code = BFD_RELOC_SPARC_UA64; break;
            default: break;
        }
    }

    reloc->howto = bfd_reloc_type_lookup(stdoutput, code == BFD_RELOC_SPARC_OLO10 ? BFD_RELOC_LO10 : code);
    if (!reloc->howto) {
        as_bad_where(fixp->fx_file, fixp->fx_line, "internal error: can't export reloc type %d (`%s')", fixp->fx_r_type, bfd_get_reloc_code_name(code));
        relocs[0] = NULL;
        return relocs;
    }

    reloc->addend = (code != BFD_RELOC_32_PCREL_S2 && code != BFD_RELOC_SPARC_WDISP22 && code != BFD_RELOC_SPARC_WDISP16 && code != BFD_RELOC_SPARC_WDISP19 && code != BFD_RELOC_SPARC_WDISP10 && code != BFD_RELOC_SPARC_WPLT30 && code != BFD_RELOC_SPARC_TLS_GD_CALL && code != BFD_RELOC_SPARC_TLS_LDM_CALL) ? fixp->fx_addnumber : (symbol_section_p(fixp->fx_addsy) ? (section->vma + fixp->fx_addnumber + md_pcrel_from(fixp)) : fixp->fx_offset);

    return relocs;
}

/* We have no need to default values of symbols.  */

symbolS *md_undefined_symbol(const char *name) {
    (void)name; // Prevent unused variable warning
    return NULL;
}

/* Round up a section size to the appropriate boundary.  */

valueT md_section_align(valueT size) {
  return size;
}

/* Exactly what point is a PC-relative offset relative TO?
   On the sparc, they're relative to the address of the offset, plus
   its size.  This gets us to the following instruction.
   (??? Is this right?  FIXME-SOON)  */
long md_pcrel_from(fixS *fixP) {
  if (fixP == NULL || fixP->fx_frag == NULL) {
    return -1; // Indicate an error
  }

  long ret = fixP->fx_where + fixP->fx_frag->fr_address;

  if (!sparc_pic_code || fixP->fx_addsy == NULL || symbol_section_p(fixP->fx_addsy)) {
    ret += fixP->fx_size;
  }

  return ret;
}

/* Return log2 (VALUE), or -1 if VALUE is not an exact positive power
   of two.  */

#include <limits.h>

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

static void s_reserve(int ignore ATTRIBUTE_UNUSED) {
    char *name;
    symbolS *symbolP;
    int size, align = 0;

    char c = get_symbol_name(&name);
    char *p = input_line_pointer;
    restore_line_pointer(c);
    SKIP_WHITESPACE();

    if (*input_line_pointer != ',') {
        as_bad(_("Expected comma after name"));
        ignore_rest_of_line();
        return;
    }

    ++input_line_pointer;

    size = get_absolute_expression();
    if (size < 0) {
        as_bad(_("BSS length (%d) <0! Ignored."), size);
        ignore_rest_of_line();
        return;
    }

    *p = '\0';
    symbolP = symbol_find_or_make(name);
    *p = c;

    if (!startswith(input_line_pointer, ",\"bss\"") && !startswith(input_line_pointer, ",\".bss\"")) {
        as_bad(_("bad .reserve segment -- expected BSS segment"));
        return;
    }

    input_line_pointer += (input_line_pointer[2] == '.') ? 7 : 6;
    SKIP_WHITESPACE();

    if (*input_line_pointer == ',') {
        ++input_line_pointer;
        SKIP_WHITESPACE();
        
        if (*input_line_pointer == '\n') {
            as_bad(_("missing alignment"));
            ignore_rest_of_line();
            return;
        }

        align = get_absolute_expression();
        if (align < 0) {
            as_bad(_("negative alignment"));
            ignore_rest_of_line();
            return;
        }

        if (align != 0) {
            int temp = mylog2(align);
            if (temp < 0) {
                as_bad(_("alignment not a power of 2"));
                ignore_rest_of_line();
                return;
            }
            align = temp;
        }

        record_alignment(bss_section, align);
    }

    if (!S_IS_DEFINED(symbolP)) {
        if (!need_pass_2) {
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
            *pfrag = '\0';

            S_SET_SEGMENT(symbolP, bss_section);

            subseg_set(current_seg, current_subseg);

            S_SET_SIZE(symbolP, size);
        }
    } else {
        as_warn(_("Ignoring attempt to re-define symbol %s"), S_GET_NAME(symbolP));
    }

    demand_empty_rest_of_line();
}

#include <stdbool.h>

#define MAX_ERROR_MSG_SIZE 1024

static void handle_common_segment_error(char *input_line);

static bool parse_comma() {
    SKIP_WHITESPACE();
    if (*input_line_pointer != ',') {
        as_bad(_("Expected comma"));
        return false;
    }
    input_line_pointer++;
    return true;
}

static offsetT parse_expression(char *error_msg) {
    offsetT temp = get_absolute_expression();
    if (temp < 0) {
        as_bad(error_msg);
        ignore_rest_of_line();
    }
    return temp;
}

static void handle_symbol_definition(symbolS *symbolP, valueT size) {
    if (S_IS_DEFINED(symbolP) && !S_IS_COMMON(symbolP)) {
        as_bad(_("Ignoring attempt to re-define symbol"));
        ignore_rest_of_line();
    } else if (S_GET_VALUE(symbolP) != 0 && S_GET_VALUE(symbolP) != (valueT)size) {
        as_warn(_("Length of .comm \"%s\" is already %ld. Not changed to %ld."),
                S_GET_NAME(symbolP), (long)S_GET_VALUE(symbolP), (long)size);
    }
}

static void allocate_common_symbol(symbolS *symbolP, offsetT size, offsetT alignment) {
    S_SET_VALUE(symbolP, size);
    S_SET_ALIGN(symbolP, alignment);
    S_SET_SIZE(symbolP, size);
    S_SET_EXTERNAL(symbolP);
    S_SET_SEGMENT(symbolP, bfd_com_section_ptr);
}

static void handle_local_symbol(symbolS *symbolP, offsetT size, offsetT alignment) {
    segT old_sec = now_seg;
    int old_subsec = now_subseg;
    int align = alignment == 0 ? 0 : mylog2(alignment);

    if (align < 0) {
        as_bad(_("alignment not a power of 2"));
        ignore_rest_of_line();
        return;
    }

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

static void handle_data_segment(symbolS *symbolP, offsetT size) {
    input_line_pointer++;
    if (*input_line_pointer == '.')
        input_line_pointer++;
    if (!startswith(input_line_pointer, "bss\"") && !startswith(input_line_pointer, "data\"")) {
        handle_common_segment_error(input_line_pointer);
        return;
    }
    while (*input_line_pointer++ != '"');
    allocate_common_symbol(symbolP, size, parse_expression(_("positive alignment")));
}

static void handle_common_line(symbolS *symbolP, offsetT size) {
    offsetT alignment;
    SKIP_WHITESPACE();
    if (*input_line_pointer != '"') {
        alignment = parse_expression(_("negative alignment"));
        if (alignment == -1) return;
        if (symbol_get_obj(symbolP)->local)
            handle_local_symbol(symbolP, size, alignment);
        else
            allocate_common_symbol(symbolP, size, alignment);
    } else {
        handle_data_segment(symbolP, size);
    }
}

static void s_common(int ignore ATTRIBUTE_UNUSED) {
    char *name;
    char c = get_symbol_name(&name);
    char *p = input_line_pointer;
    restore_line_pointer(c);

    if (!parse_comma()) return;
    offsetT size = parse_expression(_("Length (%lu) out of range ignored"));
    if (size == -1) return;

    *p = 0;
    symbolS *symbolP = symbol_find_or_make(name);
    *p = c;

    handle_symbol_definition(symbolP, size);

    if (!parse_comma()) return;

    handle_common_line(symbolP, size);

    symbol_get_bfdsym(symbolP)->flags |= BSF_OBJECT;

    demand_empty_rest_of_line();
}

static void handle_common_segment_error(char *input_line) {
    char *p = input_line_pointer;
    while (*p && *p != '\n') p++;
    char c = *p;
    *p = '\0';
    as_bad(_("bad .common segment %s"), input_line + 1);
    *p = c;
    input_line_pointer = p;
    ignore_rest_of_line();
}

/* Handle the .empty pseudo-op.  This suppresses the warnings about
   invalid delay slot usage.  */

#include <signal.h>

static void s_empty(int ignore) {
    (void)ignore;  // Explicitly ignore unused parameter
    if (signal(SIGINT, SIG_IGN) == SIG_ERR) {
        perror("Error setting signal handler");
        exit(EXIT_FAILURE);
    }
    last_insn = NULL;
}

static void s_seg(int ignore ATTRIBUTE_UNUSED) {
    int offset = 0;   
    if (startswith(input_line_pointer, "\"text\"")) {
        offset = 6;
        s_text(0);
    } else if (startswith(input_line_pointer, "\"data\"")) {
        offset = 6;
        s_data(0);
    } else if (startswith(input_line_pointer, "\"data1\"")) {
        offset = 7;
        s_data1();
    } else if (startswith(input_line_pointer, "\"bss\"")) {
        offset = 5;
        subseg_set(data_section, 255);
    } else {
        as_bad(_("Unknown segment type"));
        demand_empty_rest_of_line();
        return;
    }
    input_line_pointer += offset;
}

static void s_data1(void) {
    if (subseg_set(data_section, 1) != SUCCESS) {
        handle_error("Failed to set sub-segment.");
        return;
    }
    if (!demand_empty_rest_of_line()) {
        handle_error("Unexpected tokens after the command.");
        return;
    }
}

#include <stdbool.h>

static void
s_proc(int ignore ATTRIBUTE_UNUSED)
{
    while (true)
    {
        if (is_end_of_stmt(*input_line_pointer))
        {
            ++input_line_pointer;
            break;
        }
        ++input_line_pointer;
    }
}

/* This static variable is set by s_uacons to tell sparc_cons_align
   that the expression does not need to be aligned.  */

static int sparc_no_align_cons = 0;

/* This handles the unaligned space allocation pseudo-ops, such as
   .uaword.  .uaword is just like .word, but the value does not need
   to be aligned.  */

static void s_uacons(int bytes) {
    sparc_no_align_cons = 1;
    cons(bytes);
    sparc_no_align_cons = 0;
}

/* This handles the native word allocation pseudo-op .nword.
   For sparc_arch_size 32 it is equivalent to .word,  for
   sparc_arch_size 64 it is equivalent to .xword.  */

static void s_ncons(int bytes ATTRIBUTE_UNUSED) {
    int size = (sparc_arch_size == 32) ? 4 : 8;
    cons(size);
}

/* Handle the SPARC ELF .register pseudo-op.  This sets the binding of a
   global register.
   The syntax is:

   .register %g[2367],{#scratch|symbolname|#ignore}
*/

static void s_register(int ignore ATTRIBUTE_UNUSED) {
    char c;
    int reg;
    int flags;
    char *regname = NULL;

    if (input_line_pointer[0] != '%' || input_line_pointer[1] != 'g' ||
        ((input_line_pointer[2] & ~1) != '2' && (input_line_pointer[2] & ~1) != '6') || 
        input_line_pointer[3] != ',') {
        as_bad(_("register syntax is .register %%g[2367],{#scratch|symbolname|#ignore}"));
    }
    reg = input_line_pointer[2] - '0';
    input_line_pointer += 4;

    if (*input_line_pointer == '#') {
        ++input_line_pointer;
        c = get_symbol_name(&regname);
        if (strcmp(regname, "scratch") && strcmp(regname, "ignore")) {
            as_bad(_("register syntax is .register %%g[2367],{#scratch|symbolname|#ignore}"));
        }
        regname = (regname[0] == 'i') ? NULL : (char *) "";
    } else {
        c = get_symbol_name(&regname);
    }

    if (sparc_arch_size == 64 && reg >= 2 && reg <= 7) {
        if (globals[reg]) {
            if ((regname && globals[reg] != (symbolS *) 1 &&
                 strcmp(S_GET_NAME(globals[reg]), regname)) ||
                (regname != NULL) != (globals[reg] != (symbolS *) 1)) {
                as_bad(_("redefinition of global register"));
            }
        } else {
            if (regname == NULL) {
                globals[reg] = (symbolS *) 1;
            } else {
                if (*regname && symbol_find(regname)) {
                    as_bad(_("Register symbol %s already defined."), regname);
                }
                globals[reg] = symbol_make(regname);
                flags = symbol_get_bfdsym(globals[reg])->flags;
                if (!*regname) {
                    flags &= ~(BSF_GLOBAL | BSF_LOCAL | BSF_WEAK);
                }
                if (!(flags & (BSF_GLOBAL | BSF_LOCAL | BSF_WEAK))) {
                    flags |= BSF_GLOBAL;
                }
                symbol_get_bfdsym(globals[reg])->flags = flags;
                S_SET_VALUE(globals[reg], reg);
                S_SET_ALIGN(globals[reg], reg);
                S_SET_SIZE(globals[reg], 0);
                S_SET_SEGMENT(globals[reg], absolute_section);
                S_SET_OTHER(globals[reg], 0);
                elf_symbol(symbol_get_bfdsym(globals[reg]))
                    ->internal_elf_sym.st_info = ELF_ST_INFO(STB_GLOBAL, STT_REGISTER);
                elf_symbol(symbol_get_bfdsym(globals[reg]))
                    ->internal_elf_sym.st_shndx = SHN_UNDEF;
            }
        }
    }

    restore_line_pointer(c);
    demand_empty_rest_of_line();
}

/* Adjust the symbol table.  We set undefined sections for STT_REGISTER
   symbols which need it.  */

void sparc_adjust_symtab(void) {
    for (symbolS *sym = symbol_rootP; sym != NULL; sym = symbol_next(sym)) {
        bfd_symbol_type *bfd_sym = symbol_get_bfdsym(sym);
        elf_symbol_type *elf_sym = elf_symbol(bfd_sym);

        if (ELF_ST_TYPE(elf_sym->internal_elf_sym.st_info) == STT_REGISTER &&
            elf_sym->internal_elf_sym.st_shndx == SHN_UNDEF) {
            S_SET_SEGMENT(sym, undefined_section);
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

#include <stdbool.h>

void sparc_cons_align(int nbytes) {
    if (!enforce_aligned_data || sparc_no_align_cons) {
        return;
    }

    int nalign = mylog2(nbytes);
    if (nalign <= 0) {
        return;
    }

    if (now_seg == absolute_section) {
        if ((abs_section_offset & ((1 << nalign) - 1)) != 0) {
            as_bad(_("misaligned data"));
        }
        return;
    }

    frag_var(rs_align_test, 1, 1, 0, NULL, nalign, NULL);
    record_alignment(now_seg, nalign);
}

/* This is called from HANDLE_ALIGN in tc-sparc.h.  */

void sparc_handle_align(fragS *fragp) {
    int count = fragp->fr_next->fr_address - fragp->fr_address - fragp->fr_fix;
    char *p = fragp->fr_literal + fragp->fr_fix;

    if (fragp->fr_type == rs_align_test) {
        if (count != 0) {
            as_bad_where(fragp->fr_file, fragp->fr_line, "misaligned data");
        }
        return;
    }

    if (fragp->fr_type == rs_align_code) {
        int fix = 0;

        if (count & 3) {
            fix = count & 3;
            memset(p, 0, fix);
            p += fix;
            count -= fix;
        }

        if (SPARC_OPCODE_ARCH_V9_P(max_architecture) && count > 8) {
            unsigned wval = (0x30680000 | count >> 2); // ba,a,pt %xcc, 1f
            if (INSN_BIG_ENDIAN) {
                number_to_chars_bigendian(p, wval, 4);
            } else {
                number_to_chars_littleendian(p, wval, 4);
            }
            p += 4;
            count -= 4;
            fix += 4;
        }

        if (INSN_BIG_ENDIAN) {
            number_to_chars_bigendian(p, 0x01000000, 4);
        } else {
            number_to_chars_littleendian(p, 0x01000000, 4);
        }

        fragp->fr_fix += fix;
        fragp->fr_var = 4;
    }
}

/* Some special processing for a Sparc ELF file.  */

void sparc_elf_final_processing(void) {
    unsigned int *e_flags = &elf_elfheader(stdoutput)->e_flags;
    
    if (sparc_arch_size == 64) {
        if (sparc_memory_model == MM_RMO) {
            *e_flags |= EF_SPARCV9_RMO;
        } else if (sparc_memory_model == MM_PSO) {
            *e_flags |= EF_SPARCV9_PSO;
        }
    } else if (current_architecture >= SPARC_OPCODE_ARCH_V9) {
        *e_flags |= EF_SPARC_32PLUS;
    }

    if (current_architecture == SPARC_OPCODE_ARCH_V9A) {
        *e_flags |= EF_SPARC_SUN_US1;
    } else if (current_architecture == SPARC_OPCODE_ARCH_V9B) {
        *e_flags |= EF_SPARC_SUN_US1 | EF_SPARC_SUN_US3;
    }
}

const char *sparc_cons(expressionS *exp, int size) {
    const char *sparc_cons_special_reloc = NULL;
    char *save = input_line_pointer;

    SKIP_WHITESPACE();
    if (strncmp(input_line_pointer, "%r_", 3) == 0) {
        size_t relocate_length = 0;
        if (startswith(input_line_pointer + 3, "disp")) {
            relocate_length = 7;
            sparc_cons_special_reloc = "disp";
        } else if (startswith(input_line_pointer + 3, "plt") && (size == 4 || size == 8)) {
            relocate_length = 6;
            sparc_cons_special_reloc = "plt";
        } else if (startswith(input_line_pointer + 3, "tls_dtpoff") && (size == 4 || size == 8)) {
            relocate_length = 13;
            sparc_cons_special_reloc = "tls_dtpoff";
        }

        if (sparc_cons_special_reloc) {
            input_line_pointer += relocate_length;
            bool invalid_size = false;

            switch (size) {
                case 1: invalid_size = (*input_line_pointer != '8'); break;
                case 2: invalid_size = (strncmp(input_line_pointer, "16", 2) != 0); break;
                case 4: invalid_size = (strncmp(input_line_pointer, "32", 2) != 0); break;
                case 8: invalid_size = (strncmp(input_line_pointer, "64", 2) != 0); break;
                default: invalid_size = true; break;
            }

            if (invalid_size) {
                as_bad(_("Illegal operands: Only %%r_%s%d allowed in %d-byte data fields"), sparc_cons_special_reloc, size * 8, size);
                input_line_pointer = save;
                return NULL;
            }

            input_line_pointer += 2;
            if (*input_line_pointer != '(') {
                as_bad(_("Illegal operands: %%r_%s%d requires arguments in ()"), sparc_cons_special_reloc, size * 8);
                input_line_pointer = save;
                return NULL;
            }

            int npar = 1;
            char *end = input_line_pointer + 1;
            while (*end && npar != 0) {
                if (*end == '(') npar++;
                else if (*end == ')') npar--;
                end++;
            }

            if (*(end - 1) != ')') {
                as_bad(_("Illegal operands: %%r_%s%d requires arguments in ()"), sparc_cons_special_reloc, size * 8);
                input_line_pointer = save;
                return NULL;
            }

            char c = *end;
            *end = '\0';
            expression(exp);
            *end = c;

            input_line_pointer = end;
            if (!is_end_of_stmt(*input_line_pointer) && *input_line_pointer != ',') {
                as_bad(_("Illegal operands: garbage after %%r_%s%d()"), sparc_cons_special_reloc, size * 8);
                input_line_pointer = save;
                return NULL;
            }
            SKIP_WHITESPACE();
        }
    }

    if (!sparc_cons_special_reloc) {
        expression(exp);
    }
    return sparc_cons_special_reloc;
}

/* This is called by emit_expr via TC_CONS_FIX_NEW when creating a
   reloc for a cons.  We could use the definition there, except that
   we want to handle little endian relocs specially.  */

void cons_fix_new_sparc(fragS *frag, int where, unsigned int nbytes, expressionS *exp, const char *sparc_cons_special_reloc) {
    bfd_reloc_code_real_type r = BFD_RELOC_64;

    if (nbytes == 1) {
        r = BFD_RELOC_8;
    } else if (nbytes == 2) {
        r = BFD_RELOC_16;
    } else if (nbytes == 4) {
        r = BFD_RELOC_32;
    }

    if (target_little_endian_data && nbytes == 4 && (now_seg->flags & SEC_ALLOC)) {
        r = BFD_RELOC_SPARC_REV32;
    }

#ifdef TE_SOLARIS
    if (!target_little_endian_data && sparc_arch_size != 64 && r == BFD_RELOC_64) {
        r = BFD_RELOC_32;
    }
#endif

    if (sparc_cons_special_reloc) {
        switch (*sparc_cons_special_reloc) {
            case 'd':
                switch (nbytes) {
                    case 1: r = BFD_RELOC_8_PCREL; break;
                    case 2: r = BFD_RELOC_16_PCREL; break;
                    case 4: r = BFD_RELOC_32_PCREL; break;
                    case 8: r = BFD_RELOC_64_PCREL; break;
                    default: abort();
                }
                break;
            case 'p':
                if (nbytes == 4) {
                    r = BFD_RELOC_SPARC_PLT32;
                } else if (nbytes == 8) {
                    r = BFD_RELOC_SPARC_PLT64;
                }
                break;
            default:
                if (nbytes == 4) {
                    r = BFD_RELOC_SPARC_TLS_DTPOFF32;
                } else if (nbytes == 8) {
                    r = BFD_RELOC_SPARC_TLS_DTPOFF64;
                }
                break;
        }
    } else if (sparc_no_align_cons || strcmp(now_seg->name, ".eh_frame") == 0) {
        switch (nbytes) {
            case 2: r = BFD_RELOC_SPARC_UA16; break;
            case 4: r = BFD_RELOC_SPARC_UA32; break;
#ifdef TE_SOLARIS
            case 8:
                if (sparc_arch_size == 64) {
                    r = BFD_RELOC_SPARC_UA64;
                } else {
                    r = BFD_RELOC_SPARC_UA32;
                }
                break;
#else
            case 8: r = BFD_RELOC_SPARC_UA64; break;
#endif
            default: abort();
        }
    }

    fix_new_exp(frag, where, nbytes, exp, 0, r);
}

#define CFI_CFA_32BIT  0
#define CFI_CFA_64BIT  0x7ff
#define SPARC_ARCH_64BIT 64

void sparc_cfi_frame_initial_instructions(void) {
    int cfa_offset = (sparc_arch_size == SPARC_ARCH_64BIT) ? CFI_CFA_64BIT : CFI_CFA_32BIT;
    cfi_add_CFA_def_cfa(14, cfa_offset);
}

#include <errno.h>
#include <limits.h>
#include <stdlib.h>

int sparc_regname_to_dw2regnum(const char *regname) {
    if (!regname || !*regname) return -1;

    switch (regname[0]) {
        case 'g':
        case 'o':
        case 'l':
        case 'i':
            if (regname[1] >= '0' && regname[1] <= '7' && !regname[2]) {
                return (regname[0] - 'g') * 8 + (regname[1] - '0');
            }
            return -1;
        case 's':
            if (regname[1] == 'p' && !regname[2]) return 14;
            return -1;
        case 'f':
            if (regname[1] == 'p' && !regname[2]) return 30;
        case 'r':
            char* end;
            errno = 0;
            unsigned long regnum = strtoul(regname + 1, &end, 10);
            if (errno || *end || regnum >= ((regname[0] == 'f' && SPARC_OPCODE_ARCH_V9_P(max_architecture)) ? 64 : 32)) return -1;
            if (regname[0] == 'f') {
                regnum += 32;
                if (regnum >= 64 && (regnum & 1)) return -1;
            }
            return (int)regnum;
        default:
            return -1;
    }
}

void sparc_cfi_emit_pcrel_expr(expressionS *exp, unsigned int nbytes) {
    if (exp == NULL) return;
    sparc_no_align_cons = 1;
    emit_expr_with_reloc(exp, nbytes, "disp");
    sparc_no_align_cons = 0;
}

