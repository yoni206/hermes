/*
Copyright (c) 2009-2013, INRIA, Universite de Nancy 2 and Universidade
Federal do Rio Grande do Norte.
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
   * Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
   * Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
   * Neither the name of the Universite de Nancy 2 or the Universidade Federal
     do Rio Grande do Norte nor the names of its contributors may be used
     to endorse or promote products derived from this software without
     specific prior written permission.

THIS SOFTWARE IS PROVIDED BY INRIA, Universite de Nancy 2 and
Universidade Federal do Rio Grande do Norte ''AS IS'' AND ANY EXPRESS
OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL INRIA, Université de Nancy 2 and
Universidade Federal do Rio Grande do Norte BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

/**
   \mainpage veriT documentation

   \section intro_sec Introduction

   veriT is a Satisfiability Modulo Theory (SMT) solver.

   The solver is currently integrating a quantifier instantiation mechanism with
   decision procedures for the following: uninterpreted functions with equality,
   linear arithmetics on the real numbers, and semi-decision procedures for
   linear arithmetics on the integers. There is also experimental support
   for non-linear arithmetics on the real
   numbers (using third-party tool <a href="http://www.redlog.eu">Redlog</a>).

   \section execution_sec Execution

   The input of the solver is a proof obligation in one of the
   following formats:

   - SMT-LIB 2.0: This is the default input format and may be employed
   as long as interactive features and incrementality are not used.
   See http://www.smtlib.org for information on this format.

   - DIMACS: This format may be employed when one wants to use
   veriT as a SAT-solver (with proof production capabilities).

   SMT-LIB 1.2 is not supported.

   The solver may be executed in two modes: batch and interactive.

   In batch mode the solver expects as argument the name of a file name in one
   of the supported formats. In interactive mode the solver expects a series of
   supported SMT-LIB 2.0 commands. Several formulas may be added, and they are
   conjunctively checked for satisfiability. There is no provision for
   backtracking or incrementality.

   veriT may be used to produce proofs: when the result is unsat, a derivation
   of the result might be produced and checked by a third party. Proof
   production is only available in batch mode.

   Command-line options may be used to output information about the
   proof obligation or about the proof process itself into files or
   to the standard output stream. See the specific documentation
   modules for \ref arguments_user and \ref arguments_developer.

   \section smtlib_2_sec Support for SMT-LIB 2.0

   - Logics for which veriT is complete and proof-producing:
     - QF_LRA
     - QF_RDL
     - QF_UFLRA
     - QF_UF

   - Logics for which veriT is incomplete and proof-producing:
     - LRA
     - QF_IDL
     - QF_LIA
     - QF_UFIDL
     - QF_UFLIA
     - UFLRA
     - UFNIA

   - Logics for which veriT is incomplete:
     - AUFLIA
     - AUFLIRA
     - AUFNIRA
     - QF_AUFLIA
     - QF_AX
     - QF_NIA
     - QF_NRA
     - QF_UFNRA

   - veriT does not support logics with bit vectors (BV).

   The following commands are supported:
   - set-logic
   - set-info: :status and :version are supported.
   - get-info: :error-behavior, :name, :version, :authors, :status are supported.
   - set-option: :diagnostic-output-channel, :regular-output-channel,
   :print-success are supported.
   - get-option: only for the options listed with set-option
   - declare-sort
   - declare-fun
   - define-fun
   - assert
   - check-sat
   - exit

   The following commands are parsed but are not supported:
   - push
   - pop
   - define-sort
   - get-assertions
   - get-unsat-core
   - get-value
   - get-assignment
   - get-proof

   veriT currently does not support indexed symbols as identifiers.

   \section install_sec Installation

   The source code is available on the Web at
   http://www.verit-solver.org/ , along with a series of binaries.

   To install the solver from the sources, once it is downloaded and unpacked,
   change to the top level directory and set the values in the file
   "Makefile.variables". Run the command line make.  This will automatically
   fetch some third-party components and compile the sources. To include support
   for non-linear arithmetics, the user needs to install Redlog (available at
   http://www.redlog.eu) in the directory extern/reduce. Once the build is
   complete, copy the binary program, named "veriT", to the location of your
   choice.

   \section licence_sec Licence

   veriT is distributed under the free BSD license. It uses LGPL library GMP,
   a parser generated by flex/bison, and, optionally, Redlog.

   \section authors_sec Authors

   Pascal Fontaine, David Deharbe are the two main developpers. Additional
   contributors include Diego Caminha, Thomas Bouton and Pablo Federico Dobal.

   The solver is being developed by the <a
   href="http://sites.google.com/site/forallufrn/people">ForAll</a>
   group at <a href="http://www.ufrn.br">Universidade Federal do Rio
   Grande do Norte</a> (Brazil) and the <a
   href="http://veridis.loria.fr">VeriDis</a> group at <a
   href="http://www.univ-lorraine.fr">Universit&eacute; de Lorraine</a> and
   <a href="http://www.loria.fr">LORIA</a> (France).

   \defgroup arguments_user Options

   \defgroup arguments_developer Developer options */

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#ifdef DEBUG
#ifdef MACOS
#include <unistd.h>
#endif
#endif
#include "config.h"

#include "general.h"
#include "options.h"
#include "statistics.h"
#include "sys.h"

#include "veriT.h"
#include "complete.h"
#include "DAG-print.h"
#include "DAG.h"
#ifdef NLA
#include "nla.h"
#endif
#include "pre.h"
#ifdef PROOF
#include "proof.h"
#endif
#include "dimacs.h"
#include "smtlib2.h"
#include "tptp.h"

/* TODO: make sure veriT_init contains EVERYTHING to initialise.
   Now, options and stats are outside */


/** \addtogroup arguments_user

   - --version

   veriT prints the current version identifier and exits. */
static bool option_version_and_exit = false;

/** \addtogroup arguments_user

   - --disable-banner

   The message identifying the program is not printed to stdout. */
static bool option_disable_banner;

#ifdef PROOF
/** \addtogroup arguments_developer

   - --print-proof-format-and-exit

   Loads formula, expands macros, applies selected simplifications,
   and prints on stdout in SMT format. */
/** \todo update 2.0: Only for SMT-LIB 1.2.  From 2.0 on, use commands. */
static bool option_proof_format_and_exit;

#endif

/** \addtogroup arguments_developer

   - --print-simp-and-exit

   Loads formula, expands macros, applies selected simplifications,
   and prints on stdout in SMT format. */
/** \todo update 2.0: Only for SMT-LIB 1.2.  From 2.0 on, use commands. */
bool option_print_simp_and_exit;

#ifdef OPTION_CHECK_TIME
/** \addtogroup arguments_user

   - --max-time=n

   Sets maximal execution time to n (in seconds). Caveat: the
   execution time limit is individual to each process (i.e. the main
   process and the possible calls to external provers). */
int option_max_time = 0;
#endif

/** \addtogroup arguments_user

   - --input=(smtlib2|dimacs)

   Sets the input format (smtlib2 is default). */
static char * input_format = NULL;

/** \addtogroup arguments_developer

   - --output=smtlib2

   Sets the output format (smtlib2 is default). Meaningful only when output formulas are produced. */
char * output_format = NULL;

/** \addtogroup arguments_user

   - --disable-print-success

   Overrides the default SMT-LIB 2 behavior regarding the option
   :print-success. */
static bool option_disable_print_success = false;

/**
   @}
*/

static char *filename = NULL;

/*
  --------------------------------------------------------------
  Some output
  --------------------------------------------------------------
*/

static void
output_version_and_exit(FILE * out)
{
  fprintf(out, "This is %s, version %s\n", PROGRAM_NAME, PROGRAM_VERSION);
  veriT_exit(0);
}

static void
output_banner(FILE * out)
{
  if (option_disable_banner == 0)
    fprintf(out, "%s %s - the SMT-solver veriT (UFRN/LORIA).\n",
            PROGRAM_NAME, PROGRAM_VERSION);
}

/*
  --------------------------------------------------------------
  Core function
  --------------------------------------------------------------
*/

static Tstack_Pchar filename_table = NULL;
static FILE * input_file = NULL;

static void
set_options(void)
{
  /* DD+PF setup, declare and parse options */
  options_setup(filename_table, PROGRAM_NAME, PROGRAM_VERSION,
                PROGRAM_MAIL, "FILENAME",
                "the veriT solver "
                "-- checking verification conditions with Theories.",
                "\nPlease notice that symbol names beginning"
                " with veriT__ or ?veriT__ are reserved.\n", "VERIT_");
  options_new(0, "version",
              "Prints version identifier and exits",
              &option_version_and_exit);
  options_new_string('i', "input", "input format (smtlib2 is default)",
                     "(smtlib2|dimacs)", &input_format);
  input_format = strmake("smtlib2");
  options_new_string('o', "output", "output format (smtlib2 is default)",
                     "(smtlib2|b|py_graph)", &output_format);
  output_format = strmake("smtlib2");
#ifdef PROOF
  options_new(0, "proof-format-and-exit",
              "Print proof format on stdout and exits",
              &option_proof_format_and_exit);
#endif
  options_new(0, "print-simp-and-exit",
              "Loads formula, simplifies," "and print on stdout (smt)",
              &option_print_simp_and_exit);
  options_new(0, "print-flat", "print formula in flattened mode"
              " (no shared subterms or formulas)", &DAG_fprint_opt.flat);
  options_new(0, "disable-banner", "disable printing of program banner",
              &option_disable_banner);
  options_new(0, "disable-print-success", "cancel SMT-LIB 2 default",
              &option_disable_print_success);
#ifdef OPTION_CHECK_TIME
  options_new_int(0, "max-time", "Exit when time is exceeded",
                  "SECONDS", &option_max_time);
#endif
#ifdef NLA
  options_new_string(0, "reduce-path", "full path of redpsl",
                     "path", &reduce_path);
#endif
}
#define STATS_LEVEL 1

/*--------------------------------------------------------------*/

int
main(int argc, char **argv)
{
#ifdef DEBUG
  setbuf(stdout, 0);		/* makes it easier to catch bugs */
#endif
  stats_init();
  veriT_init();
  DAG_smtlib_logic_init();

  stack_INIT(filename_table);

  set_options();
  options_parse(argc, argv);
  veriT_set();

  if (option_version_and_exit)
    output_version_and_exit(stdout);

  /* DD+PF output some basic information */
  output_banner(stdout);

#ifdef PROOF
  if (option_proof_format_and_exit)
    {
      proof_doc(stdout);
      proof_satisfiable();
      veriT_exit(0);
    }
#endif

  /*
  if (veriT_print_report)
    options_fprint(stdout);
  */
  if (stack_size(filename_table) > 1)
    {
      fprintf(stderr, "Only one file name is allowed\n");
      options_usage(stderr);
      veriT_exit(-1);
    }

  if (stack_size(filename_table) == 1)
    {
      /* DD+PF parse file */
      filename = stack_get(filename_table, 0);
      input_file = sys_open_file(filename, "r");
#ifdef PROOF
      proof_set_input_file(filename);
#endif
    }
  else
    input_file = stdin;
#ifdef PROOF
  if (option_proof_file_from_input ||
      option_proof_filename ||
      option_proof_stat)
    proof_on = true;
#endif
  if (!strcmp(input_format,"smtlib2"))
    parse_smtlib2(input_file, option_disable_print_success);
  else if (!strcmp(input_format,"dimacs"))
    parse_dimacs(input_file);
  else if (!strcmp(input_format,"tptp"))
    parse_tptp(input_file, filename, option_disable_print_success);

  if (input_file != stdin)
    sys_close_file(input_file);

  veriT_exit(0);
  return 0; /* no gcc warning */
}
