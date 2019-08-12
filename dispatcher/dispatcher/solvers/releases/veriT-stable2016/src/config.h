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

/*
  --------------------------------------------------------------
  Configuration files
  --------------------------------------------------------------
*/

#ifndef __CONFIG_H
#define __CONFIG_H

#define PROGRAM_NAME ("veriT")
#define PROGRAM_VERSION ("stable2016")
#define PROGRAM_MAIL ("\042verit-bugs@lists.gforge.inria.fr\042")

#define HASH_ADAPTIVE_SIZE
/* PF double the size of the hash table when
   size < (nb << HASH_ADAPTIVE_RATIO) */
enum {
  HASH_ADAPTIVE_RATIO = 2
};

/* PF include proof producing code */
#ifdef PROOF
#define OPT_PROOF(a) a
#define OPTC_PROOF(a) ,a
#define PROOFID Tproof
#define PROOFRETURN return
#else
#define OPT_PROOF(a)
#define OPTC_PROOF(a)
#define PROOFID void
#define PROOFRETURN
#endif

/* #define DEBUG_PROOF */

/* DD+PF This is automatically set using make debug.
   No need to set it here */
/* #define DEBUG */

/* PF Outputs a cnf file for the Boolean abstraction of
   the input formula, conflict clauses, and lemmas with the
   check_deduced option.
   Should be sat iff the input is
   Options only compiled if DEBUG is set.
   Better leave it defined
   Incompatible with proof production */
#define DEBUG_RECHECK_UNSAT

/* option to filter literals according to polarity for theories */
#define POLARITY_FILTER MAGIC PARAM

/* options for (SMT) parser */
/* #define DEBUG_PARSER */

/* options for HOL treatment (lambda, apply, etc.) */
/* #define DEBUG_HOL */

/* options for Nelson & Oppen */
/* #define DEBUG_NO */
/* #define DEBUG_CONFLICT_CLAUSE */

/* options for Boolean module */
/* #define DEBUG_BOOL */
/* #define BOOL_STAT */

/* options for conjunctive normal form module */
/* #define DEBUG_CNF */
/* #define STATS_CNF */

/* options for congruence closure */
/* #define DEBUG_CC */

/* options for DAGs */
/* PF supplementary tests for DAG */
/* #define DAG_CHECK */
/* #define DEBUG_DAG */
/* PF gives some statistics about hashing within this modules */
/* #define DAG_STATS */

/* options for quantifier handling */
/* #define DEBUG_QNT_TIDY */

/* options for skolemization */
/* #define DEBUG_SKOLEM */

/* options for arith module */
/* #define DEBUG_ARITH */

/* DC Ignores the logic of the formula and forces the use of linear arithmetic module */
/* #define LINEAR_ARITHMETIC */

/* DC Ignores the logic of the formula and forces the use of difference logic module */
/* #define DIFFERENCE_LOGIC */

/* options for linear arith module */
/* #define DEBUG_LA */

/* options for difference logic module */
/* #define DEBUG_DL */
/* #define DEBUG_DL_DATA_STATE */

/* option for testing arithmetic only theory, i.e., it will not use NO */
/* #define PURE_ARITH */

/* options for E prover module */
/* #define DEBUG_E */
/* #define DEBUG_TSTP_PARSER */
/* #define DEBUG_TSTPFUN */

/* options for the Herbrand module */
/* #define DEBUG_HERBRAND */

/* PS options for Tom */
/* #define DEBUG_TOM */

/* PS+PF options for unit_simplification */
/* #define DEBUG_US */

/* PF STATS_LEVEL may be 0, 1, or 2
   0 No statistics at all
   1 Only statistics that do not consume computer time
   2 All statistics */
enum {
  STATS_LEVEL = 1
};

/* PF Add option to check if time exceeded
   Requires STATS_LEVEL > 0 */
#define OPTION_CHECK_TIME

#endif /* __CONFIG_H */
