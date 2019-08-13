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
  Conjunctive normal form
  --------------------------------------------------------------
*/

#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "config.h"
#include "general.h"
#include "options.h"
#include "statistics.h"

#include "bool.h"
#include "literal.h"
#include "DAG-print.h"
#include "veriT-DAG.h"
#include "cnf.h"
#include "proof.h"

/* #define DEBUG_CNF */
/* #define STATS_CNF */

/* PF clauses are added to the following list
   This is set to null before converting a formula. */
static Tstack_clause *PclausesL;

/* PF module option: 1 iff definitional normal (vs. p-definitional) form is used, 0 otherwise */
static bool cnf_definitional = false;

#ifdef STATS_CNF
/* PF module option: 1 iff cnf stats are output */
static bool cnf_stats;
#endif

#if STATS_LEVEL > 1
static unsigned stat_n_binary = 0;
static unsigned stat_n_naive = 0;
static unsigned stat_n_pdef = 0;
#endif

/*--------------------------------------------------------------*/

#ifdef PEDANTIC
typedef unsigned Tpolarity;
#else
typedef unsigned char Tpolarity;
#endif

#define POLARITY_NONE ((Tpolarity)0u)
#define POLARITY_POS  ((Tpolarity)1u)
#define POLARITY_NEG  ((Tpolarity)2u)
#define POLARITY_BOTH ((Tpolarity)3u)

#define inverse_polarities(x)						\
  ((Tpolarity)								\
   ((x == POLARITY_BOTH)?POLARITY_BOTH:					\
    ((x == POLARITY_NEG)?POLARITY_POS:					\
     ((x == POLARITY_POS)?POLARITY_NEG:POLARITY_NONE))))

/* PF records the number of literals that have a recorded polarity */
unsigned nb_polarities = 0;
/* PF for every literal, allocates an int to remember which polarities
   have already been produced */
Tpolarity * polarities = NULL;

/*--------------------------------------------------------------*/

/* PF associate a literal with a DAG
   wrapper to add polarities */
static Tlit
cnf_DAG_to_literal(TDAG DAG)
{
  Tlit lit = DAG_to_lit(DAG);
  while (lit_var(lit) >= nb_polarities)
    {
      unsigned i;
      MY_REALLOC(polarities, 2 * nb_polarities * sizeof(Tpolarity));
      for (i = nb_polarities, nb_polarities *= 2; i < nb_polarities; i++)
	polarities[i] = POLARITY_NONE;
    }
  return lit;
}

/*--------------------------------------------------------------*/

static void
cnf_literal_add_polarities(Tlit lit, Tpolarity pols)
{
  polarities[lit_var(lit)] |=
    (Tpolarity)(lit_pol(lit)?pols:inverse_polarities(pols));
}

/*--------------------------------------------------------------*/

static Tpolarity
cnf_literal_polarities(Tlit lit)
{
  if (lit_pol(lit))
    return polarities[lit_var(lit)];
  return inverse_polarities(polarities[lit_var(lit)]);
}


/*--------------------------------------------------------------*/

#ifdef STATS_CNF
/* PF print some statistics about CNF */
static void
statistics(FILE * file)
{
  unsigned i, j;
  unsigned nb_clauses = stack_size(*PclausesL);
  unsigned nb_lits = 0;
  unsigned pure = 0, unit = 0;
  unsigned *pos, *neg;
  assert(polarities);
  MY_MALLOC(pos, var_max * sizeof(unsigned));
  MY_MALLOC(neg, var_max * sizeof(unsigned));
  /* PF caution: keep those lines, even if duplicate in SAFE_MALLOC mode */
  memset(pos, 0, var_max * sizeof(unsigned));
  memset(neg, 0, var_max * sizeof(unsigned));
  for (i = 0; i < nb_clauses; i++)
    {
      Tclause clause = (Tclause) stack_get(*PclausesL, i);
      if (clause->nb_lits == 1)
	unit++;
      for (j = 0; j < clause->nb_lits; j++)
	if (lit_pol(clause->lits[j]))
	  pos[lit_var(clause->lits[j])]++;
	else
	  neg[lit_var(clause->lits[j])]++;
      nb_lits += clause->nb_lits;
    }
  for (i = 1; i < var_max; i++)
    if (!pos[i] || !neg[i])
      pure++;

  fprintf(file, "Number of variables : %d\n", var_max - 1);
  fprintf(file, "Number of clauses   : %u\n", nb_clauses);
  fprintf(file, "Number of literals  : %u\n", nb_lits);
  fprintf(file, "Aver. nb lit / cl   : %f\n", 1.0 * nb_lits / nb_clauses);
  fprintf(file, "Pure literals       : %u\n", pure);
  fprintf(file, "Unit clauses        : %u\n", unit);

  for (i = 1; i < var_max; i++)
    if (DAG_literal(var_to_DAG(i)))
      fprintf(file, "+Var %4u, pos %5u, neg %5u\n", i, pos[i], neg[i]);
    else
      fprintf(file, " Var %4u, pos %5u, neg %5u\n", i, pos[i], neg[i]);

  free(pos);
  free(neg);
}
#endif

/*--------------------------------------------------------------*/

#ifdef DEBUG_CNF
static void
clause_symbolic_fprint(FILE * file, Tclause clause)
{
  int i, prop_literal;
  assert(polarities);
  if (!clause)
    fprintf(file, "NULL clause");
  else if (clause->nb_lits == 0)
    fprintf(file, "Empty clause");
  else
    for (i = 0; i < clause->nb_lits; i++)
      {
	prop_literal = clause->lits[i];
	if (DAG_literal(var_to_DAG(lit_var(prop_literal))))
	  {
	    fprintf(file, lit_pol(prop_literal)? " ": " (not ");
	    DAG_fprint(file, var_to_DAG(lit_var(prop_literal)));
	    fprintf(file, lit_pol(prop_literal)? "" : ") ");
	  }
	else
	  fprintf(file, " %d", clause->lits[i]);
      }
  fprintf(file, "\n");
}
#endif

/*--------------------------------------------------------------*/

#if STATS_LEVEL > 1
static int
cnf_binary_count(Tstack_clause clauses)
{
  unsigned i;
  int counter = 0;
  for (i = 0; i < stack_size(clauses); ++i)
    if (stack_get(clauses, i)->nb_lits == 2)
	counter++;
  return counter;
}
#endif

/*
  --------------------------------------------------------------
  CNF computation
  --------------------------------------------------------------
*/

#define PROOF_FCT(A) A
#define PROOF_ARG(A)
#define VAR_CNF var_cnf
#define SILENT_CNF silent_cnf
#define clause_push_proof(a, b) stack_push(*PclausesL, a)

#include "cnf.c.tpl"

#ifdef PROOF

#undef PROOF_FCT
#undef PROOF_ARG
#define PROOF_FCT(A) A ## _proof
#define PROOF_ARG(A) , A
#undef VAR_CNF
#undef SILENT_CNF
#define VAR_CNF PROOF_FCT(var_cnf)
#define SILENT_CNF PROOF_FCT(silent_cnf)
#undef clause_push_proof
#define clause_push_proof(a, b) { a->proof_id = b; stack_push(*PclausesL, a); }

#include "cnf.c.tpl"

#endif /* PROOF */

/*
  --------------------------------------------------------------
  Init/Release
  --------------------------------------------------------------
*/

void
cnf_init(void)
{
  assert(!polarities);
  cnf_definitional = false;
  options_new(0, "cnf-definitional",
	      "Conjunctive normal form: "
	      "Use definitional normal form (instead of p-definitional)",
	      &cnf_definitional);
#if STATS_LEVEL > 1
  stat_n_binary =
    stats_counter_new("2cl", "Number of binary clauses in original problem", "%6d");
  stat_n_pdef =
    stats_counter_new("cnf_pdef", "Number of clauses in p-definitional CNF", "%6d");
#endif
#ifdef STATS_CNF
  cnf_stats = false;
  options_new(0, "cnf-stats",
	      "Conjunctive normal form:" " Print statistics", &cnf_stats);
#endif
  nb_polarities = 1;
  MY_MALLOC(polarities, nb_polarities * sizeof(Tpolarity));
}

/*--------------------------------------------------------------*/

void
cnf_done(void)
{
  assert(polarities);
  free(polarities);
  polarities = NULL;
  nb_polarities = 0;
}

/*--------------------------------------------------------------*/

void
cnf_reset(void)
{
  assert(polarities);
  memset(polarities, POLARITY_NONE, nb_polarities * sizeof(Tpolarity));
}
