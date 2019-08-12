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
  add some binary clauses for speed-up
  --------------------------------------------------------------
*/

#include "config.h"

#include "general.h"
#include "hash.h"
#include "statistics.h"
#include "list.h"
#include "table.h"

#include "veriT-DAG.h"
#include "DAG-ptr.h"
#include "recursion.h"

#include "bclauses.h"

#if STATS_LEVEL > 1
static unsigned stat_nb_bclauses;
#endif

/*--------------------------------------------------------------*/

static Thash assoc_table = NULL;

struct TSbassoc
{
  TDAG DAG1;
  TDAG DAG2;
  Tlist atoms;
};
typedef struct TSbassoc * Tbassoc;

/*--------------------------------------------------------------*/

static unsigned
assoc_hash(Tbassoc assoc)
{
  return (unsigned) ((uintptr_t) assoc->DAG1 ^ (uintptr_t) assoc->DAG2);
}

/*--------------------------------------------------------------*/

static int
assoc_equal(Tbassoc assoc1, Tbassoc assoc2)
{
  return assoc1->DAG1 == assoc2->DAG1 && assoc1->DAG2 == assoc2->DAG2;
}

/*--------------------------------------------------------------*/

static void
assoc_free(Tbassoc assoc)
{
  if (assoc->atoms)
    list_free(&assoc->atoms);
  free(assoc);
}

/*--------------------------------------------------------------*/

static void
assoc_add(TDAG DAG1, TDAG DAG2, TDAG atom)
{
  struct TSbassoc Sassoc;
  Tbassoc assoc;
  Sassoc.DAG1 = DAG1;
  Sassoc.DAG2 = DAG2;
  assoc = hash_lookup(assoc_table, &Sassoc);
  if (assoc)
    {
      assoc->atoms = list_cons(DAG_ptr_of(atom), assoc->atoms);
      return;
    }
  MY_MALLOC(assoc, sizeof(struct TSbassoc));
  assoc->DAG1 = DAG1;
  assoc->DAG2 = DAG2;
  assoc->atoms = list_cons(DAG_ptr_of(atom), NULL);
  hash_insert(assoc_table, assoc);
}

/*--------------------------------------------------------------*/

static Tlist
assoc_check(TDAG DAG1, TDAG DAG2)
{
  struct TSbassoc Sassoc;
  Tbassoc assoc;
  Sassoc.DAG1 = DAG1;
  Sassoc.DAG2 = DAG2;
  assoc = hash_lookup(assoc_table, &Sassoc);
  if (!assoc)
    return NULL;
  return assoc->atoms;
}

/*--------------------------------------------------------------*/

static void
add_atom(TDAG src)
{
  unsigned i;
  TDAG DAG1 = DAG_NULL, DAG2 = DAG_NULL;
  if (!DAG_ground(src))
    return;
  if (DAG_symb(src) != PREDICATE_EQ)
    return;
  if (DAG_symb(DAG_arg0(src)) != DAG_symb(DAG_arg1(src)) ||
      !DAG_arity(DAG_arg0(src)) ||
      DAG_arity(DAG_arg0(src)) != DAG_arity(DAG_arg1(src)))
    return;
  for (i = 0; i < DAG_arity(DAG_arg0(src)); i++)
    if (DAG_arg(DAG_arg0(src), i) == DAG_arg(DAG_arg1(src), i))
      continue;
    else if (DAG_arg(DAG_arg0(src), i) < DAG_arg(DAG_arg1(src), i))
      {
	if (!DAG1)
	  {
	    DAG1 = DAG_arg(DAG_arg0(src), i);
	    DAG2 = DAG_arg(DAG_arg1(src), i);
	    continue;
 	  }
	if (DAG1 == DAG_arg(DAG_arg0(src), i) &&
            DAG2 == DAG_arg(DAG_arg1(src), i))
	  continue;
	else
	  return;
     }
    else
      {
	if (!DAG1)
	  {
	    DAG1 = DAG_arg(DAG_arg1(src), i);
	    DAG2 = DAG_arg(DAG_arg0(src), i);
	    continue;
	  }
	if (DAG1 == DAG_arg(DAG_arg1(src), i) &&
            DAG2 == DAG_arg(DAG_arg0(src), i))
	  continue;
	else
	  return;
      }
  assoc_add(DAG1, DAG2, src);
}

/*--------------------------------------------------------------*/

static Ttable binary_clauses = NULL;

static void
check_atom(TDAG src)
{
  Tlist tmp, atoms;
  if (DAG_symb(src) != PREDICATE_EQ || DAG_arg0(src) == DAG_arg1(src))
    return;
  if (DAG_arg0(src) < DAG_arg1(src))
    atoms = assoc_check(DAG_arg0(src), DAG_arg1(src));
  else
    atoms = assoc_check(DAG_arg1(src), DAG_arg0(src));
  if (!atoms)
    return;
  tmp = atoms;
  do
    {
      TDAG DAG = DAG_dup(DAG_or2(DAG_not(src), DAG_of_ptr(list_car(tmp))));
      table_push(binary_clauses, DAG_ptr_of(DAG));
      tmp = list_cdr(tmp);
    }
  while (tmp != atoms);
}

/*--------------------------------------------------------------*/

#ifdef TERNARY_CLAUSES

static Ttable aux_symb_table = NULL;

static void
add_pred(TDAG src)
{
  Ttable table;
  if (DAG_symb(src) == PREDICATE_EQ)
    {
      if (DAG_arg0(src) < DAG_arg1(src))
	assoc_add(DAG_arg0(src), DAG_arg1(src), src);
      else
	assoc_add(DAG_arg1(src), DAG_arg(src, 2), src);
      return;
    }
  if (boolean_connector(DAG_symb(src)) ||
      DAG_sort(src) != SORT_BOOLEAN ||
      quantifier(DAG_symb(src)) ||
      DAG_symb_interpreted(DAG_symb(src)))
    return;
  if (DAG_symb(src)->misc)
    table = table_get(aux_symb_table, DAG_symb(src)->misc);
  else
    {
      DAG_symb(src)->misc = table_length(aux_symb_table);
      table = table_new(10,10);
      table_push(aux_symb_table, table);
    }
  table_push(table, DAG_ptr_of(src));
}

/*--------------------------------------------------------------*/

static void
tclause_aux(TDAG DAGa, TDAG DAGb)
{
  unsigned i;
  TDAG DAG1 = NULL, DAG2, DAG3;
  for (i = 0; i < DAG_arity(DAGa); i++)
    if (DAG_arg(DAGa, i) == DAG_arg(DAGb, i))
      continue;
    else if (DAG_arg(DAGa, i) < DAG_arg(DAGb, i))
      {
	if (!DAG1)
	  {
	    DAG1 = DAG_arg(DAGa, i);
	    DAG2 = DAG_arg(DAGb, i);
	    continue;
	  }
	if (DAG1 == DAG_arg(DAGa, i) && DAG2 == DAG_arg(DAGb, i))
	  continue;
	else
	  return;
      }
    else
      {
	if (!DAG1)
	  {
	    DAG1 = DAG_arg(DAGa, i);
	    DAG2 = DAG_arg(DAGb, i);
	    continue;
	  }
	if (DAG1 == DAG_arg(DAGa, i) && DAG2 == DAG_arg(DAGb, i))
	  continue;
	else
	  return;
      }
  if (!assoc_check(DAG1,DAG2))
    return;
  DAG3 = DAG_not(DAG_eq(DAG1,DAG2));
  table_push(binary_clauses, DAG_ptr_of(DAG_dup(DAG_or3(DAG3, DAGa, DAG_not(DAGb)))));
  table_push(binary_clauses, DAG_ptr_of(DAG_dup(DAG_or3(DAG3, DAG_not(DAGa), DAGb)));
}

/*--------------------------------------------------------------*/

static void
tclause(TDAG src)
{
  unsigned i, j, k;
  aux_symb_table = table_new(10,10);
  table_push(aux_symb_table, NULL);
  structural_recursion_void(src, add_pred);
  for (i = 1; i < table_length(aux_symb_table); i++)
    {
      Ttable table = table_get(aux_symb_table, i);
      for (j = 0; j < table_length(table); j++)
	for (k = j + 1; k < table_length(table); k++)
	  tclause_aux(DAG_of_ptr(table_get(table, j)),
		      DAG_of_ptr(table_get(table, k)));
    }
  for (i = 1; i < table_length(aux_symb_table); i++)
    {
      Ttable table = (Ttable) table_get(aux_symb_table, i);
      TDAG DAG = DAG_of_ptr(table_get(table, 0));
      DAG_symb_set_misc(DAG_symb(DAG), 0);
      table_free(&table);
    }
  table_free(&aux_symb_table);
}
#endif

/*--------------------------------------------------------------*/

TDAG
bclauses_add(TDAG src)
{
  unsigned i;
  TDAG dest, *PDAG;
  binary_clauses = table_new(10, 10);
  assoc_table = hash_new(256, (TFhash) assoc_hash,
			 (TFequal) assoc_equal,
			 (TFfree) assoc_free);
  structural_recursion_void(src, add_atom);
  structural_recursion_void(src, check_atom);
  hash_free(&assoc_table);

#ifdef TERNARY_CLAUSES
  assoc_table = hash_new(256, (TFhash) assoc_hash,
			 (TFequal) assoc_equal,
			 (TFfree) assoc_free);
  tclause(src);
  hash_free(&assoc_table);
#endif

  i = table_length(binary_clauses) +
    ((DAG_symb(src) == CONNECTOR_AND) ? DAG_arity(src) : 1u);
  MY_MALLOC(PDAG, i * sizeof(TDAG));
  for (i = 0; i < table_length(binary_clauses); i++)
    PDAG[i] = DAG_of_ptr(table_get(binary_clauses, i));
  if (DAG_symb(src) != CONNECTOR_AND)
    {
      PDAG[i] = src;
      i++;
    }
  else
    {
      unsigned n = table_length(binary_clauses);
      for (i = 0; i < DAG_arity(src); i++)
	PDAG[i + n] = DAG_arg(src, i);
      i = n + DAG_arity(src);
    }
#if STATS_LEVEL > 1
  stats_counter_add(stat_nb_bclauses, table_length(binary_clauses));
#endif
  dest = DAG_dup(DAG_new(CONNECTOR_AND, i, PDAG));
  table_apply(binary_clauses, (TFapply) DAG_free);
  table_free(&binary_clauses);
  return dest;
}

/*--------------------------------------------------------------*/

void
bclauses_init(void)
{

#if STATS_LEVEL > 1
  stat_nb_bclauses =
    stats_counter_new("bclauses",
		      "Number of binary clauses generated in preprocessing",
		      "%5d");
#endif
}

/*--------------------------------------------------------------*/

void
bclauses_done(void)
{
}
