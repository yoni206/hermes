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
  Module for skolemizing quantified formulas
  --------------------------------------------------------------
*/

#include "config.h"
#include "general.h"
#include "options.h"

#include "table.h"
#include "veriT-DAG.h"
#include "DAG-flag.h"
#include "DAG-prop.h"
#include "DAG-ptr.h"
#include "DAG-symb-DAG.h"
#include "HOL.h"
#include "polarities.h"
#include "qnt-trigger.h"
#include "recursion.h"
#include "skolem.h"

#define OPTC_OLDPROOF(a)

#ifdef OLDPROOF
#include "proof.h"
#endif

/* #define DEBUG_SKOLEM */

/**
   \addtogroup arguments_user

   - --enable-deep-skolem

   Enables application of deep Skolemization: Skolemizes
   within essentially universal quantifiers.

 */
static bool enable_deep_skolem = 0;

/*
  --------------------------------------------------------------
  Setting polarity bits
  --------------------------------------------------------------
*/

#if 0

#define GET_POL(F) (DAG_misc(F) & 3)
#define SET_POL(F, P) { DAG_misc(F) &= ~3; DAG_misc(F) |= P; }

/*--------------------------------------------------------------*/

static void
set_polarity(TDAG src, Tpol pol)
/* PF If src has polarity pol, set misc record for every subformula
   such that GET_POL returns the polarity(ies) of the subformula
   within src */
{
  int i;
  if ((GET_POL(src) & pol) == pol)
    return;
  SET_POL(src, GET_POL(src) | pol);
  if (DAG_symb(src) == CONNECTOR_ITE)
    {
      set_polarity(DAG_arg(src, 0), POL_BOTH);
      set_polarity(DAG_arg(src, 1), pol);
      set_polarity(DAG_arg(src, 2), pol);
      return;
    }
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      set_polarity(DAG_arg0(src), INV_POL (pol));
      set_polarity(DAG_arg1(src), pol);
      return;
    }
  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      set_polarity(DAG_arg0(src), INV_POL (pol));
      return;
    }
  if (DAG_symb(src) == CONNECTOR_EQUIV || DAG_symb(src) == CONNECTOR_XOR)
    {
      set_polarity(DAG_arg0(src), POL_BOTH);
      set_polarity(DAG_arg1(src), POL_BOTH);
      return;
    }
  if (DAG_symb(src) == CONNECTOR_OR || DAG_symb(src) == CONNECTOR_AND)
    {
      for (i = 0; i < DAG_arity(src); i++)
        set_polarity(DAG_arg(src, i), pol);
      return;
    }
  if (quantifier(DAG_symb(src)))
    set_polarity(DAG_arg(src, DAG_arity(src) - 1), pol);
}

/*--------------------------------------------------------------*/

static void
reset_polarity(TDAG src)
/* PF reset the misc record in every node of src */
{
  int i;
  if (!DAG_misc(src))
    return;
  DAG_misc_set(src, 0);
  for (i = 0; i < DAG_arity(src); i++)
    reset_polarity(DAG_arg(src, i));
}

#endif

/*
  --------------------------------------------------------------
  Problematic connector removing
  --------------------------------------------------------------
*/

/* DD+PF this is useful for removing connectors that would make a
   subformula (in a tree representation) having at the same time
   positive and negative polarities.
   As a consequence, a quantifier could be at the same time strong and
   weak, and Skolemization would be impossible. */

static TDAG
problem_connector_aux(TDAG src)
{
  TDAG dest;
  if (!DAG_quant(src))
    return src;
  if (DAG_symb(src) == CONNECTOR_XOR)
    {
      if (DAG_arity(src) != 2)
        my_error("skolem: n-ary XOR connector not implemented\n");
      dest = DAG_dup(DAG_or2(DAG_and2(DAG_not(DAG_arg0(src)), DAG_arg1(src)),
                             DAG_and2(DAG_not(DAG_arg0(src)), DAG_arg1(src))));
      DAG_free(src);
      return dest;
    }
  if (DAG_symb(src) == CONNECTOR_EQUIV)
    {
      if (DAG_arity(src) != 2)
        my_error("skolem: n-ary EQUIV connector not implemented\n");
      dest = DAG_dup(DAG_and2(DAG_implies(DAG_arg0(src), DAG_arg1(src)),
                              DAG_implies(DAG_arg1(src), DAG_arg0(src))));
      DAG_free(src);
      return dest;
    }
  if (DAG_symb(src) == CONNECTOR_ITE && DAG_quant(DAG_arg(src, 0)))
    {
      dest = DAG_dup(DAG_and2(DAG_implies(DAG_arg(src, 0), DAG_arg(src, 1)),
                              DAG_implies(DAG_not(DAG_arg(src, 0)), DAG_arg(src, 2))));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

/**
   \brief ensures that no formula has quantifiers with both polarities
   \param src a formula
   \return formula such that every quantifier appears with one polarity only
   \remark essentially removes xor, equiv, and ite where problematic
   \remark Non Destructive */
static TDAG
problem_connector(TDAG src)
{
  return cond_structural_recursion(src, problem_connector_aux, DAG_quant_f);
}

/*
  --------------------------------------------------------------
  Skolemization
  --------------------------------------------------------------
*/

static Ttable skolem_scope = NULL;

/*--------------------------------------------------------------*/

static TDAG
skolem_term(Tsort sort)
/* PF builds a skolem term of the right sort
   if skolem_scope is non-empty, the term is a skolem function applied
   to arguments in skolem_scope. */
{
  unsigned i, arity;
  Tsort *sub;
  Tsymb symb;
  TDAG *PDAG;
  arity = table_length(skolem_scope);
  if (!arity)
    return DAG_new_args(DAG_symb_skolem(sort), DAG_NULL);
  MY_MALLOC(PDAG, arity * sizeof(TDAG));
  MY_MALLOC(sub, (arity + 1) * sizeof(Tsort));
  for (i = 0; i < arity; i++)
    {
      PDAG[i] = DAG_of_ptr(table_get(skolem_scope, i));
      sub[i] = DAG_sort(PDAG[i]);
    }
  sub[i] = sort;
  symb = DAG_symb_skolem(DAG_sort_new(NULL, arity + 1, sub));
  return DAG_new(symb, arity, PDAG);
}

/*--------------------------------------------------------------*/

#define QUANTIFIED_STRONG(DAG, pol) \
   ((DAG_symb(DAG) == QUANTIFIER_EXISTS && pol == POL_POS) || \
    (DAG_symb(DAG) == QUANTIFIER_FORALL && pol == POL_NEG))
#define QUANTIFIED_WEAK(DAG, pol) \
   ((DAG_symb(DAG) == QUANTIFIER_EXISTS && pol == POL_NEG) || \
    (DAG_symb(DAG) == QUANTIFIER_FORALL && pol == POL_POS))

/*--------------------------------------------------------------*/

static TDAG
skolemize_deep(TDAG src, Tpol pol)
/* PF skolemizing while looking down non-ground subformulas of src
   Linear in the size of the tree */
{
  TDAG *PDAG;
  unsigned i;
  if (DAG_quant(src) && pol == POL_BOTH)
    my_error("skolemize: sub formula has both polarities\n");
  if (DAG_symb(src) == LAMBDA || DAG_symb(src) == APPLY_LAMBDA)
    my_error("skolemize: apply or lambda expression found\n");
  if (DAG_symb(src) == CONNECTOR_ITE)
    {
      MY_MALLOC(PDAG, 3 * sizeof(TDAG));
      PDAG[0] = skolemize_deep(DAG_arg(src, 0), POL_BOTH);
      PDAG[1] = skolemize_deep(DAG_arg(src, 1), pol);
      PDAG[2] = skolemize_deep(DAG_arg(src, 2), pol);
      return DAG_new(CONNECTOR_ITE, 3, PDAG);
    }
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      MY_MALLOC(PDAG, 2 * sizeof(TDAG));
      PDAG[0] = skolemize_deep(DAG_arg0(src), INV_POL(pol));
      PDAG[1] = skolemize_deep(DAG_arg1(src), pol);
      return DAG_new(CONNECTOR_IMPLIES, 2, PDAG);
    }
  if (QUANTIFIED_STRONG(src, pol))
    {
      TDAG tmp;
      for (i = 0; i < DAG_arity(src) - 1u; i++)
        {
          TDAG var = DAG_arg(src, i);
          if (DAG_symb_DAG[DAG_symb(var)])
            my_error ("skolemize: quantifier in scope of another"
                      " quantifier on the same variable\n");
          DAG_symb_DAG[DAG_symb(var)] = DAG_dup(skolem_term(DAG_sort(var)));
        }
      tmp = skolemize_deep(DAG_arg(src, i), pol);
      for (i = 0; i < DAG_arity(src) - 1u; ++i)
        {
          DAG_free(DAG_symb_DAG[DAG_symb(DAG_arg(src, i))]);
          DAG_symb_DAG[DAG_symb(DAG_arg(src, i))] = DAG_NULL;
        }
#ifdef OLDPROOF
      my_error("Deep skolemization is not proof producing.\n");
#endif
      return tmp;
    }
  if (QUANTIFIED_WEAK(src, pol))
    {
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src) - 1u; i++)
        {
          table_push(skolem_scope, DAG_ptr_of(DAG_arg(src, i)));
          PDAG[i] = DAG_arg(src, i);
        }
      PDAG[i] = skolemize_deep(DAG_arg(src, i), pol);
      for (i = 0; i < DAG_arity(src) - 1u; ++i)
        table_pop(skolem_scope);
      if (DAG_symb(PDAG[DAG_arity(src) - 1]) == DAG_symb(src)) /* DD join quantifiers */
        {
          TDAG body = PDAG[i];
          unsigned j, k;
          unsigned arity = DAG_arity(src) - 1u + DAG_arity(body);
          MY_REALLOC(PDAG, arity * sizeof(TDAG));
          for (j = DAG_arity(src) - 1u, k = 0; j < arity; ++j, ++k)
            PDAG[j] = DAG_arg(body, k);
          /* TODO TRIGGERS */
          return DAG_new(DAG_symb(src), arity, PDAG);
        }
      return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
    }
  if (DAG_symb(src) == CONNECTOR_NOT)
    pol = INV_POL (pol);
  else if (DAG_symb(src) == CONNECTOR_EQUIV ||
           DAG_symb(src) == CONNECTOR_XOR ||
           !boolean_connector(DAG_symb(src)))
    pol = POL_BOTH;
  if (!DAG_arity(src) && DAG_symb_DAG[DAG_symb(src)])
    return DAG_symb_DAG[DAG_symb(src)];
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = skolemize_deep(DAG_arg(src, i), pol);
  return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
}

/*--------------------------------------------------------------*/

static TDAG
skolemize_shallow_2(TDAG src)
{
  TDAG *PDAG;
  unsigned i;
  if (!DAG_arity(src) && DAG_symb_DAG[DAG_symb(src)])
    return DAG_symb_DAG[DAG_symb(src)];
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = skolemize_shallow_2(DAG_arg(src, i));
  return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
}

/*--------------------------------------------------------------*/

extern bool enable_nnf_simp;

static TDAG
skolemize_shallow (TDAG src, Tpol pol OPTC_OLDPROOF(Tstack_proof table))
{
  TDAG *PDAG;
  unsigned i;
  if (DAG_quant(src) && pol == POL_BOTH)
    my_error("skolemize: sub formula has both polarities\n");
  if (DAG_symb(src) == LAMBDA || DAG_symb(src) == APPLY_LAMBDA)
    my_error("skolemize: apply or lambda expression found\n");
  if (DAG_symb(src) == CONNECTOR_ITE)
    {
      MY_MALLOC(PDAG, 3 * sizeof(TDAG));
      PDAG[0] = skolemize_shallow(DAG_arg(src, 0), POL_BOTH OPTC_OLDPROOF(table));
      PDAG[1] = skolemize_shallow(DAG_arg(src, 1), pol OPTC_OLDPROOF(table));
      PDAG[2] = skolemize_shallow(DAG_arg(src, 2), pol OPTC_OLDPROOF(table));
      return DAG_new(CONNECTOR_ITE, 3, PDAG);
    }
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      MY_MALLOC(PDAG, 2 * sizeof(TDAG));
      PDAG[0] = skolemize_shallow(DAG_arg0(src), INV_POL(pol) OPTC_OLDPROOF(table));
      PDAG[1] = skolemize_shallow(DAG_arg1(src), pol OPTC_OLDPROOF(table));
      return DAG_new(CONNECTOR_IMPLIES, 2, PDAG);
    }
  if (QUANTIFIED_STRONG(src, pol))
    {
      TDAG tmp;
      for (i = 0; i < DAG_arity(src) - 1u; i++)
        {
          TDAG var = DAG_arg(src, i);
          TDAG skolem = DAG_dup(skolem_term(DAG_sort(var)));
          if (DAG_symb_DAG[DAG_symb(var)])
            my_error ("skolemize: quantifier in scope of another"
                      " quantifier on the same variable\n");
          DAG_symb_DAG[DAG_symb(var)] = skolem;
        }
      tmp = skolemize_shallow(DAG_arg(src, i), pol OPTC_OLDPROOF(table));
      for (i = 0; i < DAG_arity(src) - 1u; ++i)
        {
          DAG_free(DAG_symb_DAG[DAG_symb(DAG_arg(src, i))]);
          DAG_symb_DAG[DAG_symb(DAG_arg(src, i))] = DAG_NULL;
        }
#ifdef OLDPROOF
      if (pol == POL_POS)
        stack_push(table, proof_add_skolem_ex_lemma(src, tmp));
      else
        stack_push(table, proof_add_skolem_all_lemma(src, tmp));
#endif
      return tmp;
    }
  if (QUANTIFIED_WEAK(src, pol))
    {
      TDAG dest;
      /* [TODO] HB Remove this when my simp works */
      if (!enable_nnf_simp && DAG_symb(src) == QUANTIFIER_EXISTS)
        {
          Tstack_DAG DAGs;
          stack_INIT(DAGs);
          for (i = 0; i < DAG_arity(src) - 1; ++i)
            stack_push(DAGs, skolemize_shallow_2(DAG_arg(src, i)));
          stack_push(DAGs, DAG_not(skolemize_shallow_2(DAG_arg_last(src))));
          dest = DAG_not(DAG_new_stack(QUANTIFIER_FORALL, DAGs));
          stack_free(DAGs);
        }
      else
        dest = skolemize_shallow_2(src);
      Tstack_DAGstack *Pannot = DAG_prop_get(src, DAG_PROP_TRIGGER);
      if (Pannot)
        {
          Tstack_DAGstack annot2;
          unsigned i;
          stack_INIT_s(annot2, stack_size(*Pannot));
          for (i = 0; i < stack_size(*Pannot); ++i)
            {
              Tstack_DAG trigger = stack_get(*Pannot, i);
              Tstack_DAG trigger2;
              unsigned j;
              stack_INIT_s(trigger2, stack_size(trigger));
              for (j = 0; j < stack_size(trigger); ++j)
                {
                  TDAG pat = stack_get(trigger, j);
                  stack_push(trigger2, DAG_dup(skolemize_shallow_2(pat)));
                }
              stack_push(annot2, trigger2);
            }
          if (!enable_nnf_simp && DAG_symb(src) == QUANTIFIER_EXISTS)
            DAG_prop_set(DAG_arg0(dest), DAG_PROP_TRIGGER, &annot2);
          else
            DAG_prop_set(dest, DAG_PROP_TRIGGER, &annot2);
        }
      return dest;
    }
  if (DAG_symb(src) == CONNECTOR_NOT)
    pol = INV_POL (pol);
  else if (DAG_symb(src) == CONNECTOR_EQUIV ||
           DAG_symb(src) == CONNECTOR_XOR ||
           !boolean_connector(DAG_symb(src)))
    pol = POL_BOTH;

  if (!DAG_arity(src) && DAG_symb_DAG[DAG_symb(src)])
    return DAG_symb_DAG[DAG_symb(src)];
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = skolemize_shallow(DAG_arg(src, i), pol OPTC_OLDPROOF(table));
  return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
}

/*--------------------------------------------------------------*/

/* PF should never be used with POL_BOTH or POL_NONE */
#define SKOLEM_RES(a, i)			\
  (((TDAG *) DAG_Pflag(a))[(i == POL_POS)?0:1])
#define SKOLEM_ALLOC_RES(a)				\
  if (!DAG_Pflag(a))					\
    {							\
      DAG_Pflag_set(a, malloc(2 * sizeof(TDAG)));	\
      SKOLEM_RES(a, 0) = DAG_NULL;			\
      SKOLEM_RES(a, 1) = DAG_NULL;			\
    }

/*--------------------------------------------------------------*/

static TDAG
skolemize_aux (TDAG src, Tpol pol OPTC_OLDPROOF(Tstack_proof table))
/* PF skolemizing while looking down the ground subformulas of src
   Linear in the size of the ground DAG */
{
  unsigned i;
  if (!DAG_quant(src))
    return src;
  /* Ensured by elimination of problematic connectors */
  assert(pol != POL_NONE && pol != POL_BOTH);
  if (DAG_symb(src) == LAMBDA || DAG_symb(src) == APPLY_LAMBDA)
    my_error("skolemize: apply or lambda expression found\n");
  if (DAG_Pflag(src) && SKOLEM_RES(src, pol))
    return SKOLEM_RES(src, pol);
  if (DAG_symb(src) == CONNECTOR_ITE)
    {
      TDAG *PDAG, tmp;
      MY_MALLOC(PDAG, 3 * sizeof(TDAG));
      PDAG[0] = skolemize_aux(DAG_arg(src, 0), POL_BOTH OPTC_OLDPROOF(table));
      PDAG[1] = skolemize_aux(DAG_arg(src, 1), pol OPTC_OLDPROOF(table));
      PDAG[2] = skolemize_aux(DAG_arg(src, 2), pol OPTC_OLDPROOF(table));
      tmp = DAG_new(CONNECTOR_ITE, 3, PDAG);
      SKOLEM_ALLOC_RES(src);
      SKOLEM_RES(src, pol) = DAG_dup(tmp);
      return tmp;
    }
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      TDAG *PDAG, tmp;
      MY_MALLOC(PDAG, 2 * sizeof(TDAG));
      PDAG[0] = skolemize_aux(DAG_arg0(src), INV_POL(pol) OPTC_OLDPROOF(table));
      PDAG[1] = skolemize_aux(DAG_arg1(src), pol OPTC_OLDPROOF(table));
      tmp = DAG_new(CONNECTOR_IMPLIES, 2, PDAG);
      SKOLEM_ALLOC_RES(src);
      SKOLEM_RES(src, pol) = DAG_dup(tmp);
      return tmp;
    }
  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      TDAG tmp;
      tmp = DAG_not(skolemize_aux(DAG_arg0(src), INV_POL(pol) OPTC_OLDPROOF(table)));
      SKOLEM_ALLOC_RES(src);
      SKOLEM_RES(src, pol) = DAG_dup(tmp);
      return tmp;
    }
  assert(DAG_symb(src) != CONNECTOR_EQUIV || DAG_symb(src) != CONNECTOR_XOR);
  if (boolean_connector(DAG_symb(src)))
    {
      TDAG *PDAG, tmp;
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); i++)
        PDAG[i] = DAG_dup(skolemize_aux(DAG_arg(src, i), pol OPTC_OLDPROOF(table)));
      tmp = DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
      for (i = 0; i < DAG_arity(tmp); i++)
        DAG_free(DAG_arg(tmp, i));
      SKOLEM_ALLOC_RES(src);
      SKOLEM_RES(src, pol) = DAG_dup(tmp);
      return tmp;
    }
  if (quantifier(DAG_symb(src)))
    {
      TDAG tmp;
      if (enable_deep_skolem)
        tmp = skolemize_deep(src, pol);
      else
        tmp = skolemize_shallow(src, pol OPTC_OLDPROOF(table));
      SKOLEM_ALLOC_RES(src);
      SKOLEM_RES(src, pol) = DAG_dup(tmp);
      return tmp;
    }
  my_error ("skolemize: unable to Skolemize quantifier\n");
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

static void
skolemize_free_Pflag (TDAG src)
/* PF apply FDAG_free to every Pflag in src, and set to NULL */
{
  unsigned i;
  if (!DAG_Pflag(src))
    return;
  for (i = 0; i < DAG_arity(src); i++)
    skolemize_free_Pflag(DAG_arg(src, i));
  if (SKOLEM_RES(src, 0))
    DAG_free(SKOLEM_RES(src, 0));
  if (SKOLEM_RES(src, 1))
    DAG_free(SKOLEM_RES(src, 1));
  free ((TDAG *) DAG_Pflag(src));
  DAG_Pflag_set(src, NULL);
}

/*--------------------------------------------------------------*/

static TDAG
skolemize_private (TDAG src OPTC_OLDPROOF(Tstack_proof table))
/* PF skolemizing...
   Non destructive */
{
  TDAG dest;
  if (!is_FOL(src))
    my_error("skolemize: only applicable to FOL formulas\n");
  skolem_scope = table_new(10, 5);
  dest = DAG_dup(skolemize_aux(src, POL_POS OPTC_OLDPROOF(table)));
  skolemize_free_Pflag(src);
  if (table_length(skolem_scope) != 0)
    my_error("skolemize: internal inconsistency\n");
  table_free(&skolem_scope);
  return dest;
}

/*
  --------------------------------------------------------------
  Interface functions
  --------------------------------------------------------------
*/

void
skolemize_init(void)
{
  options_new (0, "enable-deep-skolem", "Enable deep Skolemization",
               &enable_deep_skolem);
}

/*--------------------------------------------------------------*/

void
skolemize_done(void)
{
}

/*--------------------------------------------------------------*/

TDAG
skolemize(TDAG src OPTC_OLDPROOF(Tproof * Pproof))
{
  TDAG dest, tmp;
#ifdef OLDPROOF
  Tstack_proof table;
  stack_INIT(table);
  if (enable_deep_skolem)
    my_error("Deep skolemization not supported in proof producing mode\n");
#endif
  dest = problem_connector(src);
#ifdef OLDPROOF
  if (src != dest)
    *Pproof = proof_tmp_sk_connector(*Pproof, dest);
#endif
  tmp = dest;
  dest = skolemize_private(tmp OPTC_OLDPROOF(table));
  DAG_free(tmp);
#ifdef OLDPROOF
  if (stack_size(table))
    *Pproof = proof_deep_res(tmp, *Pproof, table);
  stack_free(table);
#endif
#ifdef DEBUG_SKOLEM
  if (src != dest)
    {
      my_message("Before elimination of problematic connectors\n");
      DAG_fprint_smt2_bench(stderr, src, "unknown");
      my_message("After skolemization\n");
      DAG_fprint_smt2_bench(stderr, dest, "unknown");
    }
#endif
  return dest;
}

/*--------------------------------------------------------------*/
