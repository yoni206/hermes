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
  Module for polishing quantified formulas
  --------------------------------------------------------------
*/

/*#define DEBUG_QNT_TIDY*/

#include <limits.h>

#include "types.h"

#include "config.h"
#include "DAG.h"
#include "DAG-symb-DAG.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "DAG-prop.h"
#include "DAG-print.h"
#include "general.h"
#include "qnt-tidy.h"
#include "polarities.h"
#include "recursion.h"

#ifdef OLDPROOF
#include "proof.h"

Tstack_proof table = NULL;
#endif

/*
  --------------------------------------------------------------
  Renaming variables
  --------------------------------------------------------------
*/

TSstack(_stack_DAG, Tstack_DAG);

Tstack_stack_DAG sort_var = NULL;
Tstack_unsigned sort_var_c = NULL;

#define sort_var_get(sort, i) stack_get(stack_get(sort_var, sort), i)
#define sort_var_n(sort) stack_size(stack_get(sort_var,sort))
#define sort_var_push(sort, DAG) stack_push(stack_get(sort_var, sort), DAG);

/*--------------------------------------------------------------*/

static TDAG
DAG_symb_var_new(Tsort sort)
/* DD+PF get a fresh variable for sort */
{
  assert(sort < stack_size(sort_var_c));
  stack_set(sort_var_c, sort, stack_get(sort_var_c, sort) + 1);
  if (stack_get(sort_var_c, sort) > sort_var_n(sort))
    {
      Tsymb symb = DAG_symb_variable(sort);
      TDAG DAG = DAG_dup(DAG_new(symb, 0, NULL));
      sort_var_push(sort, DAG);
    }
  assert(stack_get(sort_var_c, sort) <= sort_var_n(sort));
  return sort_var_get(sort, stack_get(sort_var_c, sort) - 1);
}

/*--------------------------------------------------------------*/

static void
DAG_symb_var_delete(Tsort sort)
/* DD+PF allow to reuse a variable later */
{
  assert(sort < stack_size(sort_var_c));
  assert(stack_get(sort_var_c, sort) > 0);
  stack_set(sort_var_c, sort, stack_get(sort_var_c, sort) - 1);
}

/*--------------------------------------------------------------*/

static void
DAG_symb_var_resize(unsigned n)
{
  unsigned i;
  unsigned old = stack_size(sort_var);
  for (i = n; i < old; i++)
    {
      Tstack_DAG vars = stack_get(sort_var, i);
      unsigned j;
      for (j = 0; j < stack_size(vars); j++)
        DAG_free(stack_get(vars, j));
      stack_free(vars);
    }
  stack_resize(sort_var, n);
  stack_resize(sort_var_c, n);
  for (i = old; i < n; i++)
    {
      stack_set(sort_var_c, i, 0);
      stack_INIT(stack_get(sort_var, i));
    }
}

/*
  --------------------------------------------------------------
  Canonize
  --------------------------------------------------------------
*/

static void
DAG_reset_Pflag_prop(TDAG DAG)
{
  unsigned i;
  if (!DAG_Pflag(DAG))
    return;
  DAG_Pflag_set(DAG, DAG_ptr_of(DAG_NULL));
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_reset_Pflag_prop(DAG_arg(DAG, i));
  if (quantifier(DAG_symb(DAG)) &&
      DAG_prop_get(DAG, DAG_PROP_TRIGGER))
    {
      Tstack_DAGstack *Pannot = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
      unsigned i;
      for (i = 0; i < stack_size(*Pannot); ++i)
        {
          Tstack_DAG trigger = stack_get(*Pannot, i);
          unsigned j;
          for (j = 0; j < stack_size(trigger); ++j)
            DAG_reset_Pflag(stack_get(trigger, j));
        }
    }
}

/*--------------------------------------------------------------*/

static int
qnt_canonize_aux (TDAG DAG)
/* PF+DD see qnt_canonize.  Put rewritten DAG in DAG_Pflag(DAG)
   returns 1 iff DAG_Pflag(DAG) != DAG (0 otherwise).
   flag is used to mark variables that are actually used in their scope.
*/
{
  unsigned i;
  if (DAG_symb_type(DAG_symb(DAG)) & SYMB_VARIABLE)
    {
      if (!DAG_Pflag(DAG))
        my_error("qnt_canonize: free variable found\n");
      DAG_flag_set(DAG, 1);
      return DAG != DAG_of_ptr(DAG_Pflag(DAG));
    }
  if (DAG_symb(DAG) == LAMBDA || DAG_symb(DAG) == APPLY_LAMBDA)
    my_error("qnt_canonize: apply or lambda expression found\n");
  if (quantifier(DAG_symb(DAG)))
    {
      int *Pint;
      TDAG *PDAG;
      unsigned arity;
      /* PF remember the replacement of variables outside the
         scope of the present quantifier, and allow (by setting Pflag
         to NULL) a new symbol to be associated to them */
      MY_MALLOC(Pint, (DAG_arity(DAG) - 1u) * sizeof(int));
      MY_MALLOC(PDAG, (DAG_arity(DAG) - 1u) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(DAG) - 1u; ++i)
        {
          TDAG tmp2;
          PDAG[i] = DAG_of_ptr(DAG_Pflag(DAG_arg(DAG, i)));
          Pint[i] = DAG_flag(DAG_arg(DAG, i));
          tmp2 = DAG_symb_var_new(DAG_sort(DAG_arg(DAG, i)));
          DAG_Pflag_set(DAG_arg(DAG, i), DAG_ptr_of(tmp2));
          DAG_flag_set(DAG_arg(DAG, i), 0);
        }
      /* IMPROVE it would be clearer, and more efficient to first
         eliminate unused vars.
         For instance in the present case
         forall x y p(x,y)
         forall x z y p(x,y)
         are not renamed the same way since y will not have the same id */
      qnt_canonize_aux(DAG_arg_last(DAG));
      {
        Tstack_DAGstack *Pannot = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
        if (Pannot)
          {
            unsigned i;
            for (i = 0; i < stack_size(*Pannot); ++i)
              {
                Tstack_DAG trigger = stack_get(*Pannot, i);
                unsigned j;
                for (j = 0; j < stack_size(trigger); ++j)
                  qnt_canonize_aux(stack_get(trigger, j));
              }
          }
      }
      arity = 1;
      /* PF count the number of variables that are indeed used */
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        if (DAG_flag(DAG_arg(DAG, i)))
          ++arity;
      /* PF if no variable is used, the quantifier is useless */
      if (arity == 1)
        {
          DAG_Pflag_set(DAG, DAG_Pflag(DAG_arg_last(DAG)));
        }
      else
        {
          unsigned j;
          TDAG tmp2;
          TDAG * PDAG2;
          /* PF collect used variables, sort them, and build the DAG */
          MY_MALLOC(PDAG2, arity * sizeof(TDAG));
          for (i = 0, j = 0; i < DAG_arity(DAG)-1; i++)
            if (DAG_flag(DAG_arg(DAG, i)))
              PDAG2[j++] = DAG_of_ptr(DAG_Pflag(DAG_arg(DAG, i)));
          assert(arity != 0);
          assert(j == arity-1);
          PDAG2[j] = DAG_of_ptr(DAG_Pflag(DAG_arg_last(DAG)));
          tmp2 = DAG_new(DAG_symb(DAG), arity, PDAG2);
          DAG_Pflag_set(DAG, DAG_ptr_of(tmp2));
          {
            Tstack_DAGstack *Pannot = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
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
                        stack_push(trigger2,
                                   DAG_dup(DAG_of_ptr(DAG_Pflag(pat))));
                      }
                    stack_push(annot2, trigger2);
                  }
                DAG_prop_set(DAG_of_ptr(DAG_Pflag(DAG)), DAG_PROP_TRIGGER, &annot2);
              }
          }
        }
      for (i = 0; i < DAG_arity(DAG) - 1u; ++i)
        {
          /* PF reset the replacement of variables to their value
             outside the scope */
          DAG_flag_set(DAG_arg(DAG, i), Pint[i]);
          DAG_Pflag_set(DAG_arg(DAG, i), DAG_ptr_of(PDAG[i]));
          DAG_symb_var_delete(DAG_sort(DAG_arg(DAG, i)));
        }
      free(PDAG);
      free(Pint);
#ifdef OLDPROOF
      stack_push(table, proof_add_qnt_simp_lemma(DAG,
                                                 DAG_of_ptr(DAG_Pflag(DAG))));
#endif
      return 1;
    }
  else
    {
      /* PF+DD classical recursion: apply on all subterms
         and rebuild term if something changed */
      int changed = 0;
      for (i = 0; i < DAG_arity(DAG); i++)
        changed |= qnt_canonize_aux(DAG_arg(DAG, i));
      if (changed)
        {
          TDAG * PDAG, tmp;
          MY_MALLOC(PDAG, DAG_arity(DAG) * sizeof(TDAG));
          for (i = 0; i < DAG_arity(DAG); i++)
            PDAG[i] = DAG_of_ptr(DAG_Pflag((TDAG) DAG_arg(DAG, i)));
          tmp = DAG_new(DAG_symb(DAG), DAG_arity(DAG), PDAG);
          DAG_Pflag_set(DAG, DAG_ptr_of(tmp));
        }
      else
        DAG_Pflag_set(DAG, DAG_ptr_of(DAG));
      return changed;
    }
  my_error ("qnt_canonize: internal error\n");
  return 0;
}

/*--------------------------------------------------------------*/

static TDAG
qnt_canonize(TDAG src)
/* DD+PF rename quantified variables so that two identical quantified
   formulas (modulo renaming) are represented by the same DAG.
   Moreover, the canonization is such that quantified variables are
   ordered according to a topological sort in the DAG. Quantified
   variables that do not occur in the matrix are removed. Thus
   applying qnt_canonize on the following formulas returns the same
   TDAG:

   \forall x1, y1 @ p(x1, y1)
   \forall y2, x2 @ p(x2, y2)
   \forall x, y, z @ p(x, y)

   *However*: Formula \forall x @ \forall y @ p(x, y) would be
   represented by a different DAG.  This is taken cared of by
   qnt_join_quantifiers (better called before)
   src should be lambda-free
   Tolerant with respect to apply, macros, ite terms
*/
{
  TDAG dest;
  qnt_canonize_aux(src);
  dest = DAG_dup(DAG_of_ptr(DAG_Pflag(src)));
  DAG_reset_Pflag_prop(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Setting the ->ground bit
  --------------------------------------------------------------
*/

static unsigned
qnt_ground_aux_quant (TDAG DAG)
/* DD+PF sets the ground bit on DAGs
   An integer is associated to every variable
   this number increases for more intern variables
   return the smallest variable used in a term (INT_MAX if ground)
   This is linear with respect to the TREE size
   This is the reason why this is only used inside quantified formulas
   DAG should be lambda-free,
   DAG should not contain imbricated quantifiers on the same variable
   Tolerant to apply, macros, ite terms
*/
{
  static unsigned var_nb = 0;
  unsigned i;
  unsigned tmp;

  if (DAG_symb_type(DAG_symb(DAG)) & SYMB_VARIABLE)
    {
      if (!DAG_flag(DAG))
        my_DAG_error("qnt_ground: free variable found in %D\n", DAG);
      return (unsigned)DAG_flag(DAG);
    }
  if (DAG_symb(DAG) == LAMBDA || DAG_symb(DAG) == APPLY_LAMBDA)
    my_error("qnt_ground: apply or lambda expression found\n");
  if (!DAG_arity(DAG))
    {
      DAG_ground(DAG) = 1;
      return UINT_MAX;
    }
  if (quantifier(DAG_symb(DAG)))
    {
      assert(DAG_arity(DAG) > 0);
      for (i = 0; i < DAG_arity(DAG) - 1u; ++i)
        if (DAG_flag(DAG_arg(DAG, i)))
          my_error("qnt_ground: quantified variable is reused\n");
        else
          DAG_flag_set(DAG_arg(DAG, i), (int)++var_nb);
      tmp = qnt_ground_aux_quant(DAG_arg_last(DAG));
      for (i = 0; i < DAG_arity(DAG) - 1u; ++i)
        DAG_flag_set(DAG_arg(DAG, i), 0);
      var_nb -= DAG_arity(DAG) - 1u;
      DAG_ground(DAG) = (tmp > var_nb);
      if (DAG_ground(DAG))
        return UINT_MAX;
      return tmp;
    }
  tmp = UINT_MAX;
  for (i = 0; i < DAG_arity(DAG); i++)
    {
      unsigned tmp2 = qnt_ground_aux_quant(DAG_arg(DAG, i));
      if (tmp > tmp2)
        tmp = tmp2;
    }
  DAG_ground(DAG) = (tmp == UINT_MAX);
  return tmp;
}

/*--------------------------------------------------------------*/

void
qnt_ground(TDAG DAG)
{
  if (DAG_ground(DAG))
    return;
  if (DAG_symb_type(DAG_symb(DAG)) & SYMB_VARIABLE)
    my_error("qnt_ground: free variable found\n");
  if (quantifier(DAG_symb(DAG)))
    qnt_ground_aux_quant(DAG);
  else
    {
      unsigned i;
      for (i = 0; i < DAG_arity(DAG); i++)
        qnt_ground(DAG_arg(DAG, i));
      DAG_ground(DAG) = 1;
    }
}

/*--------------------------------------------------------------*/

/* [TODO] HB there is a function to do the same in inst-pre */
static void
DAG_copy_triggers(TDAG orig, TDAG dest)
{
  Tstack_DAGstack *Pannot1 = DAG_prop_get(orig, DAG_PROP_TRIGGER);
  Tstack_DAGstack *Pannot2;
  Tstack_DAGstack annot;
  unsigned i, j;
  int flag;
  if (!Pannot1)
    return;
  Pannot2 = DAG_prop_get(dest, DAG_PROP_TRIGGER);
  flag = (Pannot2 == NULL);
  if (flag)
    {
      stack_INIT_s(annot, stack_size(*Pannot1));
    }
  else
    annot = *Pannot2;
  for (i = 0; i < stack_size(*Pannot1); ++i)
    {
      Tstack_DAG trigger1 = stack_get(*Pannot1, i);
      Tstack_DAG trigger2;
      stack_INIT_s(trigger2, stack_size(trigger1));
      for (j = 0; j < stack_size(trigger1); ++j)
        stack_push(trigger2, DAG_dup(stack_get(trigger1, j)));
      stack_push(annot, trigger2);
    }
  if (flag)
    DAG_prop_set(dest, DAG_PROP_TRIGGER, &annot);
}

/*
  --------------------------------------------------------------
  Join same quantifiers
  --------------------------------------------------------------
*/
/* PF+DD (functions by DD) replace
   forall x forall y by forall x y
   exists x exists y by exists x y
   forall x y forall y z by forall x y z
   tolerant for ite terms, lambda, ... */

static TDAG
qnt_join_quantifiers_rec(TDAG src)
{
  TDAG     dest = DAG_NULL;
  TDAG     DAG2;
  TDAG *   PDAG;
  unsigned nvars;
  unsigned i, j;
  if (!quantifier(DAG_symb(src)) ||
      DAG_symb(src) != DAG_symb(DAG_arg_last(src)))
    return src;
  DAG2 = DAG_arg_last(src);
  assert(DAG_arity(src) > 0 && DAG_arity(DAG2) > 0);
  for (i = 0; i < DAG_arity(src) - 1u; ++i)
    DAG_flag_set(DAG_arg(src, i), 1);
  nvars = DAG_arity(src) - 1u;
  for (i = 0; i < DAG_arity(DAG2) - 1u; ++i)
    if (DAG_flag(DAG_arg(DAG2, i)) == 0) ++nvars;
  MY_MALLOC(PDAG, (nvars + 1) * sizeof(TDAG));
  for (j = 0; j < DAG_arity(src) - 1u; ++j)
    PDAG[j] = DAG_arg(src, j);
  for (i = 0; i < DAG_arity(DAG2) - 1u; ++i)
    if (DAG_flag(DAG_arg(DAG2, i)) == 0)
      PDAG[j++] = DAG_arg(DAG2, i);
  PDAG[j] = DAG_arg_last(DAG2);
  for (i = 0; i < DAG_arity(src) - 1u; ++i)
    DAG_flag(DAG_arg(src, i)) = 0;
  dest = DAG_dup(DAG_new(DAG_symb(src), nvars + 1, PDAG));
  DAG_copy_triggers(src, dest);
  DAG_copy_triggers(DAG2, dest);
#ifdef OLDPROOF
  stack_push(table, proof_add_qnt_merge_lemma(src, dest));
#endif
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

static TDAG
qnt_join_quantifiers(TDAG DAG)
{
  return cond_structural_recursion(DAG, qnt_join_quantifiers_rec, DAG_quant_f);
}

/*
  --------------------------------------------------------------
  quantifier simplifications
  --------------------------------------------------------------
*/

/* FORALL x . x != T OR P(x) --> P(T)
   EXISTS x . x = T AND P(x) --> P(T)
   if T only contains variables that have a larger scope that x */

static unsigned qnt_counter = 0;

/*--------------------------------------------------------------*/

static TDAG
qnt_subst(TDAG src)
/* PF substitutes every variable such that DAG_symb_DAG
   is set with the binded DAG
   Non-destructive, requires DAG_dup */
{
  unsigned i;
  TDAG * PDAG;
  if (DAG_symb(src) == LAMBDA || DAG_symb(src) == APPLY_LAMBDA)
    my_error("qnt_subst: apply or lambda expression found\n");
  if (quantifier(DAG_symb(src)))
    {
      TDAG tmp = qnt_subst(DAG_arg_last(src));
      if (tmp == DAG_arg_last(src))
        return src;
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src) - 1; ++i)
        PDAG[i] = DAG_arg(src, i);
      PDAG[i] = tmp;
      return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
    }
  if (DAG_arity(src))
    {
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); ++i)
        PDAG[i] = qnt_subst(DAG_arg(src, i));
      return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
    }
  if (DAG_symb_type(DAG_symb(src)) & SYMB_VARIABLE &&
      DAG_symb_DAG[DAG_symb(src)])
    return DAG_symb_DAG[DAG_symb(src)];
  return src;
}

/*--------------------------------------------------------------*/

static int
qnt_almost_var_free(TDAG src, int i)
/* PF returns 1 iff all variables in src have id s.t. 0 < id < i
   No quantifier should occur in src (through ite term) */
{
  unsigned j;
  if (quantifier(DAG_symb(src)))
    return 0;
  if (DAG_symb_type(DAG_symb(src)) & SYMB_VARIABLE)
    return (0 < DAG_flag(src) && DAG_flag(src) < i);
  for (j = 0; j < DAG_arity(src); j++)
    if (!qnt_almost_var_free(DAG_arg(src, j), i))
      return 0;
  return 1;
}

/*--------------------------------------------------------------*/

static void
qnt_lookup_eq(TDAG DAG, unsigned i, Tpol pol)
/* PF look in DAG for an equality v = T where v is a variable of id j > i
   and T is a term containing no variable with id >= j
   Set found terms using DAG_symb_DAG on variables symbols */
{
  while (quantifier(DAG_symb(DAG)))
    DAG = DAG_arg_last(DAG);
  if (DAG_symb(DAG) == PREDICATE_EQ && pol == POL_POS)
    {
      if (((unsigned) DAG_flag(DAG_arg0(DAG))) > i &&
          qnt_almost_var_free(DAG_arg1(DAG), DAG_flag(DAG_arg0(DAG))) &&
          !DAG_symb_DAG[DAG_symb(DAG_arg0(DAG))])
        DAG_symb_DAG[DAG_symb(DAG_arg0(DAG))] = DAG_dup(DAG_arg1(DAG));
      else if (((unsigned) DAG_flag(DAG_arg1(DAG))) > i &&
               qnt_almost_var_free(DAG_arg0(DAG), DAG_flag(DAG_arg1(DAG))) &&
               !DAG_symb_DAG[DAG_symb(DAG_arg1(DAG))])
        DAG_symb_DAG[DAG_symb(DAG_arg1(DAG))] = DAG_dup(DAG_arg0(DAG));
    }
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    qnt_lookup_eq(DAG_arg0(DAG), i, INV_POL(pol));
  if ((DAG_symb(DAG) == CONNECTOR_OR && pol == POL_NEG) ||
      (DAG_symb(DAG) == CONNECTOR_AND && pol == POL_POS))
    {
      unsigned j;
      for (j = 0; j < DAG_arity(DAG); j++)
        qnt_lookup_eq(DAG_arg(DAG, j), i, pol);
    }
  if (DAG_symb(DAG) == CONNECTOR_IMPLIES && pol == POL_NEG)
    {
      qnt_lookup_eq(DAG_arg0(DAG), i, POL_POS);
      qnt_lookup_eq(DAG_arg1(DAG), i, POL_NEG);
    }
}

/*--------------------------------------------------------------*/

static TDAG
qnt_simplify_aux2(TDAG src)
/* PF returns a DAG where quantifiers in src have been suppressed
   when an equality perfectly defines the quantified variable
   Tree-polynomial (tree-linear in practice?)
   No variable should be used in imbricated quantifiers (use qnt_canonize)
   Non-destructive, no DAG_dup required */
{
  unsigned i;
  TDAG * PDAG;
  TDAG dest;
  if (!DAG_quant(src))
    return src;
  if (DAG_symb(src) == LAMBDA || DAG_symb(src) == APPLY_LAMBDA)
    my_error("qnt_simplify: lambda or apply expression found\n");
  if (quantifier(DAG_symb(src)))
    {
      unsigned j;
      unsigned arity;
      j = qnt_counter;
      assert(DAG_arity(src) > 0);
      for (i = 0; i < DAG_arity(src) - 1u; ++i)
        DAG_flag(DAG_arg(src, i)) = (int)++qnt_counter;
      dest = qnt_simplify_aux2(DAG_arg_last(src));
      qnt_lookup_eq(dest, j,
                    (DAG_symb(src) == QUANTIFIER_EXISTS)?POL_POS:POL_NEG);
      arity = DAG_arity(src);
      for (i = 0; i < DAG_arity(src) - 1u; ++i)
        if (DAG_symb_DAG[DAG_symb(DAG_arg(src, i))])
          --arity;
      if (arity == DAG_arity(src) && dest == DAG_arg(src, arity - 1))
        {
          /* PF nothing changed */
          DAG_free(DAG_dup(dest));
          dest = src;
        }
      else
        {
          if (arity == DAG_arity(src))
            {
              /* PF only the matrix changed, no quantifier eliminated */
              TDAG * PDAG;
              MY_MALLOC(PDAG, arity * sizeof(TDAG));
              for (i = 0; i < DAG_arity(src) - 1u; ++i)
                PDAG[i] = DAG_arg(src, i);
              PDAG[i] = dest;
              dest = DAG_new(DAG_symb(src), arity, PDAG);
              DAG_copy_triggers(src, dest);
            }
          else if (arity == 1)
            {
              /* PF all quantifiers eliminated */
              TDAG tmp;
              for (i = 0; i < DAG_arity(src) - 1u; ++i)
                {
                  tmp = DAG_symb_DAG[DAG_symb(DAG_arg(src, i))];
                  DAG_symb_DAG[DAG_symb(DAG_arg(src, i))] =
                    DAG_dup(qnt_subst(tmp));
                  DAG_free(tmp);
                }
              tmp = qnt_subst(dest);
              DAG_free(DAG_dup(dest));
              dest = tmp;
            }
          else
            {
              /* PF some (not all) quantifiers eliminated */
              TDAG *  PDAG;
              Tstack_DAGstack *Pannot; /* the triggers */

              MY_MALLOC(PDAG, arity * sizeof(TDAG));
              j = 0;
              for (i = 0; i < DAG_arity(src) - 1u; ++i)
                if (!DAG_symb_DAG[DAG_symb(DAG_arg(src, i))])
                  PDAG[j++] = DAG_arg(src, i);
                else
                  {
                    TDAG tmp;
                    tmp = DAG_symb_DAG[DAG_symb(DAG_arg(src, i))];
                    DAG_symb_DAG[DAG_symb(DAG_arg(src, i))] =
                      DAG_dup(qnt_subst(tmp));
                    DAG_free(tmp);
                  }
              assert(j == arity - 1);
              PDAG[j] = qnt_subst(dest);
              DAG_free(DAG_dup(dest));
              dest = DAG_new(DAG_symb(src), arity, PDAG);

              Pannot = DAG_prop_get(src, DAG_PROP_TRIGGER);
              if (Pannot)
                {
                  Tstack_DAGstack annot2;
                  unsigned i, j;
                  stack_INIT_s(annot2, stack_size(*Pannot));
                  for (i = 0; i < stack_size(*Pannot); ++i)
                    {
                      Tstack_DAG trigger = stack_get(*Pannot, i);
                      Tstack_DAG trigger2;
                      stack_INIT_s(trigger2, stack_size(trigger));
                      for (j = 0; j < stack_size(trigger); ++j)
                        stack_push(trigger2, DAG_dup(qnt_subst(stack_get(trigger, j))));
                      stack_push(annot2, trigger2);
                    }
                  DAG_prop_set(dest, DAG_PROP_TRIGGER, &annot2);
                }
            }
        }
      for (i = 0; i < DAG_arity(src) - 1u; ++i)
        {
          if (DAG_symb_DAG[DAG_symb(DAG_arg(src, i))])
            {
              DAG_free(DAG_symb_DAG[DAG_symb(DAG_arg(src, i))]);
              DAG_symb_DAG[DAG_symb(DAG_arg(src, i))] = DAG_NULL;
            }
          DAG_flag_set(DAG_arg(src, i), 0);
        }
      return dest;
    }
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); i++)
    PDAG[i] = qnt_simplify_aux2(DAG_arg(src, i));
  return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
}

/*--------------------------------------------------------------*/

static bool
qnt_simplify_aux1(TDAG src)
/* PF helper function for qnt_simplify: puts intermediate results in
   Pflag */
{
  unsigned i;
  bool changed;
  if (DAG_Pflag(src))
    return src == DAG_of_ptr(DAG_Pflag(src));
  if (!DAG_quant(src))
    {
      DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(src)));
      return 0;
    }
  if (DAG_symb(src) == LAMBDA || DAG_symb(src) == APPLY_LAMBDA)
    my_error("qnt_simplify: lambda or apply expression found\n");
  changed = false;
  if (quantifier(DAG_symb(src)))
    {
      TDAG tmp = DAG_dup(qnt_simplify_aux2(src));
      DAG_Pflag_set(src, DAG_ptr_of(tmp));
      return DAG_of_ptr(DAG_Pflag(src)) != src;
    }
  for (i = 0; i < DAG_arity(src); i++)
    changed |= qnt_simplify_aux1(DAG_arg(src, i));
  if (!changed)
    {
      DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(src)));
    }
  else
    {
      TDAG * PDAG, tmp;
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); i++)
        PDAG[i] = DAG_of_ptr(DAG_Pflag(DAG_arg(src, i)));
      tmp = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
      DAG_Pflag_set(src, DAG_ptr_of(tmp));
    }
  return changed;
}

/*--------------------------------------------------------------*/

static TDAG
qnt_simplify_aux(TDAG src)
/* PF returns a DAG where quantifiers in src have been suppressed
   when an equality perfectly defines the quantified variable
   Tree-polynomial (tree-linear in practice?) with
   respect to the quantified part
   Linear with respect to the unquantified part
   No variable should be used in imbricated quantifiers (use qnt_canonize)
   Non-destructive, no DAG_dup required */
{
  TDAG dest;
  if (!DAG_quant(src))
    return DAG_dup(src);
  qnt_counter = 0;
  qnt_simplify_aux1(src);
  dest = DAG_dup(DAG_of_ptr(DAG_Pflag(src)));
  DAG_free_Pflag(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

#ifdef OLDPROOF
TDAG
qnt_tidy(TDAG src OPTC_PROOF(Tproof *Pproof))
#else
TDAG
qnt_tidy(TDAG src)
#endif
{
  TDAG dest1, dest2, dest3;
  DAG_symb_var_resize(stack_size(DAG_sort_stack));
  if (!DAG_quant(src))
    return DAG_dup(src);
#ifdef OLDPROOF
  stack_INIT(table);
#endif
  dest1 = qnt_join_quantifiers(src);
  dest2 = qnt_canonize(dest1);
  dest3 = qnt_join_quantifiers(dest2);
#ifdef DEBUG_QNT_TIDY
  if (dest1 != src)
    my_DAG_message("qnt_tidy: quantifiers joined:\n%D\n to %D\n", src, dest1);
  if (dest2 != dest1)
    my_DAG_message("qnt_tidy: canonized:\n%D\n to %D\n", src, dest2);
  if (dest3 != dest2)
    my_DAG_message("qnt_tidy: quantifiers joined (2nd pass):\n%D\n to %D\n", src, dest2);
#endif
  DAG_free(dest1);
  DAG_free(dest2);
#ifdef OLDPROOF
  *Pproof = proof_deep_res(dest3, *Pproof, table);
  stack_free(table);
#endif
  return dest3;
}

/*--------------------------------------------------------------*/

TDAG
qnt_simplify(TDAG src)
{
  TDAG dest;
  if (!DAG_quant(src))
    return DAG_dup(src);
  dest = qnt_simplify_aux(src);
#ifdef DEBUG_QNT_TIDY
  if (dest != src)
    my_DAG_message("qnt_simplify: modified formula:\n%D\n to %D\n",
                   src, dest);
#endif
  return dest;
}

/*--------------------------------------------------------------*/

void
qnt_simplify_init(void)
{
  stack_INIT(sort_var);
  stack_INIT(sort_var_c);
}

/*--------------------------------------------------------------*/

void
qnt_simplify_done(void)
{
  DAG_symb_var_resize(0);
  stack_free(sort_var);
  stack_free(sort_var_c);
}
