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
  Module for simplifying formulas and terms
  --------------------------------------------------------------
*/

#include <stdlib.h>
#include <gmp.h>

#include "veriT-qsort.h"

#include "general.h"
#include "statistics.h"

#include "DAG-print.h"
#include "DAG.h"
#include "DAG-arith.h"
#include "DAG-tmp.h"
#include "DAG-flag.h"
#include "DAG-ptr.h"
#include "recursion.h"
#include "simplify.h"

/* TODO eliminate all about AC, and use flattening
   simplify the main functions
   check if there is anything useful with simplify_boolean_node and eliminate
   eliminate simplify_free*
*/

/* #define DEBUG_SIMPLIFY_AC */
/* #define SIMP_STAT */

#ifdef SIMP_STAT
#define STAT_INC( A, B ) stats_easy_inc(#A, "simp: " B, "%4d")
#else
#define STAT_INC( A, B ) ;
#endif

#define mpz_is_zero(A) (mpz_cmp_ui(A, 0u) == 0)
#define mpq_is_int(A) (mpz_cmp_ui(mpq_denref(A), 1u) == 0)
#define mpq_is_zero(A) (mpz_cmp_ui(mpq_numref(A), 0u) == 0)
#define mpq_is_one(A) ((mpz_cmp_ui(mpq_numref(A), 1u) == 0) && mpq_is_int(A))

mpq_t mpq_tmp1, mpq_tmp2;
mpz_t mpz_tmp1, mpz_tmp2;

static TDAG simplify_node(TDAG src);
static void simplify_AC(TDAG src);

static inline bool
DAG_opposite(TDAG DAG0, TDAG DAG1)
{
  return (DAG_symb(DAG0) == CONNECTOR_NOT && DAG_arg0(DAG0) == DAG1)
    || (DAG_symb(DAG1) == CONNECTOR_NOT && DAG_arg0(DAG1) == DAG0);
}

/*
  --------------------------------------------------------------
  General simplification functions
  --------------------------------------------------------------
*/

/**
   \brief count the number of elements in the AC list, removing duplicates
   \pre symb is an associative and commutative operator */
static unsigned
simplify_AC_count_args(Tsymb symb, TDAG src)
{
  unsigned i, result;
  if (DAG_flag(src)) return 0;
  DAG_flag_set(src, 1);
  if (DAG_symb(src) != symb)
    return 1;
  result = 0;
  for (i = 0; i < DAG_arity(src); ++i)
    result += simplify_AC_count_args(symb, DAG_arg(src, i));
  return result;
}

/*--------------------------------------------------------------*/

/**
   \pre collects elements in the AC list, removing dups
   \param symb an associative and commutative operator
   \param src the DAG on which to collect args */
static void
simplify_AC_collect_args(Tsymb symb, TDAG src, TDAG ** PPDAG)
{
  if (!DAG_flag(src)) return;
  DAG_flag_set(src, 0);
  if (DAG_symb(src) == symb)
    {
      unsigned i;
      for (i = 0; i < DAG_arity(src); ++i)
        simplify_AC_collect_args(symb, DAG_arg(src, i), PPDAG);
    }
  else
    {
      **PPDAG = src;
      *PPDAG += 1;
    }
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is not an associative and commutative operator */
static TDAG
simplify_AC_args(TDAG src)
{
  unsigned i;
  bool changed;
  TDAG * PDAG;

  assert(!DAG_Pflag(src));
  changed = false;
  for (i = 0; i < DAG_arity(src); ++i)
    {
      simplify_AC(DAG_arg(src, i));
      changed |= (DAG_arg(src, i) != DAG_of_ptr(DAG_Pflag(DAG_arg(src, i))));
    }
  if (!changed)
    return src;

  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  for (i = 0; i < DAG_arity(src); ++i)
    PDAG[i] = DAG_of_ptr(DAG_Pflag(DAG_arg(src, i)));
  return DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is an associative and commutative operator
   \brief The simplifications performed are illustrated by the
   following examples, where f is an AC symbol with idempotence:
   * (f (f x1 (f x2 x3) x4) -> (f x1 x2 x3 x4)
   * (f x1 x1 x2) -> (f x1 x2)
   * (f x1 x1) -> x1
   \note we do not worry about commutativity actually.
 */
static void
simplify_AC_aux_AC(TDAG src)
{
  TDAG DAG0, DAG1;
  unsigned new_arity, i;
  int changed;

#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n *** src = %D\n", src);
#endif
  assert(!DAG_Pflag(src));

  new_arity = simplify_AC_count_args(DAG_symb(src), src);
  changed = (DAG_arity(src) != new_arity);
  for (i = 0; i < DAG_arity(src) && !changed; ++i)
    changed |= (DAG_symb(src) == DAG_symb(DAG_arg(src, i)));

  if (!changed)
    {
      DAG_reset_flag(src);
      DAG0 = DAG_dup(src);
    }
  else
    {
      TDAG * ptr;
      TDAG * PDAG;
      STAT_INC(AC, "AC");
      MY_MALLOC(PDAG, new_arity * sizeof(TDAG));
      ptr = PDAG;
      simplify_AC_collect_args(DAG_symb(src), src, &ptr);
      if (new_arity == 1)
        {
          DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(PDAG[0])));
          free(PDAG);
          return;
        }
      DAG0 = DAG_dup(DAG_new(DAG_symb(src), new_arity, PDAG));
    }

  /* DAG0 is result of applying simplification to src */
  assert(DAG_symb(DAG0) == DAG_symb(src));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n *** src = %D\n *** DAG0 = %D\n", src, DAG0);
#endif
  if (DAG_Pflag(DAG0))
    {
      DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(DAG_of_ptr(DAG_Pflag(DAG0)))));
      DAG_free(DAG0);
      return;
    }

  DAG1 = DAG_dup(simplify_AC_args(DAG0));
  DAG_free(DAG0);

  if (DAG_Pflag(DAG1))
    {
      assert(!DAG_Pflag(src));
      DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(DAG_of_ptr(DAG_Pflag(DAG1)))));
      DAG_free(DAG1);
      return;
    }

  /* DAG1 is result of applying simplification to DAG0 descendants */
  assert(DAG_symb(DAG1) == DAG_symb(src));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n *** src = %D\n *** DAG1 = %D\n", src, DAG1);
#endif
  changed = 0;
  for (i = 0; i < DAG_arity(DAG1); ++i)
    changed |= (DAG_symb(src) == DAG_symb(DAG_arg(DAG1, i)));
  assert(!DAG_Pflag(src));
  if (changed)
    {
      TDAG * ptr;
      TDAG * PDAG;
      TDAG tmp;
      STAT_INC(AC, "AC");
      new_arity = simplify_AC_count_args(DAG_symb(DAG1), DAG1);
      MY_MALLOC(PDAG, new_arity * sizeof(TDAG));
      ptr = PDAG;
      simplify_AC_collect_args(DAG_symb(src), DAG1, &ptr);
      assert(ptr - PDAG == new_arity);
      if (new_arity == 1)
        {
          DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(PDAG[0])));
          free(PDAG);
          DAG_free(DAG1);
          return;
        }
      veriT_qsort(PDAG, new_arity, sizeof(TDAG), (TFcmp) DAG_cmp_q);
      tmp = DAG_dup(DAG_new(DAG_symb(DAG1), new_arity, PDAG));
      DAG_Pflag_set(src, DAG_ptr_of(tmp));
    }
  else
    DAG_Pflag_set(src, DAG_ptr_of(DAG_dup(DAG1)));

  DAG_free(DAG1);
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_AC\n*** src = %D\n*** DAG_Pflag(src) = %D\n",
                  src, DAG_Pflag(src));
#endif
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is not an associative and commutative operator */
static void
simplify_AC_aux_not_AC(TDAG src)
{
  TDAG tmp;
  assert(!DAG_Pflag(src));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_not_AC\n*** src = %D\n", src);
#endif
  tmp = DAG_dup(simplify_AC_args(src));
  DAG_Pflag_set(src, DAG_ptr_of(tmp));
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC_aux_not_AC\n*** src = %D *** DAG_Pflag(src) = %D\n",
                  src, DAG_Pflag(src));
#endif
}

/*--------------------------------------------------------------*/

/**
   \pre DAG_symb(src) is an associative and commutative operator */
static void
simplify_AC(TDAG src)
{
  if (DAG_Pflag(src))
    return;
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC\n *** src = %D\n", src);
#endif
  if (DAG_symb(src) != CONNECTOR_OR && DAG_symb(src) != CONNECTOR_AND)
    simplify_AC_aux_not_AC(src);
  else
    simplify_AC_aux_AC(src);
#ifdef DEBUG_SIMPLIFY_AC
  my_DAG_message("simplify_AC\n *** src = %D *** DAG_Pflag(src) = %D\n",
                  src, DAG_Pflag(src));
#endif
}

/*--------------------------------------------------------------*/

#if 0
static TDAG
simplify_AC(TDAG src)
/* PF For AC operators
   Examples * + AND OR */
{
  usigned i, j, k, new_arity = 0;
  TDAG *DAGs, dest;
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_symb(src) == DAG_symb(DAG_arg(src, i)))
      {
        new_arity += DAG_arity(DAG_arg(src, i));
        j++;
      }
  if (!j)
    return src;
  STAT_INC(AC, "AC");
  new_arity += DAG_arity(src) - j;
  MY_MALLOC(DAGs, new_arity * sizeof(TDAG));
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_symb(src) == DAG_symb(DAG_arg(src, i)))
      for (k = 0; k < DAG_arity(DAG_arg(src, i)); k++)
        DAGs[j++] = DAG_arg(DAG_arg(src, i), k);
    else
      DAGs[j++] = DAG_arg(src, i);
  assert(j == new_arity);
  dest = DAG_dup(DAG_new(DAG_symb(src), new_arity, DAGs));
  DAG_free(src);
  return dest;
}
#endif

/*
  --------------------------------------------------------------
  Helper functions for simplifications below
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontain
   \brief flatten terms with same top symbol
   \param src the term
   \remark useful for flattening AND, OR, +, ... */
static TDAG
simplify_flattening(TDAG src)
{
  Tsymb symb = DAG_symb(src);
  unsigned i, j;
  TDAG *PDAG;
  TDAG dest;
  for (j = 0, i = 0; i < DAG_arity(src); i++)
    j += (DAG_symb(DAG_arg(src, i)) == symb)?DAG_arity(DAG_arg(src, i)):1;
  if (j == DAG_arity(src))
    return src;
  MY_MALLOC(PDAG, j * sizeof(TDAG *));
  for (j = 0, i = 0; i < DAG_arity(src); i++)
    if (DAG_symb(DAG_arg(src, i)) == symb)
      {
        memcpy(PDAG + j, DAG_args(DAG_arg(src, i)),
               DAG_arity(DAG_arg(src, i)) * sizeof(TDAG));
        j += DAG_arity(src);
      }
    else
      PDAG[j++] = DAG_arg(src, i);
  dest = DAG_dup(DAG_new(symb, j, PDAG));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief eliminate every direct subDAG of src equal to sub
   \param src the term
   \param sub the subterm to eliminate
   \remark useful for eliminating TRUE in conjunction, FALSE in disjunction,
   0 in sum, 1 in products */
static TDAG
simplify_neutral(TDAG src, TDAG sub)
{
  unsigned i, j;
  unsigned n = DAG_arity(src);
  TDAG dest, *DAGs;
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_arg(src, i) == sub)
      n--;
  if (n == DAG_arity(src))
    return src;
  STAT_INC(neutral, "a O b O c, c -> a O b");
  MY_MALLOC(DAGs, n * sizeof(TDAG *));
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_arg(src, i) != sub)
      DAGs[j++] = DAG_arg(src, i);
  assert(j == n);
  dest = DAG_dup(DAG_new(DAG_symb(src), n, DAGs));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

/**
   \author David Déharbe
   \brief find if subterm is a direct argument (or subterm) of src
   \remark useful for simplifying TRUE in disjunction, FALSE in conjunction,
   ZERO in products */
static bool
find_arg(TDAG src, TDAG subterm)
{
  unsigned i;
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_arg(src, i) == subterm)
      return true;
  return false;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief eliminate duplicate args and sort
   \param[in] src the DAG
   \return the simplified DAG
   \remark destructive
   \remark Useful for A AND A AND B -> A AND B and A OR A OR B -> A OR B */
static TDAG
simplify_ACidem(TDAG src)
{
  unsigned i, j;
  unsigned n = DAG_arity(src);
  TDAG dest, *PDAG;
  if (n < 2)
    return src;
  for (i = 0, j = 0; i < n; i++)
    if (!DAG_misc(DAG_arg(src, i)))
      {
        DAG_misc_set(DAG_arg(src, i), 1);
        j++;
      }
  if (j == n)
    {
      for (i = 0; i < n; i++)
        DAG_misc_set(DAG_arg(src, i), 0);
      return src;
    }
  MY_MALLOC(PDAG, j * sizeof(TDAG));
  for (i = 0, j = 0; i < n; i++)
    if (DAG_misc(DAG_arg(src, i)))
      {
        PDAG[j] = DAG_arg(src, i);
        DAG_misc_set(PDAG[j], 0);
        j++;
      }
  dest = DAG_dup(DAG_new(DAG_symb(src), j, PDAG));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief find if there is a complementary pair of subterms
   \param[in] src the DAG
   \return true if there exists a complementary pair of subterms
   \pre arguments should be sorted, e.g. with simplify_ACidem
   \remark Useful for A and not A, A or not A */
static bool
find_comp(TDAG src)
{
  unsigned i;
  bool comp = false;
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_symb(DAG_arg(src, i)) == CONNECTOR_NOT)
      DAG_misc(DAG_arg0(DAG_arg(src,i))) |= 2;
    else
      DAG_misc(DAG_arg(src,i)) |= 4;
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_symb(DAG_arg(src, i)) == CONNECTOR_NOT)
      {
        comp |= (DAG_misc(DAG_arg0(DAG_arg(src,i))) == 6);
        DAG_misc_set(DAG_arg0(DAG_arg(src,i)), 0);
      }
    else
      {
        comp |= (DAG_misc(DAG_arg(src,i)) == 6);
        DAG_misc_set(DAG_arg(src,i), 0);
      }
  return comp;
}

/*
  --------------------------------------------------------------
  lifting ite
  --------------------------------------------------------------
*/

static TDAG
simplify_lift_ite(TDAG src)
     /* PF apply simple case where ite function can be lifted to
        ite connector
        e1 = ite (c, e2, e3) --> if c then e1 = e2 else e1 = e3
        actually, this leads to explosions in some cases
        turned of
     */
{
  return src;
#if 0
  TDAG dest, tmp1, tmp2, tmp3, tmp4;
  if (DAG_symb(src) != PREDICATE_EQ ||
      (DAG_symb(DAG_arg0(src)) != FUNCTION_ITE &&
       DAG_symb(DAG_arg1(src)) != FUNCTION_ITE) ||
      (DAG_symb(DAG_arg0(src)) == FUNCTION_ITE &&
       DAG_symb(DAG_arg1(src)) == FUNCTION_ITE))
    return src;
  STAT_INC(itelift, "safe lifting (some) ite from terms to formulas");
  tmp1 = DAG_arg0(src);
  tmp2 = DAG_arg1(src);
  if (DAG_symb(DAG_arg0(src)) != FUNCTION_ITE)
    SWAP(tmp1, tmp2);
  tmp3 = simplify_node(DAG_dup(DAG_eq(DAG_arg(tmp1, 1), tmp2)));
  tmp4 = simplify_node(DAG_dup(DAG_eq(DAG_arg(tmp1, 2), tmp2)));
  dest = DAG_dup(DAG_ite(DAG_arg(tmp1, 0), tmp3, tmp4));
  DAG_free(src);
  DAG_free(tmp3);
  DAG_free(tmp4);
  return simplify_node(dest);
#endif
}

/*
  --------------------------------------------------------------
  Core simplification functions
  --------------------------------------------------------------
*/

static TDAG
simplify_and(TDAG src)
{
  src = simplify_neutral(src, DAG_TRUE);
  src = simplify_ACidem(src);
  if (find_arg(src, DAG_FALSE) || find_comp(src))
    {
      STAT_INC(and, "boolean AND");
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  if (!DAG_arity(src))
    {
      STAT_INC(and, "boolean AND");
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  if (DAG_arity(src) == 1)
    {
      TDAG dest;
      dest = DAG_dup(DAG_arg0(src));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_or(TDAG src)
{
  /* A_1 OR ... A_j OR FALSE OR A_{j+1} OR ... A_n --> A_1 OR ... A_n */
  src = simplify_neutral(src, DAG_FALSE);
  src = simplify_ACidem(src);
  if (find_arg(src, DAG_TRUE) || find_comp(src))
    {
      STAT_INC(or, "boolean OR");
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  if (!DAG_arity(src))
    {
      STAT_INC(or, "boolean OR");
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  if (DAG_arity(src) == 1)
    {
      TDAG dest = DAG_dup(DAG_arg0(src));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_not(TDAG src)
{
  assert(DAG_symb(src) == CONNECTOR_NOT);
  /* NOT NOT A --> A */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT)
    {
      TDAG dest = DAG_dup(DAG_arg0(DAG_arg0(src)));
      STAT_INC(not, "boolean NOT");
      DAG_free(src);
      return dest;
    }
  /* NOT FALSE --> TRUE */
  if (DAG_arg0(src) == DAG_FALSE)
    {
      STAT_INC(not, "boolean NOT");
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  /* NOT TRUE --> FALSE */
  if (DAG_arg0(src) == DAG_TRUE)
    {
      STAT_INC(not, "boolean NOT");
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_implies(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == CONNECTOR_IMPLIES);
  /* (NOT A) => (NOT B) --> B => A */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT &&
      DAG_symb(DAG_arg1(src)) == CONNECTOR_NOT)
    {
      STAT_INC(implies, "boolean =>");
      dest = DAG_dup(DAG_implies(DAG_arg0(DAG_arg1(src)), DAG_arg0(DAG_arg0(src))));
      DAG_free(src);
      src = dest;
    }
  /* FALSE => A, A => TRUE --> TRUE */
  if (DAG_arg0(src) == DAG_FALSE || DAG_arg1(src) == DAG_TRUE)
    {
      STAT_INC(implies, "boolean =>");
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  /* TRUE => A --> A */
  else if (DAG_arg0(src) == DAG_TRUE)
    {
      STAT_INC(implies, "boolean =>");
      dest = DAG_dup(DAG_arg1(src));
      DAG_free(src);
      return dest;
    }
  /* A => FALSE --> NOT A */
  else if (DAG_arg1(src) == DAG_FALSE)
    {
      STAT_INC(implies, "boolean =>");
      dest = DAG_dup(DAG_not(DAG_arg0(src)));
      DAG_free(src);
      return simplify_not(dest);
    }
  /* A => A --> TRUE */
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      STAT_INC(implies, "boolean =>");
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  /* (NOT A) => A --> A */
  /* A => NOT A --> NOT A */
  if (DAG_opposite(DAG_arg0(src), DAG_arg1(src)))
    {
      STAT_INC(implies, "boolean =>");
      dest = DAG_dup(DAG_arg1(src));
      DAG_free(src);
      return dest;
    }
  /* (P => Q) => Q --> P OR Q */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_IMPLIES &&
      DAG_arg1(DAG_arg0(src)) == DAG_arg1(src))
    {
      STAT_INC(implies, "boolean =>");
      dest = DAG_dup(DAG_or2(DAG_arg0(DAG_arg0(src)), DAG_arg1(src)));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_equiv(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == CONNECTOR_EQUIV);
  /* (NOT A) EQV (NOT B) --> A EQV B */
  if (DAG_symb(DAG_arg0(src)) == CONNECTOR_NOT &&
      DAG_symb(DAG_arg1(src)) == CONNECTOR_NOT)
    {
      STAT_INC(equiv, "boolean EQV");
      dest = DAG_dup(DAG_equiv(DAG_arg0(DAG_arg0(src)), DAG_arg0(DAG_arg1(src))));
      DAG_free(src);
      src = dest;
    }
  /* A EQV A --> TRUE */
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      STAT_INC(equiv, "boolean EQV");
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  /* A EQV NOT A, NOT A EQV A --> FALSE */
  if (DAG_opposite(DAG_arg0(src), DAG_arg1(src)))
    {
      STAT_INC(equiv, "boolean EQV");
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  /* TRUE EQV A --> A */
  if (DAG_arg0(src) == DAG_TRUE)
    {
      STAT_INC(equiv, "boolean EQV");
      dest = DAG_dup(DAG_arg1(src));
      DAG_free(src);
      return dest;
    }
  /* A EQV TRUE --> A */
  if (DAG_arg1(src) == DAG_TRUE)
    {
      STAT_INC(equiv, "boolean EQV");
      dest = DAG_dup(DAG_arg0(src));
      DAG_free(src);
      return dest;
    }
  /* FALSE EQV A --> NOT A */
  if (DAG_arg0(src) == DAG_FALSE)
    {
      STAT_INC(equiv, "boolean EQV");
      dest = DAG_dup(DAG_not(DAG_arg1(src)));
      DAG_free(src);
      return simplify_not(dest);
    }
  /* A EQV FALSE --> NOT A */
  if (DAG_arg1(src) == DAG_FALSE)
    {
      STAT_INC(equiv, "boolean EQV");
      dest = DAG_dup(DAG_not(DAG_arg0(src)));
      DAG_free(src);
      return simplify_not(dest);
    }
  return src;
}

/*--------------------------------------------------------------*/

#define IF(DAG) (DAG_arg(DAG, 0))
#define THEN(DAG) (DAG_arg(DAG, 1))
#define ELSE(DAG) (DAG_arg((DAG),2))
static TDAG
simplify_ite(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == CONNECTOR_ITE);
  /* IF TRUE THEN A ELSE B --> A */
  if (IF(src) == DAG_TRUE)
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* IF FALSE THEN A ELSE B --> B */
  if (IF(src) == DAG_FALSE)
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(ELSE(src));
      DAG_free(src);
      return dest;
    }
  /* IF C THEN TRUE ELSE FALSE --> C */
  if (THEN(src) == DAG_TRUE && ELSE(src) == DAG_FALSE)
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(IF(src));
      DAG_free(src);
      return dest;
    }
  /* IF C THEN FALSE ELSE TRUE --> NOT C */
  if (THEN(src) == DAG_FALSE && ELSE(src) == DAG_TRUE)
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(DAG_not(IF(src)));
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF C THEN A ELSE A --> A */
  if (THEN(src) == ELSE(src))
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* IF C THEN TRUE ELSE B --> C OR B */
  if (THEN(src) == DAG_TRUE)
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(DAG_or2(IF(src), ELSE(src)));
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF C THEN A ELSE FALSE --> C AND A */
  if (ELSE(src) == DAG_FALSE)
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(DAG_and2(IF(src), THEN(src)));
      DAG_free(src);
      return simplify_and(dest);
    }
  /* IF C THEN FALSE ELSE B --> NOT C AND B */
  if (THEN(src) == DAG_FALSE)
    {
      TDAG tmp;
      STAT_INC(ite, "boolean ite");
      tmp = simplify_node(DAG_dup(DAG_not(IF(src))));
      dest = DAG_dup(DAG_and2(tmp, ELSE(src)));
      DAG_free(tmp);
      DAG_free(src);
      return simplify_and(dest);
    }
  /* IF C THEN A ELSE TRUE --> NOT C OR A */
  if (ELSE(src) == DAG_TRUE)
    {
      TDAG tmp;
      STAT_INC(ite, "boolean ite");
      tmp = simplify_node(DAG_dup(DAG_not(IF(src))));
      dest = DAG_dup(DAG_or2(tmp, THEN(src)));
      DAG_free(tmp);
      DAG_free(src);
      return simplify_node(dest);
    }
  /* IF NOT C THEN A ELSE B --> IF C THEN B ELSE A */
  if (DAG_symb(IF(src)) == CONNECTOR_NOT)
    {
      STAT_INC(ite, "boolean ite");
      dest = DAG_dup(DAG_ite(DAG_arg0(IF(src)), ELSE(src), THEN(src)));
      DAG_free(src);
      return dest;
    }
  /* ITE(C, ITE(C, T1, T2), T3) --> ITE(C, T1, T3) */
  if (DAG_symb(THEN(src)) == CONNECTOR_ITE && IF(src) == IF(THEN(src)))
    {
      STAT_INC(ite_ite, "nested ite");
      dest = DAG_dup(DAG_ite(IF(src), THEN(THEN(src)), ELSE(src)));
      DAG_free(src);
      return dest;
    }
  /* ITE(C, T1, ITE(C, T2, T3)) --> ITE(C, T1, T3) */
  if (DAG_symb(ELSE(src)) == CONNECTOR_ITE && IF(src) == IF(ELSE(src)))
    {
      STAT_INC(ite_ite, "nested ite");
      dest = DAG_dup(DAG_ite(IF(src), THEN(src), ELSE(ELSE(src))));
      DAG_free(src);
      return dest;
    }
  return src;
}
#undef IF
#undef THEN
#undef ELSE

/*--------------------------------------------------------------*/

static TDAG
simplify_eq(TDAG src)
{
  assert(DAG_symb(src) == PREDICATE_EQ && DAG_arity(src) == 2);
  if (DAG_is_number(DAG_arg0(src)) && DAG_is_number(DAG_arg1(src)))
    {
      TDAG dest;
      DAG_mpq_set(mpq_tmp1, DAG_arg0(src));
      DAG_mpq_set(mpq_tmp2, DAG_arg1(src));
      dest = DAG_dup(mpq_equal(mpq_tmp1, mpq_tmp2) ? DAG_TRUE : DAG_FALSE);
      STAT_INC(eq, "eq");
      DAG_free(src);
      return dest;
    }
  else if (DAG_arg0(src) == DAG_arg1(src))
    {
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  return src;
}

/*--------------------------------------------------------------*/

#define IF(DAG) DAG_arg(DAG, 0)
#define THEN(DAG) DAG_arg(DAG, 1)
#define ELSE(DAG) DAG_arg(DAG, 2)

static TDAG
simplify_fite(TDAG src)
{
  TDAG dest;
  assert(DAG_symb(src) == FUNCTION_ITE);
  /* ITE TRUE T1 T2 --> T1 */
  if (IF(src) == DAG_TRUE)
    {
      STAT_INC(fite, "fite");
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* ITE FALSE T1 T2 --> T1 */
  if (IF(src) == DAG_FALSE)
    {
      STAT_INC(fite, "fite");
      dest = DAG_dup(ELSE(src));
      DAG_free(src);
      return dest;
    }
  /* ITE C T1 T1 --> T1 */
  if (THEN(src) == ELSE(src))
    {
      STAT_INC(fite, "fite");
      dest = DAG_dup(THEN(src));
      DAG_free(src);
      return dest;
    }
  /* ITE NOT C T1 T2 --> ITE C T2 T1 */
  if (DAG_symb(IF(src)) == CONNECTOR_NOT)
    {
      STAT_INC(fite, "fite");
      dest = DAG_dup(DAG_new_args(FUNCTION_ITE, DAG_arg0(IF(src)),
                                  ELSE(src), THEN(src), DAG_NULL));
      DAG_free(src);
      src = dest;
    }
  /* ITE(C, ITE(C, T1, T2), T3) --> ITE(C, T1, T3) */
  if (DAG_symb(THEN(src)) == FUNCTION_ITE && IF(src) == IF(THEN(src)))
    {
      STAT_INC(ite_ite, "nested ite");
      dest = DAG_dup(DAG_new_args(FUNCTION_ITE, IF(src),
                                  THEN(THEN(src)), ELSE(src), DAG_NULL));
      DAG_free(src);
      return simplify_fite(dest);
    }
  /* ITE(C, T1, ITE(C, T2, T3)) --> ITE(C, T1, T3) */
  if (DAG_symb(ELSE(src)) == FUNCTION_ITE && IF(src) == IF(ELSE(src)))
    {
      STAT_INC(ite_ite, "nested ite");
      dest = DAG_dup(DAG_new_args(FUNCTION_ITE, IF(src),
                                  THEN(src), ELSE(ELSE(src)), DAG_NULL));
      DAG_free(src);
      return simplify_fite(dest);
    }
  return src;
}
#undef IF
#undef ELSE
#undef THEN

/*
  --------------------------------------------------------------
  Arithmetic simplification
  --------------------------------------------------------------
*/

/*--------------------------------------------------------------*/

static TDAG
simplify_less(TDAG src)
{
  assert(DAG_symb(src) == PREDICATE_LESS && DAG_arity(src) == 2);
  if (DAG_is_number(DAG_arg0(src)) && DAG_is_number(DAG_arg1(src)))
    {
      TDAG dest;
      DAG_mpq_set(mpq_tmp1, DAG_arg0(src));
      DAG_mpq_set(mpq_tmp2, DAG_arg1(src));
      dest = DAG_dup(mpq_cmp(mpq_tmp1, mpq_tmp2) < 0 ? DAG_TRUE : DAG_FALSE);
      STAT_INC(less, "less");
      DAG_free(src);
      return dest;
    }
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_leq(TDAG src)
{
  assert(DAG_symb(src) == PREDICATE_LEQ && DAG_arity(src) == 2);
  if (DAG_is_number(DAG_arg0(src)) && DAG_is_number(DAG_arg1(src)))
    {
      TDAG dest;
      DAG_mpq_set(mpq_tmp1, DAG_arg0(src));
      DAG_mpq_set(mpq_tmp2, DAG_arg1(src));
      dest = DAG_dup(mpq_cmp(mpq_tmp1, mpq_tmp2) <= 0 ? DAG_TRUE : DAG_FALSE);
      STAT_INC(less, "less");
      DAG_free(src);
      return dest;
    }
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  return src;
}

/*
  --------------------------------------------------------------
  Rewrite t >= t' to t' <= t
  Rewrite t < t' to \neg t' <= t
  Rewrite t > t' to \neg t <= t'
  --------------------------------------------------------------
*/

static TDAG
rewrite_arith_compare(TDAG src)
{
  TDAG dest = src;
  if (DAG_symb(src) == PREDICATE_GREATEREQ)
    dest = DAG_new_binary(PREDICATE_LEQ, DAG_arg1(src), DAG_arg0(src));
  else if (DAG_symb(src) == PREDICATE_LESS)
    dest = DAG_not(DAG_new_binary(PREDICATE_LEQ, DAG_arg1(src), DAG_arg0(src)));
  else if (DAG_symb(src) == PREDICATE_GREATER)
    dest = DAG_not(DAG_new_binary(PREDICATE_LEQ, DAG_arg0(src), DAG_arg1(src)));
  DAG_dup(dest);
  DAG_free(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Rewrite (- c) and (/ c d) where c and d are numbers
  --------------------------------------------------------------
*/

static TDAG
simplify_div(TDAG src)
{
  TDAG dest = DAG_NULL;
  assert(DAG_arity(src) == 2);
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      DAG_free(src);
      dest = DAG_dup(DAG_new_integer(1));
      return dest;
    }
  if (!DAG_is_number(DAG_arg1(src)))
    return src;
  DAG_mpq_set(mpq_tmp2, DAG_arg1(src));
  if (mpq_is_one(mpq_tmp2))
    {
      DAG_free(src);
      dest = DAG_dup(DAG_arg0(src));
      return dest;
    }
  if (!DAG_is_number(DAG_arg0(src)))
    return src;
  DAG_mpq_set(mpq_tmp1, DAG_arg0(src));
  mpq_div(mpq_tmp1, mpq_tmp1, mpq_tmp2);
  dest = DAG_dup(DAG_new_rational_mpq(mpq_tmp1));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_unary_minus(TDAG src)
{
  if (DAG_arity(src) != 1)
    my_error("simplify_unary_minus: strange arity for src\n");
  if (DAG_is_integer(DAG_arg0(src)))
    {
      TDAG dest;
      DAG_mpz_set(mpz_tmp1, DAG_arg0(src));
      mpz_neg(mpz_tmp1, mpz_tmp1);
      dest = DAG_dup(DAG_new_integer_mpz(mpz_tmp1));
      DAG_free(src);
      return dest;
    }
  if (DAG_is_rational(DAG_arg0(src)))
    {
      TDAG dest;
      DAG_mpq_set(mpq_tmp1, DAG_arg0(src));
      mpq_neg(mpq_tmp1, mpq_tmp1);
      dest = DAG_dup(DAG_new_rational_mpq(mpq_tmp1));
      DAG_free(src);
      return dest;
    }
  if (unary_minus(DAG_symb(DAG_arg0(src))))
    {
      TDAG dest = DAG_dup(DAG_arg0(DAG_arg0(src)));
      DAG_free(src);
      return dest;
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_sum(TDAG src)
{
  bool is_zero;
  unsigned i, j = 0, numbers = 0;
  TDAG dest;
  TDAG * PDAG;
  assert(DAG_arity(src) > 1);
  mpz_set_ui(mpz_tmp1, 0u);
  mpq_set_ui(mpq_tmp1, 0u, 1u);
  for (i = 0; i < DAG_arity(src); i++)
    if (DAG_is_integer(DAG_arg(src, i)))
      {
        numbers++;
        DAG_mpz_set(mpz_tmp2, DAG_arg(src, i));
        mpz_add(mpz_tmp1, mpz_tmp1, mpz_tmp2);
      }
    else if (DAG_is_rational(DAG_arg(src, i)))
      {
        numbers++;
        DAG_mpq_set(mpq_tmp2, DAG_arg(src, i));
        mpq_add(mpq_tmp1, mpq_tmp1, mpq_tmp2);
      }
  if (numbers == 0)
    return src;
  if (numbers == 1 && DAG_is_number(DAG_arg(src, 0)) &&
      !(mpz_is_zero(mpz_tmp1) && mpq_is_zero(mpq_tmp1)))
    return src;
  if (numbers == DAG_arity(src))
    {
      DAG_free(src);
      if (mpq_is_int(mpq_tmp1))
        {
          mpz_add(mpz_tmp1, mpz_tmp1, mpq_numref(mpq_tmp1));
          return DAG_dup(DAG_new_integer_mpz(mpz_tmp1));
        }
      mpq_set_z(mpq_tmp2, mpz_tmp1);
      mpq_add(mpq_tmp1, mpq_tmp1, mpq_tmp2);
      return DAG_dup(DAG_new_rational_mpq(mpq_tmp1));
    }
  is_zero = mpq_is_zero(mpq_tmp1) && (mpz_cmp_ui(mpz_tmp1, 0) == 0);
  if (is_zero && DAG_arity(src) - numbers == 1)
    for (i = 0; i < DAG_arity(src); ++i)
      if (!DAG_is_number(DAG_arg(src, i)))
        {
          dest = DAG_dup(DAG_arg(src, i));
          DAG_free(src);
          return dest;
        }
  assert(DAG_arity(src) > numbers);
  MY_MALLOC(PDAG, (DAG_arity(src) - numbers + (is_zero?0:1)) * sizeof(TDAG));
  if (!is_zero)
    {
      if (mpq_is_int(mpq_tmp1))
        {
          mpz_add(mpz_tmp1, mpz_tmp1, mpq_numref(mpq_tmp1));
          PDAG[j++] = DAG_new_integer_mpz(mpz_tmp1);
        }
      else
        {
          mpq_set_z(mpq_tmp2, mpz_tmp1);
          mpq_add(mpq_tmp1, mpq_tmp1, mpq_tmp2);
          PDAG[j++] = DAG_new_rational_mpq(mpq_tmp1);
        }
    }

  for (i = 0; i < DAG_arity(src); ++i)
    if (!DAG_is_number(DAG_arg(src, i)))
      PDAG[j++] = DAG_arg(src, i);
  assert(j - (is_zero?0:1) + numbers == DAG_arity(src));
  dest = DAG_dup(DAG_new(DAG_symb(src),
                         DAG_arity(src) - numbers + (is_zero?0:1), PDAG));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_minus(TDAG src)
{
  assert(DAG_arity(src) == 2);
  if (DAG_arg0(src) == DAG_arg1(src))
    {
      DAG_free(src);
      return DAG_dup(DAG_new_integer(0));
    }
  if (DAG_is_number(DAG_arg(src, 0)) && DAG_is_number(DAG_arg1(src)))
    {
      TDAG dest = DAG_NULL;
      if (DAG_is_integer(DAG_arg0(src)) && DAG_is_integer(DAG_arg1(src)))
        {
          DAG_mpz_set(mpz_tmp1, DAG_arg0(src));
          DAG_mpz_set(mpz_tmp2, DAG_arg1(src));
          mpz_sub(mpz_tmp1, mpz_tmp1, mpz_tmp2);
          dest = DAG_dup(DAG_new_integer_mpz(mpz_tmp1));
          DAG_free(src);
          return dest;
        }
      if (DAG_is_integer(DAG_arg0(src)))
        {
          DAG_mpz_set(mpz_tmp1, DAG_arg0(src));
          mpq_set_z(mpq_tmp1, mpz_tmp1);
        }
      else
        DAG_mpq_set(mpq_tmp1, DAG_arg0(src));
      if (DAG_is_integer(DAG_arg1(src)))
        {
          DAG_mpz_set(mpz_tmp2, DAG_arg1(src));
          mpq_set_z(mpq_tmp2, mpz_tmp2);
        }
      else
        DAG_mpq_set(mpq_tmp2, DAG_arg0(src));
      mpq_sub(mpq_tmp1, mpq_tmp1, mpq_tmp2);
      dest = DAG_dup(DAG_new_rational_mpq(mpq_tmp1));
      DAG_free(src);
      return dest;
    }
  if (DAG_is_number(DAG_arg1(src)))
    {
      DAG_mpq_set(mpq_tmp2, DAG_arg1(src));
      if (mpq_is_zero(mpq_tmp2))
        {
          TDAG dest = DAG_dup(DAG_arg0(src));
          DAG_free(src);
          return dest;
        }
    }
  if (DAG_is_number(DAG_arg0(src)))
    {
      DAG_mpq_set(mpq_tmp1, DAG_arg0(src));
      if (mpq_is_zero(mpq_tmp1))
        {
          TDAG dest = DAG_dup(DAG_new_unary(FUNCTION_UNARY_MINUS,
                                            DAG_arg1(src)));
          DAG_free(src);
          return dest;
        }
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_prod(TDAG src)
{
  bool is_one;
  unsigned i, j = 0, numbers = 0;
  TDAG dest;
  TDAG * PDAG;
  assert(DAG_arity(src) > 1);
  mpz_set_ui(mpz_tmp1, 1u);
  mpq_set_ui(mpq_tmp1, 1u, 1u);
  for (i = 0; i < DAG_arity(src); i++)
    {
      if (!DAG_is_number(DAG_arg(src, i)))
        continue;
      numbers++;
      DAG_mpq_set(mpq_tmp2, DAG_arg(src, i));
      mpq_mul(mpq_tmp1, mpq_tmp1, mpq_tmp2);
    }
  if (numbers == 0)
    return src;
  if (numbers == 1 && DAG_is_number(DAG_arg(src, 0))
      && !mpq_is_zero(mpq_tmp1) && !mpq_is_one(mpq_tmp1))
    return src;
  if (numbers == DAG_arity(src) || mpq_is_zero(mpq_tmp1))
    {
      DAG_free(src);
      return DAG_dup((mpq_is_int(mpq_tmp1))?DAG_new_integer_mpz(mpq_numref(mpq_tmp1)):
                     DAG_new_rational_mpq(mpq_tmp1));
    }
  is_one = mpq_is_one(mpq_tmp1);
  if (is_one && DAG_arity(src) - numbers == 1)
    for (i = 0; i < DAG_arity(src); ++i)
      if (!DAG_is_number(DAG_arg(src, i)))
        {
          dest = DAG_dup(DAG_arg(src, i));
          DAG_free(src);
          return dest;
        }
  MY_MALLOC(PDAG, (DAG_arity(src) - numbers + (is_one?0:1)) * sizeof(TDAG));
  if (!is_one)
    PDAG[j++] = (mpq_is_int(mpq_tmp1))?
      DAG_new_integer_mpz(mpq_numref(mpq_tmp1)):
      DAG_new_rational_mpq(mpq_tmp1);
  for (i = 0; i < DAG_arity(src); ++i)
    if (!DAG_is_number(DAG_arg(src, i)))
      PDAG[j++] = DAG_arg(src, i);
  assert(j - (is_one?0:1) + numbers == DAG_arity(src));
  dest = DAG_dup(DAG_new(DAG_symb(src),
                         DAG_arity(src) - numbers + (is_one?0:1), PDAG));
  DAG_free(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Quantifier simplification
  --------------------------------------------------------------
*/

static TDAG
simplify_quantifier(TDAG src)
{
  TDAG matrix;
  if (!quantifier(DAG_symb(src)))
    return src;
  matrix = DAG_arg_last(src);
  if (matrix == DAG_FALSE)
    {
      DAG_free(src);
      return DAG_dup(DAG_FALSE);
    }
  if (matrix == DAG_TRUE)
    {
      DAG_free(src);
      return DAG_dup(DAG_TRUE);
    }
  return src;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_node(TDAG src)
{
  if (DAG_symb(src) == CONNECTOR_AND)
    return simplify_and(src);
  if (DAG_symb(src) == CONNECTOR_OR)
    return simplify_or(src);
  if (DAG_symb(src) == CONNECTOR_NOT)
    return simplify_not(src);
  if (DAG_symb(src) == CONNECTOR_IMPLIES)
    return simplify_implies(src);
  if (DAG_symb(src) == CONNECTOR_EQUIV)
    return simplify_equiv(src);
  if (DAG_symb(src) == CONNECTOR_ITE)
    return simplify_ite(src);
  if (DAG_symb(src) == PREDICATE_EQ)
    return simplify_lift_ite(simplify_eq(src));
  if (DAG_symb(src) == PREDICATE_LESS ||
      DAG_symb(src) == PREDICATE_GREATEREQ ||
      DAG_symb(src) == PREDICATE_GREATER)
    src = rewrite_arith_compare(src);
  if (DAG_symb(src) == PREDICATE_LESS)
    return simplify_less(src);
  if (DAG_symb(src) == PREDICATE_LEQ)
    return simplify_leq(src);
  if (DAG_symb(src) == FUNCTION_ITE)
    return simplify_fite(src);
  if (DAG_symb(src) == FUNCTION_SUM)
    return simplify_sum(src);
  if (DAG_symb(src) == FUNCTION_MINUS)
    return simplify_minus(src);
  if (unary_minus(DAG_symb(src)))
    return simplify_unary_minus(src);
  if (DAG_symb(src) == FUNCTION_PROD)
    return simplify_prod(src);
  if (DAG_symb(src) == FUNCTION_DIV)
    return simplify_div(src);
  if (quantifier(DAG_symb(src)))
    return simplify_quantifier(src);
  return src;
}

/*--------------------------------------------------------------*/

/* TODO use DAG_tmp */

static void
simplify_free_tmp_all_rec(TDAG src)
{
  unsigned i;
  if (DAG_flag(src))
    return;
  DAG_flag_set(src, 1);
  for (i = 0; i < DAG_arity(src); i++)
    simplify_free_tmp_all_rec((TDAG) DAG_arg(src, i));
  if (DAG_Pflag(src))
    {
      DAG_free(DAG_of_ptr(DAG_Pflag(src)));
      DAG_Pflag_set(src, NULL);
    }
}

/*--------------------------------------------------------------*/

static void
simplify_free_tmp_all(TDAG src)
{
  simplify_free_tmp_all_rec(src);
  DAG_reset_flag(src);
}

/*
  --------------------------------------------------------------
  x = a and phi(x) --> phi(a)
  --------------------------------------------------------------
*/

/* x = t and phi(x) --> phi(t), if x \notin t */
/* p EQV G and H(p) --> H(G), if p \notin G */
/* forall i. p(i) EQV G(i) and H(p(*)) --> H(G(*)), if p \notin G */
/* forall i. f(i) EQV g(i) and H(f(*)) --> H(g(*)), if f \notin g */

/*--------------------------------------------------------------*/

static TDAG
simplify_boolean_node(TDAG src)
{
  TDAG dest = src;
  if (DAG_symb(src) == CONNECTOR_NOT)
    {
      TDAG DAG0 = DAG_arg0(src);
      /* !(P -> Q) ==> P & !Q */
      if (DAG_symb(DAG0) == CONNECTOR_IMPLIES)
        dest = DAG_and2(DAG_arg0(DAG0), DAG_not(DAG_arg1(DAG0)));
      /* !(P | Q) ==> !P & !Q */
      else if (DAG_symb(DAG0) == CONNECTOR_OR && DAG_arity(src) == 2)
        dest = DAG_and2(DAG_not(DAG_arg0(DAG0)), DAG_not(DAG_arg1(DAG0)));
      /* !(P & Q) ==> !P | !Q */
      else if (DAG_symb(DAG0) == CONNECTOR_AND && DAG_arity(src) == 2)
        dest = DAG_or2(DAG_not(DAG_arg0(DAG0)), DAG_not(DAG_arg1(DAG0)));
    }
  else if (DAG_symb(src) == CONNECTOR_IMPLIES)
    {
      TDAG DAG0 = DAG_arg0(src);
      TDAG DAG1 = DAG_arg1(src);
      /* P -> (Q -> R) ==> (P & Q) -> R */
      if (DAG_symb(DAG1) == CONNECTOR_IMPLIES)
        dest = DAG_implies(DAG_and2(DAG0, DAG_arg0(DAG1)), DAG_arg1(DAG1));
      /* (P -> Q) -> Q ==> P | Q */
      if (DAG_symb(DAG0) == CONNECTOR_IMPLIES && DAG_arg1(DAG0) == DAG1)
        dest = DAG_or2(DAG_arg0(DAG0), DAG1);
    }
  /* P & (P -> Q) ==> P & Q */
  else if (DAG_symb(src) == CONNECTOR_AND &&
           DAG_arity(src) == 2 &&
           DAG_symb(DAG_arg1(src)) == CONNECTOR_IMPLIES &&
           DAG_arg0(src) == DAG_arg0(DAG_arg1(src)))
    dest = DAG_and2(DAG_arg0(src), DAG_arg1(DAG_arg1(src)));
  DAG_dup(dest);
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

static TDAG
simplify_boolean(TDAG src)
{
  TDAG dest;
  dest = structural_recursion(src, simplify_boolean_node);
  DAG_free(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Elimination of duplicate args at top level
  --------------------------------------------------------------
*/

static TDAG
eliminate_duplicate_arg(TDAG src)
{
  unsigned i, j;
  TDAG * PDAG;
  TDAG dest;
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (!DAG_tmp_DAG[DAG_arg(src, i)])
      {
        DAG_tmp_DAG[DAG_arg(src, i)] = DAG_arg(src, i);
        j++;
      }
  MY_MALLOC(PDAG, j * sizeof(TDAG));
  for (i = 0, j = 0; i < DAG_arity(src); i++)
    if (DAG_tmp_DAG[DAG_arg(src, i)])
      {
        PDAG[j++] = DAG_arg(src, i);
        DAG_tmp_DAG[DAG_arg(src, i)] = DAG_NULL;
      }
  dest = DAG_dup(DAG_new(DAG_symb(src), j, PDAG));
  DAG_free(src);
  return dest;
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

TDAG
simplify_formula(TDAG src)
{
  TDAG dest;
  TDAG * PDAG;
  unsigned i;
  src = simplify_boolean(src);
  simplify_AC(src);
  dest = DAG_dup(DAG_of_ptr(DAG_Pflag(src)));
  simplify_free_tmp_all(src);
#ifdef SIMP_STAT
  if (DAG_count_nodes(src) != DAG_count_nodes(dest))
    my_message("Simplification AC: before %d nodes, after %d nodes\n",
            DAG_count_nodes(src), DAG_count_nodes(dest));
#endif
  DAG_free(src);
  src = dest;
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  memcpy(PDAG, DAG_args(src), DAG_arity(src) * sizeof(TDAG));
  /* PF for some reasons, shuffling the arguments of the top-level conjunction
     has a negative effect on efficiency */
  /* my_DAG_message("src (before simp_node): %D\n", dest); */
  for (i = 0; i < DAG_arity(src); i++)
    DAG_dup(PDAG[i]);
  structural_recursion_array(DAG_arity(src), PDAG, simplify_node);
  dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
  for (i = 0; i < DAG_arity(dest); i++)
    DAG_free(DAG_arg(dest, i));
  /* PF if top level symbol is or/and, eliminate duplicates */
  DAG_free(src);
  if (DAG_symb(dest) == CONNECTOR_OR || DAG_symb(dest) == CONNECTOR_AND)
    {
      DAG_tmp_reserve();
      dest = eliminate_duplicate_arg(dest);
      DAG_tmp_release();
    }
  return dest;
}

/*
  --------------------------------------------------------------
  Simplify an instance of a quantified formula
  --------------------------------------------------------------
*/

/*
   DD simplify_formula is based on the assumption that src is a
   conjunction, and its structure must be preserved.
   This is not the case for instances, and we have a dedicated
   simplification routine that does more work. */
TDAG
simplify_instance(TDAG src)
{
  TDAG dest;
  src = simplify_boolean(src);
  simplify_AC(src);
  dest = DAG_dup(DAG_of_ptr(DAG_Pflag(src)));
  simplify_free_tmp_all(src);
#ifdef SIMP_STAT
  if (DAG_count_nodes(src) != DAG_count_nodes(dest))
    my_message("Simplification AC: before %d nodes, after %d nodes\n",
            DAG_count_nodes(src), DAG_count_nodes(dest));
#endif
  DAG_free(src);
  src = dest;
  dest = structural_recursion(src, simplify_node);
  DAG_free(src);
  /* PF if top level symbol is or/and, eliminate duplicates */
  if (DAG_symb(dest) == CONNECTOR_OR || DAG_symb(dest) == CONNECTOR_AND)
    {
      DAG_tmp_reserve();
      dest = eliminate_duplicate_arg(dest);
      DAG_tmp_release();
    }
  return dest;
}

/*--------------------------------------------------------------*/
static bool simplify_initialized = false;

void
simplify_init(void)
{
  simplify_initialized = true;
  mpz_init(mpz_tmp1);
  mpz_init(mpz_tmp2);
  mpq_init(mpq_tmp1);
  mpq_init(mpq_tmp2);
}

/*--------------------------------------------------------------*/

void
simplify_done(void)
{
  mpz_clear(mpz_tmp1);
  mpz_clear(mpz_tmp2);
  mpq_clear(mpq_tmp1);
  mpq_clear(mpq_tmp2);
}
