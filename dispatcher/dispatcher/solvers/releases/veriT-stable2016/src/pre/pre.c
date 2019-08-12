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

#include <string.h>

#include "config.h"

#include "general.h"

#include "DAG.h"
#include "DAG-stat.h"
#include "options.h"

#ifdef DEBUG
#include "DAG-print.h"
#endif

#include "fix-trigger.h"
#include "HOL.h"
#include "binder-rename.h"
#include "bfun-elim.h"
#include "bclauses.h"
#include "distinct-elim.h"
#include "eq-norm.h"
#include "ite-elim.h"
#include "free-vars.h"
#include "inst-pre.h"
#include "inst-trigger.h"
#include "let-elim.h"
#include "nary-elim.h"
#include "pm.h"
#include "pre.h"
#include "qnt-tidy.h"
#include "qnt-trigger.h"
#include "rare-symb.h"
#include "simplify.h"
#include "skolem.h"
#include "simp-sym.h"
#include "simp-unit.h"
#include "proof.h"
#include "LA-pre.h"

static bool pre_quantifier = true;
static bool pre_eq = false;

/**
   \addtogroup arguments_user

   - --disable-simp

   Disables simplification of expressions.

 */
static bool disable_simp = 0;
static bool disable_unit_simp = 0;
static bool disable_unit_subst_simp = 0;
static bool disable_bclause = 0;
static bool disable_ackermann = 0;

/**
   \addtogroup arguments_user

   - --enable-assumption-simp

   Enables application of simplifications of assumptions

 */
static bool enable_assumption_simp = 0;

bool enable_nnf_simp = 0;

/*--------------------------------------------------------------*/

#ifdef PROOF

Tstack_DAG snapshot = NULL;

static void
pre_proof_snapshot(unsigned n, TDAG * Psrc)
{
  unsigned i;
  if (!snapshot)
    {
      stack_INIT(snapshot);
    }
  else
    for (i = 0; i < stack_size(snapshot); i++)
      DAG_free(stack_get(snapshot,i));
  stack_resize(snapshot, n);
  for (i = 0; i < n; i++)
    stack_set(snapshot, i, DAG_dup(Psrc[i]));
}

/*--------------------------------------------------------------*/

static void
pre_proof_compare(unsigned n, TDAG * Psrc, Tproof * Pproof,
                  Tproof (f) (Tproof, TDAG))
{
  unsigned i;
  assert (stack_size(snapshot) == n);
  for (i = 0; i < n; i++)
    if (Psrc[i] != stack_get(snapshot, i))
      Pproof[i] = f(Pproof[i], Psrc[i]);
}

/*--------------------------------------------------------------*/

static void
pre_proof_erase_snapshot(void)
{
  unsigned i;
  if (snapshot)
    for (i = 0; i < stack_size(snapshot); i++)
      DAG_free(stack_get(snapshot,i));
  stack_free(snapshot);
}
#endif

/*--------------------------------------------------------------*/

static TDAG
pre_HOL_to_FOL(TDAG src)
{
  TDAG dest;
  /**************** fix_triggers */
  /* DD normalizes triggers (quantification patterns)
     this should be done once and forall on every input formula
     instances should not be reprocessed */
  /* In principle this should also be applied on formulas coming from
     macros, etc.  However, since this is a favour for the user who
     writes badly formed formulas, it will not be applied on macros */
  fix_trigger_array(1, &src);

  /**************** macro_subst */
  /* PF HOL->FOL: the higher order processing */
  /* binder_rename is applied on macro body before expansion so that
     - no bound variable of the macro interacts with bound/unbound vars
     of the formula
     - no free symbol of the macro interacts with binders of the formulas
     thanks to the fact that binder_rename uses fresh names
     To avoid problems with macro containing macros, this occurs
     at macro expansion in macro_substitute */
  /* requires the binder_rename invariant
     should come high in the list because it will introduce new terms
     that also need processing */
  dest = HOL_to_FOL(src);
  DAG_free(src);
  src = dest;

  /**************** bfun_elim */
  dest = bfun_elim(src);
  DAG_free(src);
  src = dest;
  /* my_DAG_message("HOL_to_FOL %D\n", src); */
  return src;
}

/*--------------------------------------------------------------*/

#ifdef PROOF

static void
pre_HOL_to_FOL_array_proof(unsigned n, TDAG * Psrc, Tproof * Pproof)
{
  /**************** fix_triggers */
  /* DD normalizes triggers (quantification patterns)
     this should be done once and forall on every input formula
     instances should not be reprocessed */
  /* In principle this should also be applied on formulas coming from
     macros, etc.  However, since this is a favour for the user who
     writes badly formed formulas, it will not be applied on macros */
  fix_trigger_array(n, Psrc);
  /**************** HOL_to_FOL */
  /* PF HOL->FOL: the higher order processing */
  /* binder_rename is applied on macro body before expansion so that
     - no bound variable of the macro interacts with bound/unbound vars
     of the formula
     - no free symbol of the macro interacts with binders of the formulas
     thanks to the fact that binder_rename uses fresh names
     To avoid problems with macro containing macros, this occurs
     at macro expansion in macro_substitute */
  /**************** beta_reduction */
  /* should come after equality lowering because it could rewrite
     X = lambda x. f(x) to forall y . X(y) = ((lambda x . f(x)) y) */
  pre_proof_snapshot(n, Psrc);
  HOL_to_FOL_array(n, Psrc);
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_betared);
  /* HOL-free, let-free below this point, but still bfuns */
  /**************** bfun_elim */
  pre_proof_snapshot(n, Psrc);
  bfun_elim_array(n, Psrc);
  pre_proof_compare(n, Psrc, Pproof, proof_tmp_bfun_elim);
  pre_proof_erase_snapshot();
}

#endif

/*--------------------------------------------------------------*/

static TDAG
pre_lang_red(TDAG src)
{
  TDAG dest;
  /**************** equality normalization */
  /* replace equalities between propasitions to equivalencies */
  dest = eq_norm(src);
  DAG_free(src);
  src = dest;

  /**************** nary_elim */
  /* replace n-ary by binary operators
     necessary for Skolemization */
  dest = nary_elim(src);
  DAG_free(src);
  src = dest;

  /**************** distinct_elim */
  dest = distinct_elim(src); /* eliminates distinct */
  DAG_free(src);

  return dest;
}

/*--------------------------------------------------------------*/

#ifdef PROOF

static TDAG
pre_lang_red_proof(TDAG src, Tproof * Pproof)
{
  TDAG dest;
  /**************** equality normalization */
  /* replace equalities between propasitions to equivalencies */
  dest = eq_norm(src);
  if (src != dest)
    *Pproof = proof_tmp_eq_norm(*Pproof, dest);
  DAG_free(src);
  src = dest;

  /**************** nary_elim */
  /* replace n-ary by binary operators
     necessary for Skolemization */
  dest = nary_elim(src);
  if (src != dest)
    *Pproof = proof_tmp_nary_elim(*Pproof, dest);
  DAG_free(src);
  src = dest;

  /**************** distinct_elim */
  dest = distinct_elim(src); /* eliminates distinct */
  if (src != dest)
    *Pproof = proof_tmp_distinct_elim(*Pproof, dest);
  DAG_free(src);
  return dest;
}

#endif /* PROOF */

/*--------------------------------------------------------------*/

#include "inst-pre.h"

static TDAG
pre_quant_ite(TDAG src)
{
  TDAG dest;
  int first = 1, changed = 0;
  dest = qnt_tidy(src);
  DAG_free(src);
  src = dest;
  /* Completely breaks the binder_rename invariant */
  /* Skolemization does not go into ite terms
     This should thus be applied after ite elimination */
  dest = qnt_simplify(src);
  DAG_free(src);
  src = dest;
  /* here is a loop to eliminate skolem quant and ites */
  do
    {
      if (!disable_simp)
        src = simplify_formula(src);
      dest = ite_elim(src);

      /* ite elim may reveal new skolemizable quant */
      if (!first && src == dest)
        {
          DAG_free(dest);
          break;
        }
      else
        first = 0;
      DAG_free(src);
      src = dest;
      /*      dest = skolemize(src OPTC_PROOF(Pproof)); */
      dest = skolemize(src);
      /* skolemize may make new ite terms appear */
      changed = (src != dest);
      DAG_free(src);
      src = dest;
    }
  while (changed);
  if (enable_nnf_simp)
    {
      /* Remove conectives besides AND/OR/NOT from scope of quantifiers */
      dest = qnt_connectives(src);
      changed = changed || (src != dest);
      DAG_free(src);
      src = dest;
      if (!disable_simp && changed)
        {
          src = simplify_formula(src);
          changed = false;
        }
      /* Put quantified formulas in NNF, remove weak existentials */
      dest = qnt_NNF(src);
      changed = changed || (src != dest);
      DAG_free(src);
      src = dest;
      if (!disable_simp && changed)
        {
          src = simplify_formula(src);
          changed = false;
        }
      dest = qnt_uniq_vars(src);
      if (!disable_simp && src != dest)
        src = simplify_formula(src);
      DAG_free(src);
      src = dest;
      /* dest = qnt_NF(src); */
      /* DAG_free(src); */
      /* src = dest; */
    }
  return src;
}

/*--------------------------------------------------------------*/

#if PROOF

static TDAG
pre_quant_ite_proof(TDAG src, Tproof * Pproof)
{
  TDAG dest;
  int first = 1, changed = 0;
  dest = qnt_tidy(src);
  if (src != dest)
    *Pproof = proof_tmp_qnt_tidy(*Pproof, dest);
  DAG_free(src);
  src = dest;
  /* Completely breaks the binder_rename invariant */
  /* Skolemization does not go into ite terms
     This should thus be applied after ite elimination */
  dest = qnt_simplify(src);
  if (src != dest)
    *Pproof = proof_tmp_qnt_simplify(*Pproof, dest);
  DAG_free(src);
  src = dest;
  /* here is a loop to eliminate skolem quant and ites */
  do
    {
#ifndef PROOF
      if (!disable_simp)
        src = simplify_formula(src);
#endif
      dest = ite_elim(src);
      /* ite elim may reveal new skolemizable quant */
      if (src != dest)
        *Pproof = proof_tmp_ite_elim(*Pproof, dest);
      if (!first && src == dest)
        {
          DAG_free(dest);
          break;
        }
      else
        first = 0;
      DAG_free(src);
      src = dest;
      /*      dest = skolemize(src OPTC_PROOF(Pproof)); */
      dest = skolemize(src);
      /* skolemize may make new ite terms appear */
      if (src != dest)
        *Pproof = proof_tmp_skolemize(*Pproof, dest);
      changed = (src != dest);
      DAG_free(src);
      src = dest;
    }
  while (changed);
  return src;
}

#endif

/*--------------------------------------------------------------*/

static TDAG
pre_ite(TDAG src)
{
  TDAG dest;
  /* simplify formula may handle ite in a more gentle way than
     ite_elim, it should therefore come before */
  if (!disable_simp)
    src = simplify_formula(src);
  /* This has no effect inside quantifiers
     This thus should be applied after any rewrite rule that may
     eliminate quantifiers */
  dest = ite_elim(src);
  DAG_free(src);
  src = dest;
  return src;
}

/*--------------------------------------------------------------*/

#if PROOF
static TDAG
pre_ite_proof(TDAG src, Tproof * Pproof)
{
  TDAG dest;
  /* simplify formula may handle ite in a more gentle way than
     ite_elim, it should therefore come before */
#ifndef PROOF
  if (!disable_simp)
    src = simplify_formula(src);
#endif
  /* This has no effect inside quantifiers
     This thus should be applied after any rewrite rule that may
     eliminate quantifiers */
  dest = ite_elim(src);
  if (src != dest)
    *Pproof = proof_tmp_ite_elim(*Pproof, dest);
  DAG_free(src);
  src = dest;
  return src;
}
#endif

/*--------------------------------------------------------------*/

static TDAG
pre_non_essential(TDAG src)
{
  TDAG dest;
  if (!disable_ackermann)
    {
      dest = rare_symb(src);
      DAG_free(src);
      src = dest;
    }

  dest = simp_sym(src);
  DAG_free(src);
  src = dest;

  if (!disable_unit_subst_simp)
    src = simplify_formula_sat(src);
  return src;
}

/*--------------------------------------------------------------*/

/* This uses NO, CC, etc..., and will only replace atoms by TRUE/FALSE
   this should come late */
/* Requires to have free access to the NO stack */
/* TODO: for incrementality, it should only be activated if the NO stack is empty */
static TDAG
pre_unit(TDAG src)
{
  TDAG dest;
  Tunsigned orig_n;
  Tunsigned dest_n = DAG_count_nodes(src);
  do
    {
      dest = simplify_unit(src);
      if (dest == src)
        {
          DAG_free(dest);
          break;
        }
      DAG_free(src);
      src = dest;
      src = simplify_formula(src);

      orig_n = dest_n;
      dest_n = DAG_count_nodes(src);
      qnt_ground(src);
    }
  while ((dest_n > 1) && /* final formula is not TRUE or FALSE */
         /* previous decrease at least 10 % of nodes */
         ((orig_n - dest_n) * 10 > orig_n) &&
         /* previous decrease of at least 20 nodes */
         ((orig_n - dest_n) > 20));

  return src;
}

/*--------------------------------------------------------------*/

TDAG
pre_process(TDAG src)
{
  TDAG dest;
  src = pre_HOL_to_FOL(src);
  assert(is_FOL_strict(src));
  /* HOL-free, let-free below this point */
  src = pre_lang_red(src);
  /* HOL-free, let-free, symbol-normalized below this point */

  /* quantifier handling (skolem, tidy, simplify) is sensitive to HOL
     it should come after HOL elimination */
  if (pre_quantifier && DAG_quant(src))
    src = pre_quant_ite(src);
  else
    src = pre_ite(src);

  src = pre_non_essential(src);
  if (!disable_simp)
    src = simplify_formula(src);

  /* this should come very last because it only tags formulas
     ground bit is used in congruence closure, and quantifier handling,
     so this should come before unit simplification */
  qnt_ground(src);

  if (!disable_unit_simp)
    src = pre_unit(src);

  if (!disable_bclause)
    {
      dest = bclauses_add(src);
      DAG_free(src);
      src = dest;
      src = simplify_formula(src);
      qnt_ground(src);
    }
  /* PF this should come late because = may be used or generated before,
     e.g. for ite terms */
  if (pre_eq)
    LA_pre_array(1, &src);
  /* HB sets variables infrastructure */
  set_fvars(src);
  /* HOL-free
     let-free
     symbol-normalized i.e. variety of symbols are rewritten (or n-ary
     to binary) so that no attention to those is necessary in the solver
     qnt_ground should be applied
     qnt_tidy should be applied
     ite should only occur in quantified formulas
     no strong (skolemizable) quantifier outside ite terms */
  return src;
}

/*--------------------------------------------------------------*/

#ifdef PROOF

void
pre_process_array_proof(unsigned n, TDAG * Psrc, Tproof * Pproof)
{
  unsigned i;
  pre_HOL_to_FOL_array_proof(n, Psrc, Pproof);
  for (i = 0; i < n; i++)
    assert(is_FOL_strict(Psrc[i]));
  /* HOL-free, let-free below this point */
  for (i = 0; i < n; i++)
    Psrc[i] = pre_lang_red_proof(Psrc[i], &Pproof[i]);
  /* HOL-free, let-free, symbol-normalized below this point */

  /* quantifier handling (skolem, tidy, simplify) is sensitive to HOL
     it should come after HOL elimination */
  for (i = 0; i < n; i++)
    if (pre_quantifier && DAG_quant(Psrc[i]))
      Psrc[i] = pre_quant_ite_proof(Psrc[i], &Pproof[i]);
    else
      Psrc[i] = pre_ite_proof(Psrc[i], &Pproof[i]);
  /* this should come very last because it only tags formulas
     ground bit is used in congruence closure, and quantifier handling,
     so this should come before unit simplification */
#ifndef PROOF
  /* IMPROVE */
  src = pre_non_essential(src);
  if (!disable_simp)
    src = simplify_formula(src);
#endif
  for (i = 0; i < n; i++)
    qnt_ground(Psrc[i]);

#ifndef PROOF
  /* IMPROVE */
  if (!disable_unit_simp)
    src = pre_unit(src);

  if (!disable_bclause)
    {
      TDAG dest = bclauses_add(src);
      DAG_free(src);
      src = dest;
      src = simplify_formula(src);
      qnt_ground(src);
    }
#endif
  /* PF this should come late because = may be used or generated before,
     e.g. for ite terms */
  /* PF this should come late because = may be used or generated before,
     e.g. for ite terms */
  if (pre_eq) /* TODO: sure here??? what about qnt_grount */
    {
      pre_proof_snapshot(n, Psrc);
      LA_pre_array(n, Psrc);
      pre_proof_compare(n, Psrc, Pproof, proof_tmp_LA_pre);
      pre_proof_erase_snapshot();
    }
  /* HB sets variables infrastructure */
  if (pre_quantifier)
    for (i = 0; i < n; i++)
      if (DAG_quant(Psrc[i]))
        set_fvars(Psrc[i]);
  /* HOL-free
     let-free
     symbol-normalized i.e. variety of symbols are rewritten (or n-ary
     to binary) so that no attention to those is necessary in the solver
     qnt_ground should be applied
     qnt_tidy should be applied
     ite should only occur in quantified formulas
     no strong (skolemizable) quantifier outside ite terms */
}

#endif

/*--------------------------------------------------------------*/

TDAG
pre_process_instance(TDAG src)
{
  TDAG quant, instance, lemma;
  assert(DAG_arity(src) == 2);
  quant = DAG_arg0(src);
  instance = DAG_dup(DAG_arg1(src));
  if (pre_quantifier && DAG_quant(instance))
    instance = pre_quant_ite(instance);
  else
    instance = pre_ite(instance);
  if (!disable_simp)
    instance = simplify_instance(instance);
  lemma = DAG_dup(DAG_or2(quant, instance));

  /* this should come very last because it only tags formulas
     ground bit is used in congruence closure, and quantifier handling,
     so this should come before unit simplification */
  qnt_ground(lemma);
  /* [TODO] how to avoid working on ground terms which were already checked? */
  /* sets variables infrastructure */
  set_fvars(lemma);
  DAG_free(src);
  DAG_free(instance);
  return lemma;
}

/*--------------------------------------------------------------*/

#ifdef PROOF
TDAG
pre_process_instance_proof(TDAG src OPTC_PROOF(Tproof * Pproof))
{
  TDAG quant, instance, lemma;
  Tproof proof;
  assert(DAG_arity(src) == 2);
  quant = DAG_arg0(src);
  instance = DAG_dup(DAG_arg1(src));
  /* quantifier handling (skolem, tidy, simplify) is sensitive to HOL
     it should come after HOL elimination */
  proof_subproof_begin();
  proof = proof_add_formula(DAG_dup(instance));
  if (pre_quantifier && DAG_quant(instance))
    instance = pre_quant_ite_proof(instance, &proof);
  else
    instance = pre_ite_proof(instance, &proof);
  if (DAG_arg1(src) != instance)
    {
      Tproof proof1, proof2, proof3;
      proof = proof_subproof_end();
      lemma = DAG_dup(DAG_or2(quant, instance));
      proof1 = proof_or(*Pproof);
      proof2 = proof_or_neg(lemma, 0);
      proof3 = proof_or_neg(lemma, 1);
      *Pproof = proof_resolve(4, proof1, proof, proof2, proof3);
    }
  else
    {
      proof_subproof_remove();
      lemma = DAG_dup(src);
    }
  /* this should come very last because it only tags formulas
     ground bit is used in congruence closure, and quantifier handling,
     so this should come before unit simplification */
  qnt_ground(lemma);
  /* [TODO] how to avoid working on ground terms which were already checked? */
  /* sets variables infrastructure */
  set_fvars(lemma);
  DAG_free(src);
  DAG_free(instance);
  return lemma;
}
#endif

/*--------------------------------------------------------------*/

void
pre_init(void)
{
  qnt_simplify_init();
  distinct_elim_init();
  skolemize_init();
  simp_sym_init();
  bclauses_init();
  options_new(0, "disable-simp", "Disable simplification of expressions.",
              &disable_simp);
  options_new(0, "disable-unit-simp",
              "Disable unit clause propagation as simplification."
              "Only available in non-interactive mode",
              &disable_unit_simp);
  options_new(0, "disable-unit-subst-simp",
              "Disables unit clause rewriting as simplification."
              "Only available in non-interactive mode",
              &disable_unit_subst_simp);
  options_new(0, "disable-ackermann",
              "Disable local Ackermannization and elimination of rare symbols.",
              &disable_ackermann);
  options_new(0, "enable-assumption-simp", "Enable simplifications of assumptions",
              &enable_assumption_simp);
  options_new(0, "enable-nnf-simp", "Qnt formulas into NNF, with var renaming",
              &enable_nnf_simp);
  options_new(0, "disable-bclause",
              "Do not optimize for binary clauses.",
              &disable_bclause);
  pre_quantifier = true;
}

/*--------------------------------------------------------------*/

void
pre_logic(char * logic)
{
  if (strcmp(logic, "QF_UF") == 0 ||
      strcmp(logic, "QF_UFIDL") == 0 ||
      strcmp(logic, "QF_IDL") == 0 ||
      strcmp(logic, "QF_RDL") == 0 ||
      strcmp(logic, "QF_LRA") == 0 ||
      strcmp(logic, "QF_UFLRA") == 0 ||
      strcmp(logic, "QF_LIA") == 0 ||
      strcmp(logic, "QF_UFLIA") == 0)
    pre_quantifier = false;
  else
    pre_quantifier = true;
  if (strcmp(logic, "QF_RDL") == 0 ||
      strcmp(logic, "QF_IDL") == 0 ||
      strcmp(logic, "QF_LRA") == 0 ||
      strcmp(logic, "QF_LIA") == 0)
    pre_eq = true;
}

/*--------------------------------------------------------------*/

void
pre_done(void)
{
  distinct_elim_done();
  bclauses_done();
  skolemize_done();
  simp_sym_done();
  qnt_simplify_done();
}
