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

#define DEBUG_TRIGGERS 0
#define DEBUG_INST_PRE 0

#include "options.h"
#include "statistics.h"
#include "polarities.h"
#include "recursion.h"
#include "DAG-print.h"
#include "DAG-subst.h"
#include "DAG-tmp.h"
#include "DAG-prop.h"
#include "qnt-trigger.h"
#include "qnt-tidy.h"

#include "free-vars.h"
#include "inst-pre.h"

extern bool enable_nnf_simp;

/*
  --------------------------------------------------------------
  Triggers
  --------------------------------------------------------------
*/

extern bool triggers_single_weak;
extern bool triggers_multi_weak;

/** \brief associates a set of variables to sets of terms which combined have
    those variables */
typedef struct Tmulti_Cand
{
  Tstack_DAG vars;
  Tstack_DAGstack terms_sets;
} Tmulti_Cand;

TSstack(_multi_Cand, Tmulti_Cand); /* typedefs Tstack_multi_Cand */

/*--------------------------------------------------------------*/

int
DAG_cmp_q_stacks(Tstack_DAG *P1, Tstack_DAG *P2)
{
  assert(*P1 && *P2);
  return (int) stack_size(*P1) - (int) stack_size(*P2);
}

/*--------------------------------------------------------------*/

int
DAG_cmp_q_m_Cand(Tmulti_Cand *Pm_Cand1, Tmulti_Cand *Pm_Cand2)
{
  assert(Pm_Cand1->vars);
  assert(Pm_Cand2->vars);
  return (int) stack_size(Pm_Cand1->vars) - (int) stack_size(Pm_Cand2->vars);
}

/*--------------------------------------------------------------*/

static Tstack_DAGstack
copy_triggers(Tstack_DAGstack triggers)
{
  unsigned i;
  Tstack_DAGstack result;
  stack_INIT(result);
  for (i = 0; i < stack_size(triggers); ++i)
    {
      stack_inc(result);
      stack_COPY(stack_top(result), stack_get(triggers, i));
    }
  for (i = 0; i < stack_size(result); ++i)
    stack_apply(stack_get(result, i), DAG_dup);
  return result;
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief whether among the candidates there are combinations with all the
    bound variables
    \param candidates a set of candidates
    \param bound_vars a set of variables
    \return true if there is a combination with all variables, false otherwise
*/
static bool
no_combination(Tstack_multi_Cand candidates, Tstack_DAG bound_vars)
{
  unsigned i;
  Tstack_DAG local_vars;
  assert(candidates);
  if (stack_is_empty(candidates))
    return true;
  stack_INIT(local_vars);
  for (i = 0; i < stack_size(candidates); ++i)
    stack_merge(local_vars, stack_get(candidates, i).vars);
  stack_sort(local_vars, DAG_cmp_q);
  stack_uniq(local_vars);
  if (stack_size(local_vars) < stack_size(bound_vars))
    {
      stack_free(local_vars);
      return true;
    }
  stack_free(local_vars);
  return false;
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief creates new candidate with same variables and the combined term sets
    \param m_Cand1 the first candidate
    \param m_Cand2 the second candidate
    \return a new candidate
    \remark the variables of the candidates must be disjoint for at least one
    element
    \remark all information is copied, so the combination can be freely
    destroyed */
static Tmulti_Cand
combine_m_Cand_terms(Tmulti_Cand m_Cand1, Tmulti_Cand m_Cand2)
{
  unsigned i, j;
  Tmulti_Cand result;
#ifdef DEBUG
  Tstack_DAG stack;
  stack = stack_size(m_Cand1.vars) > stack_size(m_Cand2.vars) ?
    stack_DAG_difference(m_Cand1.vars, m_Cand2.vars) :
    stack_DAG_difference(m_Cand2.vars, m_Cand1.vars);
  assert(!stack_is_empty(stack));
  stack_free(stack);
#endif
  /* Merge variables */
  stack_COPY(result.vars, m_Cand1.vars);
  stack_merge(result.vars, m_Cand2.vars);
  stack_sort(result.vars, DAG_cmp_q);
  stack_uniq(result.vars);
  stack_INIT(result.terms_sets);
  /* Get all pairs of terms sets */
  for (i = 0; i < stack_size(m_Cand1.terms_sets); ++i)
    for (j = 0; j < stack_size(m_Cand2.terms_sets); ++j)
      {
        stack_inc(result.terms_sets);
        stack_COPY(stack_top(result.terms_sets), stack_get(m_Cand1.terms_sets, i));
        stack_merge(stack_top(result.terms_sets), stack_get(m_Cand2.terms_sets, j));
      }
  return result;
}

/*--------------------------------------------------------------*/

/**
   \author Haniel Barbosa

   \brief successively combines candidates until one with all variables is
   achieved
   \param index the index of the first next candidate to be considered
   \param candidate the candidate built so far
   \param all_candidates a set of candidates
   \param bound_vars a set of variables
   \return a candidate whose collection of sets of terms yield a multi-trigger
   for the given variables, if any, otherwise NULL */
Tmulti_Cand
combine_candidates(unsigned index, Tmulti_Cand candidate,
                   Tstack_multi_Cand all_candidates, Tstack_DAG bound_vars)
{
  unsigned i;
  Tmulti_Cand result, new, tmp;
  Tstack_multi_Cand local_results;
  stack_COPY(result.vars, bound_vars);
  stack_INIT(result.terms_sets);
  /* candidate is a multi-trigger */
  if (stack_size(candidate.vars) == stack_size(bound_vars))
    {
#ifdef DEBUG
      assert(stack_DAG_equal(candidate.vars, bound_vars));
#endif
      for (i = 0; i < stack_size(candidate.terms_sets); ++i)
        {
          stack_inc(result.terms_sets);
          stack_COPY(stack_top(result.terms_sets), stack_get(candidate.terms_sets, i));
        }
      return result;
    }
  stack_INIT(local_results);
  for (i = index; i < stack_size(all_candidates); ++i)
    {
      /* Whether this candidate adds variables */
      if (stack_DAG_subset(stack_get(all_candidates, i).vars, candidate.vars))
        continue;
      /* Combine current candidate with new term */
      tmp = combine_m_Cand_terms(stack_get(all_candidates, i), candidate);
      /* Combine with remaining terms */
      new = combine_candidates(i + 1, tmp, all_candidates, bound_vars);
      /* There was a succesfull combination */
      if (new.terms_sets)
        stack_push(local_results, new);
      stack_free(tmp.vars);
      stack_apply(tmp.terms_sets, stack_free);
      stack_free(tmp.terms_sets);
    }
  /* No succesful combination */
  if (stack_is_empty(local_results))
    {
      stack_free(local_results);
      stack_free(result.vars);
      stack_free(result.terms_sets);
      return result;
    }
  /* Merge succesful combinations */
  while (!stack_is_empty(local_results))
    {
      new = stack_pop(local_results);
      assert(stack_size(new.vars) == stack_size(bound_vars) && new.terms_sets);
      stack_free(new.vars);
      stack_merge(result.terms_sets, new.terms_sets);
      stack_free(new.terms_sets);
    }
  stack_free(local_results);
  return result;
}

/*--------------------------------------------------------------*/

static void
clean_multi_triggers(Tstack_DAGstack * multi_triggers)
{
  unsigned i, j;
  Tstack_DAGstack result;
  /* Removes same stacks */
  if (stack_size(*multi_triggers) > 1)
    {
      stack_INIT(result);
      for (i = 0; i < stack_size(*multi_triggers); ++i)
        {
          stack_sort(stack_get(*multi_triggers, i), DAG_cmp_q);
          stack_uniq(stack_get(*multi_triggers, i));
        }
      for (i = 0; i < stack_size(*multi_triggers); ++i)
        {
          if (!stack_get(*multi_triggers, i))
            continue;
          for (j = i + 1; j < stack_size(*multi_triggers); ++j)
            {
              if (!stack_get(*multi_triggers, j))
                continue;
              if (stack_DAG_equal(stack_get(*multi_triggers, i),
                                  stack_get(*multi_triggers, j)))
                stack_free(stack_get(*multi_triggers, j));
            }
          stack_push(result, stack_get(*multi_triggers, i));
        }
      stack_reset(*multi_triggers);
      stack_merge(*multi_triggers, result);
      stack_free(result);
    }
  for (i = 0; i < stack_size(*multi_triggers); ++i)
    stack_apply(stack_get(*multi_triggers, i), DAG_dup);
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief remove redundant single-triggers
    \param single_triggers a set of terms/predicates
    \return the set of non-redundant single triggers
    \remark "redundant" is defined as a term being contained in another trigger,
    or vice-versa */
static void
clean_single_triggers(Tstack_DAG * single_triggers)
{
  stack_sort(*single_triggers, DAG_cmp_q);
  stack_uniq(*single_triggers);
  stack_apply(*single_triggers, DAG_dup);
  /* [TODO] assure that there is no trigger contained in another */
  /* [TODO] assure that if both p(x, y) and p(y, x), only one remains */
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief checks recursively for combinations of subDAGs as a multi-trigger for
    the given variables
    \param DAG a non-ground term or predicate application
    \param bound_vars a set of variables
    \return a candidate multi-trigger, i.e., sets of terms which combined have
    the given variables
    \remark it only does the recursive search if the "triggers_multi_weak"
    option is on, otherwise taking the initial DAG given as the single term in
    the multi-trigger */
Tmulti_Cand
set_multi_trigger(TDAG DAG, Tstack_DAG bound_vars)
{
  unsigned i, j;
  Tstack_multi_Cand candidates, tmp_candidates;
  Tmulti_Cand result, tmp;
  assert(DAG_arity(DAG) && !ground(DAG));
  stack_COPY(result.vars, get_fvars(DAG));
  stack_INIT(result.terms_sets);
  /* DAG itself will be considered */
  if (!triggers_multi_weak)
    {
      stack_inc(result.terms_sets);
      stack_INIT(stack_top(result.terms_sets));
      if (!(DAG_symb_type(DAG_symb(DAG)) & SYMB_INTERPRETED))
        stack_push(stack_top(result.terms_sets), DAG);
      else
        {
          /* If both args are non-vars, take the non-grs as the candidates */
          if (DAG_arity(DAG_arg0(DAG)) && DAG_arity(DAG_arg1(DAG)))
            {
              if (!ground(DAG_arg0(DAG)))
                stack_push(stack_top(result.terms_sets), DAG_arg0(DAG));
              if (!ground(DAG_arg1(DAG)))
                stack_push(stack_top(result.terms_sets), DAG_arg1(DAG));
            }
          else
            stack_push(stack_top(result.terms_sets), DAG);
        }
      return result;
    }
  /* collect candidates from non-variable non-ground sub-terms */
  stack_INIT(candidates);
  for (i = 0; i < DAG_arity(DAG); ++i)
    {
      if (!DAG_arity(DAG_arg(DAG, i)) || ground(DAG_arg(DAG, i)))
        continue;
      stack_push(candidates, set_multi_trigger(DAG_arg(DAG, i), bound_vars));
#if DEBUG
      assert(stack_top(candidates).vars &&
             stack_top(candidates).terms_sets);
#endif
    }
  /* DAG itself needs to be the candidate */
  if (no_combination(candidates, bound_vars))
    {
      stack_inc(result.terms_sets);
      stack_INIT(stack_top(result.terms_sets));
      stack_push(stack_top(result.terms_sets), DAG);
      for (i = 0; i < stack_size(candidates); ++i)
        {
          stack_free(stack_get(candidates, i).vars);
          stack_apply(stack_get(candidates, i).terms_sets, stack_free);
          stack_free(stack_get(candidates, i).terms_sets);
        }
      stack_free(candidates);
      return result;
    }
  /* There is a single candidate and it is sufficient */
  if (stack_size(candidates) == 1)
    {
      assert(stack_size(stack_top(candidates).vars) == stack_size(bound_vars));
      stack_merge(result.terms_sets, stack_top(candidates).terms_sets);
      stack_free(stack_top(candidates).vars);
      stack_free(stack_top(candidates).terms_sets);
      stack_free(candidates);
      return result;
    }
  /* Order candidate by number of variables; [TODO] Order lexicographically? */
  stack_sort(candidates, DAG_cmp_q_m_Cand);
  /* Merge term sets with the same variables */
  stack_INIT(tmp_candidates);
  for (i = 0; i < stack_size(candidates); ++i)
    {
      /* result has already been merged */
      if (!stack_get(candidates, i).terms_sets)
        continue;
      for (j = i + 1; j < stack_size(candidates); ++j)
        {
          if (!stack_get(candidates, j).terms_sets)
            continue;
          /* No longer in subset of terms with possibly same vars */
          if (stack_size(stack_get(candidates, i).vars) !=
              stack_size(stack_get(candidates, j).vars))
            break;
          if (stack_DAG_equal(stack_get(candidates, i).vars,
                              stack_get(candidates, j).vars))
            {
              stack_merge(stack_get(candidates, i).terms_sets,
                          stack_get(candidates, j).terms_sets);
              stack_free(stack_get(candidates, j).vars);
              stack_free(stack_get(candidates, j).terms_sets);
            }
        }
      stack_push(tmp_candidates, stack_get(candidates, i));
    }
  stack_free(candidates);
  candidates = tmp_candidates;
  /* Take term sets which have the same variables as DAG */
  stack_sort(candidates, DAG_cmp_q_m_Cand);
  while (!stack_is_empty(candidates) &&
         stack_size(stack_top(candidates).vars) == stack_size(get_fvars(DAG)))
    {
      tmp = stack_pop(candidates);
      stack_free(tmp.vars);
      stack_merge(result.terms_sets, tmp.terms_sets);
      stack_free(tmp.terms_sets);
    }
  if (stack_is_empty(candidates))
    {
      stack_free(candidates);
      return result;
    }
  stack_INIT(tmp_candidates);
  /* Get all minimal combinations of terms sets whose vars equal those of DAG */
  for (i = 0; i < stack_size(candidates) - 1; ++i)
    {
      tmp = combine_candidates(i + 1, stack_get(candidates, i),
                               candidates, bound_vars);
      if (tmp.terms_sets)
        stack_push(tmp_candidates, tmp);
    }
  for (i = 0; i < stack_size(candidates); ++i)
    {
      stack_free(stack_get(candidates, i).vars);
      stack_apply(stack_get(candidates, i).terms_sets, stack_free);
      stack_free(stack_get(candidates, i).terms_sets);
    }
  stack_free(candidates);
  /* Form multi-pattern for given variables */
  while (!stack_is_empty(tmp_candidates))
    {
      tmp = stack_pop(tmp_candidates);
      assert(stack_size(tmp.vars) == stack_size(bound_vars) && tmp.terms_sets);
      stack_free(tmp.vars);
      stack_merge(result.terms_sets, tmp.terms_sets);
      stack_free(tmp.terms_sets);
    }
  stack_free(tmp_candidates);
  return result;
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief searches for triggers for a set of variables among given candidates
    \param bound_vars a set of variables
    \param candidates a set of non-ground terms/predicate applications
    \return a non-empty set of triggers, if any, NULL otherwise */
Tstack_DAGstack
set_triggers_qnt(Tstack_DAG bound_vars, Tstack_DAG candidates)
{
  /* [TODO] Be destructive for candidates?? */
  unsigned i;
  Tstack_DAG single_triggers;
  Tstack_DAGstack triggers = NULL;
  Tmulti_Cand multi_triggers, tmp;
  Tstack_multi_Cand m_candidates, tmp_candidates;
  assert(stack_size(bound_vars));
  stack_INIT(single_triggers);
  stack_INIT(m_candidates);
  multi_triggers.terms_sets = NULL;
  /* [TODO] sort candidates by number of variables? */
  for (i = 0; i < stack_size(candidates); ++i)
    if (stack_size(get_fvars(stack_get(candidates, i))) == stack_size(bound_vars))
      stack_push(single_triggers, stack_get(candidates, i));
    else
      stack_push(m_candidates,
                 set_multi_trigger(stack_get(candidates, i),
                                   get_fvars(stack_get(candidates, i))));
  if (!stack_is_empty(m_candidates))
    {
      stack_INIT(tmp_candidates);
      /* Get all minimal combinations of terms sets with all bound vars */
      for (i = 0; i < stack_size(m_candidates) - 1; ++i)
        {
          tmp = combine_candidates(i + 1, stack_get(m_candidates, i),
                                   m_candidates, bound_vars);
          if (tmp.terms_sets)
            stack_push(tmp_candidates, tmp);
        }
      for (i = 0; i < stack_size(m_candidates); ++i)
        {
          stack_free(stack_get(m_candidates, i).vars);
          stack_apply(stack_get(m_candidates, i).terms_sets, stack_free);
          stack_free(stack_get(m_candidates, i).terms_sets);
        }
      stack_free(m_candidates);
      stack_INIT(multi_triggers.terms_sets);
      /* Form multi-triggers */
      while (!stack_is_empty(tmp_candidates))
        {
          tmp = stack_pop(tmp_candidates);
          assert(stack_size(tmp.vars) == stack_size(bound_vars) && tmp.terms_sets);
          stack_free(tmp.vars);
          stack_merge(multi_triggers.terms_sets, tmp.terms_sets);
          stack_free(tmp.terms_sets);
        }
      stack_free(tmp_candidates);
    }
  stack_INIT(triggers);
  clean_single_triggers(&single_triggers);
  while(!stack_is_empty(single_triggers))
    {
      stack_inc(triggers);
      stack_INIT(stack_top(triggers));
      stack_push(stack_top(triggers), stack_pop(single_triggers));
    }
  stack_free(single_triggers);
  if (multi_triggers.terms_sets)
    {
      if (!stack_is_empty(multi_triggers.terms_sets))
        {
          clean_multi_triggers(&multi_triggers.terms_sets);
          stack_merge(triggers, multi_triggers.terms_sets);
        }
      stack_free(multi_triggers.terms_sets);
    }
  if (stack_is_empty(triggers))
    stack_free(triggers);
  stack_free(candidates);
  stack_free(m_candidates);
  return triggers;
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief checks recursively if any non-ground sub-term/predicate application
    is a candidate single-trigger for the given variables
    \param DAG a non-ground term or predicate application
    \param bound_vars a set of variables
    \param candidates accumulator for non-ground terms/predicates
    \return true if the given DAG is a single-trigger for the given variables,
    false otherwise
    \remark it only does the recursive search if the "triggers_single_weak"
    option is on, otherwise taking the initial DAG given as the single
    trigger (unless it is an equality, which has a special treatment) */
bool
set_candidates_single(TDAG DAG, Tstack_DAG bound_vars, Tstack_DAG * candidates)
{
  unsigned i;
  bool has_subterm_candidate;
  assert(DAG_arity(DAG) && !ground(DAG));
  if (!triggers_single_weak)
    {
      if (!(DAG_symb_type(DAG_symb(DAG)) & SYMB_INTERPRETED))
        stack_push(*candidates, DAG);
      else
        {
          /* [TODO] should be recursive: (<= (+ fx gy) hxy) */
          /* Special handling for interpreted symbols */
          if (DAG_arity(DAG_arg0(DAG)) && !ground(DAG_arg0(DAG)) &&
              stack_size(get_fvars(DAG_arg0(DAG))) == stack_size(bound_vars))
            {
              assert(stack_DAG_equal(get_fvars(DAG_arg0(DAG)), bound_vars));
              stack_push(*candidates, DAG_arg0(DAG));
              has_subterm_candidate = true;
            }
          if (DAG_arity(DAG_arg1(DAG)) && !ground(DAG_arg1(DAG)) &&
              stack_size(get_fvars(DAG_arg1(DAG))) == stack_size(bound_vars))
            {
              assert(stack_DAG_equal(get_fvars(DAG_arg1(DAG)), bound_vars));
              stack_push(*candidates, DAG_arg1(DAG));
              has_subterm_candidate = true;
            }
          /* [TODO] This should actually become a candidate for multi-trigger... */
          if (!has_subterm_candidate)
            stack_push(*candidates, DAG);
        }
      return true;
    }
  if (stack_size(get_fvars(DAG)) != stack_size(bound_vars))
    return false;
  /* DAG or one its sub-DAGs is a single-trigger */
#if DEBUG
  Tstack_DAG stack = stack_DAG_intersect(get_fvars(DAG), bound_vars);
  assert(stack_size(stack) == stack_size(bound_vars));
  stack_free(stack);
#endif
  has_subterm_candidate = false;
  /* Whether a non-variable sub-term is a single-trigger */
  for (i = 0; i < DAG_arity(DAG); ++i)
    {
      if (!DAG_arity(DAG_arg(DAG, i)) || ground(DAG_arg(DAG, i)))
        continue;
      has_subterm_candidate =
        set_candidates_single(DAG_arg(DAG, i), bound_vars, candidates) ||
        has_subterm_candidate;
    }
  if (!has_subterm_candidate)
    stack_push(*candidates, DAG);
  return true;
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief sets candidates for single and multi-triggers
    \param DAG a DAG
    \param bound_vars a set of variables
    \param candidates accumulator for non-ground terms/predicates
    \remark broadly, candidates are non-ground, according to the given set of
    variables, terms/predicate applications. Whether strong (maximal depth) or
    weak (minimal) candidates are considered is up to the user options; at this
    level the selection is done for single triggers, while for multi-triggers
    the computation is downstream
    \remark does not consider candidates inside nested quantifiers or functional
    ITEs */
static void
set_candidates(TDAG DAG, Tstack_DAG bound_vars, Tstack_DAG * candidates)
{
  unsigned i;
  /* Variables already computed or quant subformulas; [TODO] What about
     functional ITEs? */
  if (quantifier(DAG_symb(DAG)) || ground(DAG) || DAG_symb(DAG) == FUNCTION_ITE)
    return;
  if (boolean_connector(DAG_symb(DAG)))
    {
      for (i = 0; i < DAG_arity(DAG); ++i)
        set_candidates(DAG_arg(DAG, i), bound_vars, candidates);
      return;
    }
  assert(DAG_literal(DAG));
  if (stack_size(get_fvars(DAG)) == stack_size(bound_vars))
    set_candidates_single(DAG, bound_vars, candidates);
  else
    stack_push(*candidates, DAG);
  /* set_candidates_multi(DAG, get_fvars(DAG), candidates); */
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief searchs for triggers for a set of variables within the given DAG
    \param body_DAG the body of a quantified formula
    \param bound_vars a set of variables
    \return a set of triggers
    \remark uses DAG_tmp to store variables of each DAG not under the scope of a
    nested quantifier (or functional ITE) */
static Tstack_DAGstack
compute_triggers_vars(TDAG body_DAG, Tstack_DAG bound_vars)
{
  Tstack_DAG candidates;
  Tstack_DAGstack result;
  stack_INIT(candidates);
  /* Setting variables and candidates for triggers in non-quant subformulas */
  set_candidates(body_DAG, bound_vars, &candidates);
#if DEBUG
  unsigned i;
  for (i = 0; i < stack_size(candidates); ++i)
    assert(!ground(stack_get(candidates, i)));
#endif
  /* Searching triggers in non-quant subformulas */
  result = set_triggers_qnt(bound_vars, candidates);
  assert(!result || !stack_is_empty(result));
  return result;
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa

    \brief prenex quantifiers which are safe regarding miniscoping and
    quantifier alternation, based on found triggers

    \param DAG a formula
    \param bound_vars set of variables bound by quantifiers

    \param prenex_vars set of variables bound by quantifiers

    \param bvars stack of variables to be increased with variables under the
    scope of found FORALL
    \param rename whether terms should have variables replaced
    \return a DAG without universals and a stack with all bound variables from
    each argument.

    \remark it is not destructive to parameters, however all prenexed DAGs
    created during the process that are not necessary ultimately (the temporary
    "and/or") are destructed

    \remark assumes NNF */
void
set_triggers(TDAG DAG, Tstack_DAG previous_vars, Tstack_DAGstack * triggers)
{
  unsigned i;
  Tstack_DAG local_bound_vars;
  Tstack_DAGstack qnt_triggers, nested_triggers;
  Tsymb top_symbol = DAG_symb(DAG);
  /* [TODO] for now the new triggers are computed assuming NNF (I don't want to
     do the polarity thing all over again) */
  assert(enable_nnf_simp);
  assert(!previous_vars || !stack_is_empty(previous_vars));
  if (!DAG_quant(DAG) || (DAG_literal(DAG) && top_symbol != QUANTIFIER_FORALL))
    return;
  if (top_symbol == QUANTIFIER_FORALL)
    {
      if (DAG_prop_check(DAG, DAG_PROP_TRIGGER))
        return;
      stack_INIT(local_bound_vars);
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        stack_push(local_bound_vars, DAG_arg(DAG, i));
      stack_sort(local_bound_vars, DAG_cmp_q);
      /* If not nested, get triggers to quantifier */
      if (!previous_vars)
        {
          /* [TODO] Have not only the triggers but, in case of failure, the
             candidates for multi-patterns */
          qnt_triggers = compute_triggers_vars(DAG_arg_last(DAG), local_bound_vars);
          /* Found local_triggers */
          if (qnt_triggers)
            {
#if DEBUG_TRIGGERS
              my_DAG_message("set_triggers: local for {%d}%D:\n", DAG, DAG);
              print_Tstack_DAGstack(qnt_triggers);
#endif
              stack_sort(qnt_triggers, DAG_cmp_q_stacks);
              DAG_prop_set(DAG, DAG_PROP_TRIGGER, &qnt_triggers);
              stack_free(local_bound_vars);
              return;
            }
          /* Search for triggers for this quantifier in nested ones */
          stack_INIT(qnt_triggers);
          set_triggers(DAG_arg_last(DAG), local_bound_vars, &qnt_triggers);
          if (!stack_is_empty(qnt_triggers))
            {
#if DEBUG_TRIGGERS
              my_DAG_message("set_triggers: nested for {%d}%D:\n", DAG, DAG);
              print_Tstack_DAGstack(qnt_triggers);
#endif
              stack_sort(qnt_triggers, DAG_cmp_q_stacks);
              DAG_prop_set(DAG, DAG_PROP_TRIGGER, &qnt_triggers);
            }
          else
            stack_free(qnt_triggers);
          stack_free(local_bound_vars);
          return;
        }
      /* Search for nested triggers in nonground quantifier */
      if (!ground(DAG))
        {
          stack_merge(local_bound_vars, previous_vars);
          stack_sort(local_bound_vars, DAG_cmp_q);
          nested_triggers = compute_triggers_vars(DAG_arg_last(DAG), local_bound_vars);
          /* If found, done; don't set for deeper quantifiers */
          if (nested_triggers)
            {
              stack_merge(*triggers, nested_triggers);
              stack_free(nested_triggers);
              stack_free(local_bound_vars);
              return;
            }
        }
      /* Search for deeper nested triggers */
      set_triggers(DAG_arg_last(DAG), local_bound_vars, triggers);
      stack_free(local_bound_vars);
      return;
    }
  assert(top_symbol == CONNECTOR_OR || top_symbol == CONNECTOR_AND);
  for (i = 0; i < DAG_arity(DAG); ++i)
    set_triggers(DAG_arg(DAG, i), previous_vars, triggers);
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief computes triggers in nested quantifiers
    \remark experimental
    \remark assumes NNF */
void
set_nested_triggers(TDAG DAG, Tstack_DAG previous_vars, Tstack_DAGstack * triggers)
{
  unsigned i;
  Tstack_DAG local_bound_vars;
  Tstack_DAGstack qnt_triggers, * Ptriggers;
  Tsymb top_symbol = DAG_symb(DAG);
  assert(enable_nnf_simp);
  assert(!previous_vars || !stack_is_empty(previous_vars));
  if (!DAG_quant(DAG) || (DAG_literal(DAG) && top_symbol != QUANTIFIER_FORALL))
    return;
  if (top_symbol == QUANTIFIER_FORALL)
    {
      stack_INIT(local_bound_vars);
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        stack_push(local_bound_vars, DAG_arg(DAG, i));
      stack_sort(local_bound_vars, DAG_cmp_q);
      /* If not nested, search for triggers for in nested ones */
      if (!previous_vars)
        {
          /* [TODO] This happens only with the first quantified formula called,
             no? */
          stack_INIT(qnt_triggers);
          set_nested_triggers(DAG_arg_last(DAG), local_bound_vars, &qnt_triggers);
          if (!stack_is_empty(qnt_triggers))
            {
#if DEBUG_TRIGGERS
              my_DAG_message("set_nested_triggers: nested for {%d}%D:\n", DAG, DAG);
              print_Tstack_DAGstack(qnt_triggers);
#endif
              Ptriggers = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
              if (!Ptriggers)
                {
                  stack_sort(qnt_triggers, DAG_cmp_q_stacks);
                  DAG_prop_set(DAG, DAG_PROP_TRIGGER, &qnt_triggers);
                }
              else
                {
                  /* [TODO] is this OK with the memory? */
                  stack_merge(*Ptriggers, qnt_triggers);
                  stack_free(qnt_triggers);
                  stack_sort(*Ptriggers, DAG_cmp_q_stacks);
                }
            }
          else
            stack_free(qnt_triggers);
          stack_free(local_bound_vars);
          return;
        }
      /* Search for nested triggers only in nonground quantifiers */
      if (!ground(DAG))
        {
          stack_merge(local_bound_vars, previous_vars);
          stack_sort(local_bound_vars, DAG_cmp_q);
          qnt_triggers = compute_triggers_vars(DAG_arg_last(DAG), local_bound_vars);
          /* If found, done; don't set for deeper quantifiers */
          if (qnt_triggers)
            {
              stack_merge(*triggers, qnt_triggers);
              stack_free(qnt_triggers);
              stack_free(local_bound_vars);
              return;
            }
        }
      /* Search for deeper nested triggers */
      set_nested_triggers(DAG_arg_last(DAG), local_bound_vars, triggers);
      stack_free(local_bound_vars);
      return;
    }
  assert(top_symbol == CONNECTOR_OR || top_symbol == CONNECTOR_AND);
  for (i = 0; i < DAG_arity(DAG); ++i)
    set_nested_triggers(DAG_arg(DAG, i), previous_vars, triggers);
}

/*--------------------------------------------------------------*/

/**
    \author David Deharbe, Pascal Fontaine, Haniel Barbosa
    \brief inspects the whole formula, adds trigger to every quantified formula
    without triggers, and ensures the triggers are on the formula itself, not on
    the body
    \param src the formula
    \remark sets the DAG_PROP_TRIGGER property if triggers are found  */
void
set_triggers_old(TDAG DAG)
{
  unsigned i;
  Tstack_DAGstack triggers, *Ptriggers;
  if (!DAG_quant(DAG))
    return;
  if (DAG_symb_type(DAG_symb(DAG)) & SYMB_BOOLEAN_CONNECTOR)
    for (i = 0; i < DAG_arity(DAG); ++i)
      set_triggers_old(DAG_arg(DAG, i));
  if (!quantifier(DAG_symb(DAG)))
    return;
  Ptriggers = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
  if (!Ptriggers)
    {
      triggers = qnt_triggers(DAG);
      if (!triggers)
        return;
      DAG_prop_set(DAG, DAG_PROP_TRIGGER, &triggers);
    }
}

/*--------------------------------------------------------------*/

/**
   \author David Deharbe & Pascal Fontaine
   \brief inspects the whole formula, adds trigger to every quantified
   formula without triggers, and ensures the triggers are on the
   formula itself, not on the body
   \param src the formula */
static void
inst_add_triggers(TDAG src)
{
  unsigned i;
  Tstack_DAGstack *Pannot;

  if (!DAG_quant(src))
    return;
  if (DAG_symb_type(DAG_symb(src)) & SYMB_BOOLEAN_CONNECTOR)
    for (i = 0; i < DAG_arity(src); ++i)
      inst_add_triggers(DAG_arg(src, i));
  if (!quantifier(DAG_symb(src)))
    return;
  Pannot = DAG_prop_get(src, DAG_PROP_TRIGGER);
  if (!Pannot)
    {
      Tstack_DAGstack annot = qnt_triggers(src);
      if (!annot)
        return;
      DAG_prop_set(src, DAG_PROP_TRIGGER, &annot);
    }
}

/*--------------------------------------------------------------*/

void
inst_pre(TDAG src)
{
  inst_add_triggers(src);
}

/*
  --------------------------------------------------------------
  Normal forms
  --------------------------------------------------------------
*/

#define cnf_count ((unsigned **) DAG_tmp)
#define cnf_count_clauses(D) cnf_count[D][0]

/*--------------------------------------------------------------*/

static inline unsigned
cnf_count_DAGs(TDAG DAG)
{
  unsigned i, total = 0;
  assert(cnf_count[DAG] && cnf_count[DAG][0]);
  for (i = 1; i <= cnf_count[DAG][0]; ++i)
    total += cnf_count[DAG][i];
  return total;
}

/*--------------------------------------------------------------*/

void
DAG_tmp_reset_cnf_count(TDAG DAG)
{
  unsigned i;
  if (!cnf_count[DAG])
    return;
  free(cnf_count[DAG]);
  cnf_count[DAG] = NULL;
  for (i = 0; i < DAG_arity(DAG); ++i)
    DAG_tmp_reset_cnf_count(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

extern int ccfv_cnf_threshold;

static void
count_CNF_nodes(TDAG DAG)
{
  unsigned i, j, k1, k2, clauses, arg_clauses;
  Tsymb top_symbol = DAG_symb(DAG);
  assert(top_symbol != QUANTIFIER_FORALL);
  if (cnf_count[DAG])
    return;
  if (DAG_literal(DAG))
    {
      assert(!quantifier(top_symbol) || top_symbol == QUANTIFIER_EXISTS);
      MY_MALLOC(cnf_count[DAG], 2 * sizeof(unsigned));
      cnf_count_clauses(DAG) = 1;
      cnf_count[DAG][1] = 1;
      return;
    }
  if (top_symbol == CONNECTOR_AND)
    {
      clauses = 0;
      MY_MALLOC(cnf_count[DAG], sizeof(unsigned));
      for (i = 0; i < DAG_arity(DAG); ++i)
        {
          count_CNF_nodes(DAG_arg(DAG, i));
          if (!cnf_count_clauses(DAG_arg(DAG, i)))
            break;
          MY_REALLOC(cnf_count[DAG],
                     (clauses + cnf_count_clauses(DAG_arg(DAG, i)) + 1) *
                     sizeof(unsigned));
          for (j = 1; j <= cnf_count_clauses(DAG_arg(DAG, i)); ++j)
            cnf_count[DAG][++clauses] = cnf_count[DAG_arg(DAG, i)][j];
        }
      cnf_count_clauses(DAG) = clauses;
      /* Whether it exploded */
      if (i != DAG_arity(DAG) || cnf_count_DAGs(DAG) > ccfv_cnf_threshold)
        {
          cnf_count_clauses(DAG) = 0;
          return;
        }
#if DEBUG_INST_PRE > 2
      my_DAG_message("CNF count of %D: %d clauses, %d DAGs\n", DAG,
                     cnf_count_clauses(DAG), cnf_count_DAGs(DAG));
#endif
      return;
    }
  // OR
  assert(top_symbol == CONNECTOR_OR && DAG_arity(DAG));
  /* [TODO] Improve this so it does not go separately at 0 */
  clauses = 0;
  count_CNF_nodes(DAG_arg(DAG, 0));
  /* Whether it exploded */
  if (!cnf_count_clauses(DAG_arg(DAG, 0)))
    {
      MY_MALLOC(cnf_count[DAG], sizeof(unsigned));
      cnf_count_clauses(DAG) = 0;
      return;
    }
  MY_REALLOC(cnf_count[DAG],
             (cnf_count_clauses(DAG_arg(DAG, 0)) + 1) * sizeof(unsigned));
  cnf_count_clauses(DAG) = cnf_count_clauses(DAG_arg(DAG, 0));
  for (i = 1; i <= cnf_count_clauses(DAG_arg(DAG, 0)); ++i)
    cnf_count[DAG][++clauses] = cnf_count[DAG_arg(DAG, 0)][i];
  for (i = 1; i < DAG_arity(DAG); ++i)
    {
      count_CNF_nodes(DAG_arg(DAG, i));
      /* Whether it exploded */
      if (!cnf_count_clauses(DAG_arg(DAG, i)))
        break;
      arg_clauses = cnf_count_clauses(DAG_arg(DAG, i));
      k2 = clauses;
      clauses = clauses * arg_clauses;
      MY_REALLOC(cnf_count[DAG], (clauses + 1) * sizeof(unsigned));
      for (j = clauses; j > 0; )
        {
          for (k1 = 0; k1 < arg_clauses; ++k1)
            cnf_count[DAG][j - k1] =
              cnf_count[DAG_arg(DAG, i)][arg_clauses - k1] + cnf_count[DAG][k2];
          j -= k1;
          --k2;
        }
      cnf_count_clauses(DAG) = clauses;
      /* Whether it exploded */
      if (cnf_count_DAGs(DAG) > ccfv_cnf_threshold)
        break;
    }
  /* Whether it exploded */
  if (i != DAG_arity(DAG))
    {
      cnf_count_clauses(DAG) = 0;
      return;
    }
#if DEBUG_INST_PRE > 2
  my_DAG_message("CNF count of %D: %d clauses, %d DAGs\n", DAG,
                 cnf_count_clauses(DAG), cnf_count_DAGs(DAG));
#endif
}

/*--------------------------------------------------------------*/

#define QUANTIFIED_STRONG(DAG, pol) \
   ((DAG_symb(DAG) == QUANTIFIER_EXISTS && pol == POL_POS) || \
    (DAG_symb(DAG) == QUANTIFIER_FORALL && pol == POL_NEG))
#define QUANTIFIED_WEAK(DAG, pol) \
   ((DAG_symb(DAG) == QUANTIFIER_EXISTS && pol == POL_NEG) || \
    (DAG_symb(DAG) == QUANTIFIER_FORALL && pol == POL_POS))

/**
   \brief Traverses DAG applying the distributive law whenever necessary
   \param DAG a prenexed quantified formula in NNF
   \return Always return either a single literal of a conjunction of clauses
   \remark Naive (on purpose, though), exponential. Treats EXISTS as atom for now. */
#define cnf_of ((Tstack_DAGstack *) DAG_tmp)

/*--------------------------------------------------------------*/

void
DAG_tmp_reset_cnf(TDAG DAG)
{
  unsigned i;
  if (!cnf_of[DAG])
    return;
  stack_apply(cnf_of[DAG], stack_free);
  stack_free(cnf_of[DAG]);
  for (i = 0; i < DAG_arity(DAG); ++i)
    DAG_tmp_reset_cnf(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

static void
set_CNF_rec(TDAG DAG)
{
  unsigned i, j;
  Tstack_DAG old_clause, new_clause;
  Tstack_DAGstack clauses;
  Tsymb top_symbol = DAG_symb(DAG);
  assert(top_symbol != QUANTIFIER_FORALL);
  if (cnf_of[DAG])
    return;
  stack_INIT(cnf_of[DAG]);
  if (DAG_literal(DAG))
    {
      /* Put literal into a new clause */
      assert(!quantifier(top_symbol) || top_symbol == QUANTIFIER_EXISTS);
      stack_INIT(new_clause);
      stack_push(new_clause, DAG);
      stack_push(cnf_of[DAG], new_clause);
      return;
    }
  if (top_symbol == CONNECTOR_AND)
    {
      /* Put the CNF of each argument in a new clause */
      for (i = 0; i < DAG_arity(DAG); ++i)
        {
          set_CNF_rec(DAG_arg(DAG, i));
          for (j = 0; j < stack_size(cnf_of[DAG_arg(DAG, i)]); ++j)
            {
              stack_COPY(new_clause, stack_get(cnf_of[DAG_arg(DAG, i)], j));
              stack_push(cnf_of[DAG], new_clause);
            }
        }
#if DEBUG_INST_PRE > 1
      my_DAG_message("CNF of %D:\n", DAG);
      print_Tstack_DAGstack(cnf_of[DAG]);
#endif
      return;
    }
  // OR
  assert(top_symbol == CONNECTOR_OR && DAG_arity(DAG));
  /* [TODO] Improve this so it does not go separately at 0 */
  set_CNF_rec(DAG_arg(DAG, 0));
  for (i = 0; i < stack_size(cnf_of[DAG_arg(DAG, 0)]); ++i)
    {
      stack_COPY(new_clause, stack_get(cnf_of[DAG_arg(DAG, 0)], i));
      stack_push(cnf_of[DAG], new_clause);
    }
  for (i = 1; i < DAG_arity(DAG); ++i)
    {
      /* For each disjunct, compute its CNF. Then combine each of its clauses with every clause from the previous disjuncts */
      set_CNF_rec(DAG_arg(DAG, i));
      stack_INIT(clauses);
      while (!stack_is_empty(cnf_of[DAG]))
        {
          old_clause = stack_pop(cnf_of[DAG]);
          for (j = 0; j < stack_size(cnf_of[DAG_arg(DAG, i)]); ++j)
            {
              stack_COPY(new_clause, old_clause);
              stack_merge(new_clause, stack_get(cnf_of[DAG_arg(DAG, i)], j));
              stack_push(clauses, new_clause);
            }
          stack_free(old_clause);
        }
      stack_free(cnf_of[DAG]);
      stack_COPY(cnf_of[DAG], clauses);
      stack_free(clauses);
    }
#if DEBUG_INST_PRE > 1
  my_DAG_message("CNF of %D:\n", DAG);
  print_Tstack_DAGstack(cnf_of[DAG]);
#endif
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief removes all nested occurrences of universal quantifiers while
    accumulating the respective bounded variables
    \param DAG a formula
    \param all_vars all bound variables accumulated so far
    \param ubound_vars all universally bound variables accumulated so far
    \return a DAG without universals
    \remark not destructive to parameters, however all prenexed DAGs created
    during the process that are not necessary ultimately (the temporary
    "and/or") are destructed
    \remark does variable renaming to avoid capture (same variable under the
    scope of two quantifiers) */
static unsigned
prenex_rec(TDAG DAG, Tstack_DAG * ubound_vars)
{
  unsigned i, res = 0;
  TDAG tmp_DAG;
  Tstack_DAG DAGs;
  Tsymb top_symbol = DAG_symb(DAG);
  if (DAG_tmp_DAG[DAG])
    return DAG_tmp_DAG[DAG] != DAG;
  if (!DAG_quant(DAG) || (DAG_literal(DAG) && top_symbol != QUANTIFIER_FORALL))
    {
      DAG_tmp_DAG[DAG] = DAG;
      return 0;
    }
  if (top_symbol == QUANTIFIER_FORALL)
    {
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        stack_push(*ubound_vars, DAG_arg(DAG, i));
      prenex_rec(DAG_arg_last(DAG), ubound_vars);
      DAG_tmp_DAG[DAG] = DAG_tmp_DAG[DAG_arg_last(DAG)];
      return 1;
    }
  assert(top_symbol == CONNECTOR_OR || top_symbol == CONNECTOR_AND);
  for (i = 0; i < DAG_arity(DAG); ++i)
    res |= prenex_rec(DAG_arg(DAG, i), ubound_vars);
  if (res)
    {
      stack_INIT(DAGs);
      for (i = 0; i < DAG_arity(DAG); ++i)
        stack_push(DAGs, DAG_tmp_DAG[DAG_arg(DAG, i)]);
      tmp_DAG = DAG_new_stack(top_symbol, DAGs);
      stack_free(DAGs);
      DAG_tmp_DAG[DAG] = tmp_DAG;
      return 1;
    }
  DAG_tmp_DAG[DAG] = DAG;
  return 0;
}

/*--------------------------------------------------------------*/

TDAG
prenex(TDAG DAG)
{
  TDAG body_DAG;
  Tstack_DAG DAGs;
  assert(DAG_symb(DAG) == QUANTIFIER_FORALL);
  stack_INIT(DAGs);
  /* Prenex universal quantifiers in DAG */
  DAG_tmp_reserve();
  prenex_rec(DAG, &DAGs);
  body_DAG = DAG_tmp_DAG[DAG_arg_last(DAG)];
  DAG_tmp_reset_DAG(DAG);
  if (body_DAG != DAG_arg_last(DAG))
    {
      stack_push(DAGs, body_DAG);
      DAG = DAG_new_stack(QUANTIFIER_FORALL, DAGs);
    }
  DAG_tmp_release();
  stack_free(DAGs);
  return DAG;
}

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief resets DAG_tmp_DAG of all subDAGs execept if they are variables among
    the given set
    \param DAG a DAG
    \param vars a set of variables */
void
DAG_tmp_reset_DAG_except_vars(TDAG DAG, Tstack_DAG vars)
{
  unsigned i;
  if (!DAG_tmp_DAG[DAG])
    return;
  if (DAG_arity(DAG) || !vars || !stack_DAG_contains(vars, DAG))
    DAG_tmp_DAG[DAG] = DAG_NULL;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_reset_DAG_except_vars(DAG_arg(DAG, i), vars);
}

/*--------------------------------------------------------------*/

unsigned
qnt_uniq_vars_rec(TDAG DAG, Tstack_DAG * bound_vars)
{
  unsigned i, j, res = 0;
  Tsymb top_symbol = DAG_symb(DAG);
  TDAG tmp_DAG, var, new_var = 0;
  Tstack_DAG DAGs, trigger, previous_vars = NULL;
  Tstack_DAGstack * Ptriggers, triggers;
  if (DAG_tmp_DAG[DAG])
    return DAG_tmp_DAG[DAG] != DAG;
  if (quantifier(top_symbol))
    {
      if (stack_size(*bound_vars))
        stack_COPY(previous_vars, *bound_vars);
      stack_INIT(DAGs);
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        {
          var = DAG_arg(DAG, i);
          if (stack_DAG_contains(*bound_vars, var))
            {
              /* [TODO] DAG_dup new variables, later free them */
              new_var = DAG_new_nullary(DAG_symb_variable(DAG_sort(var)));
              DAG_tmp_DAG[var] = new_var;
              var = new_var;
            }
          else
            stack_push(*bound_vars, var);
          stack_push(DAGs, var);
        }
      stack_sort(*bound_vars, DAG_cmp_q);
      res = qnt_uniq_vars_rec(DAG_arg_last(DAG), bound_vars) || new_var;
      if (res)
        {
          stack_push(DAGs, DAG_tmp_DAG[DAG_arg_last(DAG)]);
          tmp_DAG = DAG_new_stack(top_symbol, DAGs);
          DAG_tmp_DAG[DAG] = tmp_DAG;
          Ptriggers = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
          if (Ptriggers)
            {
              /* Need to rename variables in each DAG in triggers */
              if (new_var)
                {
                  /* [TODO] Make sure this is correct */
                  stack_INIT(triggers);
                  for (i = 0; i < stack_size(*Ptriggers); ++i)
                    {
                      trigger = stack_get(*Ptriggers, i);
                      stack_inc(triggers);
                      stack_INIT(stack_top(triggers));
                      for (j = 0; j < stack_size(trigger); ++j)
                        {
                          DAG_tmp_subst(stack_get(trigger, j));
                          stack_push(stack_top(triggers),
                                     DAG_dup(DAG_tmp_DAG[stack_get(trigger, j)]));
                        }
                    }
                }
              else
                triggers = copy_triggers(*Ptriggers);
              DAG_prop_set(tmp_DAG, DAG_PROP_TRIGGER, &triggers);
            }
        }
      else
        DAG_tmp_DAG[DAG] = DAG;
      /* Since an equal subDAG may appear under another quantifier */
      if (previous_vars)
        {
          DAG_tmp_reset_DAG_except_vars(DAG_arg_last(DAG), previous_vars);
          stack_free(previous_vars);
        }
      else
        {
          DAG_tmp_reset_DAG(DAG_arg_last(DAG));
          stack_apply(*bound_vars, DAG_tmp_reset_DAG);
          stack_reset(*bound_vars);
        }
      stack_free(DAGs);
      return res;
    }
  for (i = 0; i < DAG_arity(DAG); i++)
    res |= qnt_uniq_vars_rec(DAG_arg(DAG, i), bound_vars);
  if (res)
    {
      stack_INIT(DAGs);
      /* Some subformulas of quantifiers may appear outside quantifiers, so
         their DAG_tmp would have been reset */
      for (i = 0; i < DAG_arity(DAG); i++)
        if (DAG_tmp_DAG[DAG_arg(DAG, i)])
          stack_push(DAGs, DAG_tmp_DAG[DAG_arg(DAG, i)]);
        else
          stack_push(DAGs, DAG_arg(DAG, i));
      tmp_DAG = DAG_new_stack(top_symbol, DAGs);
      stack_free(DAGs);
      DAG_tmp_DAG[DAG] = tmp_DAG;
      return 1;
    }
  DAG_tmp_DAG[DAG] = DAG;
  return 0;
}

/*--------------------------------------------------------------*/

TDAG
qnt_uniq_vars(TDAG DAG)
{
  TDAG result;
  Tstack_DAG DAGs;
  stack_INIT(DAGs);
  DAG_tmp_reserve();
  qnt_uniq_vars_rec(DAG, &DAGs);
  result = DAG_dup(DAG_tmp_DAG[DAG]);
  stack_apply(DAGs, DAG_tmp_reset_DAG);
  DAG_tmp_reset_DAG(DAG);
  DAG_tmp_release();
  stack_free(DAGs);
  return result;
}

/*--------------------------------------------------------------*/

TDAG
NNF(TDAG DAG, bool pol)
{
  unsigned i, j;
  TDAG nnf_DAG, tmp_NNF;
  Tstack_DAG DAGs;
  Tsymb nnf_symbol, top_symbol = DAG_symb(DAG);
  if (top_symbol == CONNECTOR_NOT)
    return NNF(DAG_arg0(DAG), !pol);
  if (top_symbol == CONNECTOR_AND || top_symbol == CONNECTOR_OR)
    {
      nnf_symbol = pol? top_symbol :
        (top_symbol == CONNECTOR_OR? CONNECTOR_AND : CONNECTOR_OR);
      stack_INIT(DAGs);
      for (i = 0; i < DAG_arity(DAG); ++i)
        {
          tmp_NNF = NNF(DAG_arg(DAG, i), pol);
          if (DAG_symb(tmp_NNF) == nnf_symbol)
            {
              for (j = 0; j < DAG_arity(tmp_NNF); ++j)
                stack_push(DAGs, DAG_dup(DAG_arg(tmp_NNF, j)));
              DAG_free(DAG_dup(tmp_NNF));
            }
          else
            stack_push(DAGs, DAG_dup(tmp_NNF));
        }
      nnf_DAG = DAG_new_stack(nnf_symbol, DAGs);
      stack_apply(DAGs, DAG_free);
      stack_free(DAGs);
      return nnf_DAG;
    }
  if (top_symbol == CONNECTOR_IMPLIES)
    {
      if (pol)
        return DAG_or2(NNF(DAG_arg0(DAG), 0),
                       NNF(DAG_arg1(DAG), 1));
      return DAG_and2(NNF(DAG_arg0(DAG), 1),
                      NNF(DAG_arg1(DAG), 0));
    }
  if (top_symbol == CONNECTOR_EQUIV)
    {
      if (pol)
        return DAG_and2(DAG_or2(NNF(DAG_arg0(DAG), 0),
                                NNF(DAG_arg1(DAG), 1)),
                        DAG_or2(NNF(DAG_arg1(DAG), 0),
                                NNF(DAG_arg0(DAG), 1)));
      return DAG_or2(DAG_and2(NNF(DAG_arg0(DAG), 1),
                              NNF(DAG_arg1(DAG), 0)),
                     DAG_and2(NNF(DAG_arg1(DAG), 1),
                              NNF(DAG_arg0(DAG), 0)));
      /* [TODO] test if this is OK */
      /* return DAG_and2(DAG_or2(NNF(DAG_arg0(DAG), 1), */
      /*                         NNF(DAG_arg1(DAG), 1)), */
      /*                DAG_or2(NNF(DAG_arg0(DAG), 0), */
      /*                         NNF(DAG_arg1(DAG), 0))); */
    }
  if (top_symbol == CONNECTOR_ITE)
    {
      if (pol)
        return DAG_and2(DAG_or2(NNF(DAG_arg(DAG, 0), 0),
                                NNF(DAG_arg(DAG, 1), 1)),
                        DAG_or2(NNF(DAG_arg(DAG, 0), 1),
                                NNF(DAG_arg(DAG, 2), 1)));
      return DAG_or2(DAG_and2(NNF(DAG_arg(DAG, 0), 1),
                              NNF(DAG_arg(DAG, 1), 0)),
                     DAG_and2(NNF(DAG_arg(DAG, 0), 0),
                              NNF(DAG_arg(DAG, 2), 0)));
    }
  if (quantifier(top_symbol))
    {
      stack_INIT(DAGs);
      nnf_symbol = pol? top_symbol :
        (top_symbol == QUANTIFIER_FORALL? QUANTIFIER_EXISTS
         : QUANTIFIER_FORALL);
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        stack_push(DAGs, DAG_arg(DAG, i));
      stack_push(DAGs, NNF(DAG_arg_last(DAG), pol));
      nnf_DAG = DAG_new_stack(nnf_symbol, DAGs);
      stack_free(DAGs);
      return nnf_DAG;
    }
  if (DAG_literal(DAG))
    return pol? DAG : DAG_neg(DAG);
  my_DAG_error("NNF: Symbol %s is not supported.\n", DAG_symb_name2(top_symbol));
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

static unsigned
qnt_connectives_rec(TDAG DAG, bool in_qnt_body)
{
  unsigned i, res = 0;
  Tsymb top_symbol = DAG_symb(DAG);
  TDAG tmp_DAG, tmp_arg0, tmp_arg1, tmp_arg2;
  Tstack_DAG DAGs;
  Tstack_DAGstack * Ptriggers, triggers;
  if (DAG_tmp_DAG[DAG])
    return DAG_tmp_DAG[DAG] != DAG;
  if (quantifier(top_symbol))
    {
      res = qnt_connectives_rec(DAG_arg_last(DAG), true);
      if (res)
        {
          /* [TODO] Use directly *PDAG */
          stack_INIT(DAGs);
          for (i = 0; i < DAG_arity(DAG) - 1; ++i)
            stack_push(DAGs, DAG_arg(DAG, i));
          stack_push(DAGs, DAG_tmp_DAG[DAG_arg_last(DAG)]);
          tmp_DAG = DAG_new_stack(top_symbol, DAGs);
          stack_free(DAGs);
          Ptriggers = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
          if (Ptriggers)
            {
              triggers = copy_triggers(*Ptriggers);
              DAG_prop_set(tmp_DAG, DAG_PROP_TRIGGER, &triggers);
            }
          DAG_tmp_DAG[DAG] = tmp_DAG;
          return 1;
        }
      DAG_tmp_DAG[DAG] = DAG;
      return 0;
    }
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      res = qnt_connectives_rec(DAG_arg0(DAG), in_qnt_body);
      if (res)
        {
          tmp_DAG = DAG_not(DAG_tmp_DAG[DAG_arg0(DAG)]);
          DAG_tmp_DAG[DAG] = tmp_DAG;
          return 1;
        }
      DAG_tmp_DAG[DAG] = DAG;
      return 0;
    }
  if (DAG_literal(DAG) || (!in_qnt_body && !DAG_quant(DAG)))
    {
      DAG_tmp_DAG[DAG] = DAG;
      return 0;
    }
  if (in_qnt_body && DAG_symb(DAG) == CONNECTOR_IMPLIES)
    {
      qnt_connectives_rec(DAG_arg0(DAG), in_qnt_body);
      qnt_connectives_rec(DAG_arg1(DAG), in_qnt_body);
      /* [TODO] is this necessary? I'm just scared */
      tmp_arg0 = DAG_tmp_DAG[DAG_arg0(DAG)];
      tmp_arg1 = DAG_tmp_DAG[DAG_arg1(DAG)];
      tmp_DAG = DAG_or2(DAG_not(tmp_arg0), tmp_arg1);
      DAG_tmp_DAG[DAG] = tmp_DAG;
      return 1;
    }
  if (in_qnt_body && DAG_symb(DAG) == CONNECTOR_EQUIV)
    {
      qnt_connectives_rec(DAG_arg0(DAG), in_qnt_body);
      qnt_connectives_rec(DAG_arg1(DAG), in_qnt_body);
      tmp_arg0 = DAG_tmp_DAG[DAG_arg0(DAG)];
      tmp_arg1 = DAG_tmp_DAG[DAG_arg1(DAG)];
      tmp_DAG = DAG_and2(DAG_or2(DAG_not(tmp_arg0), tmp_arg1),
                         DAG_or2(DAG_not(tmp_arg1), tmp_arg0));
      DAG_tmp_DAG[DAG] = tmp_DAG;
      return 1;
    }
  if (in_qnt_body && DAG_symb(DAG) == CONNECTOR_ITE)
    {
      qnt_connectives_rec(DAG_arg(DAG, 0), in_qnt_body);
      qnt_connectives_rec(DAG_arg(DAG, 1), in_qnt_body);
      qnt_connectives_rec(DAG_arg(DAG, 2), in_qnt_body);
      tmp_arg0 = DAG_tmp_DAG[DAG_arg(DAG, 0)];
      tmp_arg1 = DAG_tmp_DAG[DAG_arg(DAG, 1)];
      tmp_arg2 = DAG_tmp_DAG[DAG_arg(DAG, 2)];
      tmp_DAG = DAG_and2(DAG_or2(DAG_not(tmp_arg0), tmp_arg1),
                         DAG_or2(tmp_arg0, tmp_arg2));
      DAG_tmp_DAG[DAG] = tmp_DAG;
      return 1;
    }
  for (i = 0; i < DAG_arity(DAG); i++)
    res |= qnt_connectives_rec(DAG_arg(DAG, i), in_qnt_body);
  if (res)
    {
      stack_INIT(DAGs);
#ifdef DEBUG
      for (i = 0; i < DAG_arity(DAG); i++)
        assert(DAG_tmp_DAG[DAG_arg(DAG, i)]);
#endif
      for (i = 0; i < DAG_arity(DAG); i++)
        stack_push(DAGs, DAG_tmp_DAG[DAG_arg(DAG, i)]);
      tmp_DAG = DAG_new_stack(top_symbol, DAGs);
      stack_free(DAGs);
      DAG_tmp_DAG[DAG] = tmp_DAG;
      return 1;
    }
  DAG_tmp_DAG[DAG] = DAG;
  return 0;
}

/*--------------------------------------------------------------*/

TDAG
qnt_connectives(TDAG DAG)
{
  TDAG result;
  DAG_tmp_reserve();
  qnt_connectives_rec(DAG, false);
  result = DAG_dup(DAG_tmp_DAG[DAG]);
  DAG_tmp_reset_DAG(DAG);
  DAG_tmp_release();
  return result;
}

/*--------------------------------------------------------------*/

typedef struct TDAG_pol
{
  TDAG pol[2];
} * TDAG_pol;

#define DAG_tmp_DAG_pol ((TDAG_pol *) DAG_tmp)

#define DAG_for_pol(A, p)                       \
  (p == POL_NEG? DAG_tmp_DAG_pol[A]->pol[0] :   \
   DAG_tmp_DAG_pol[A]->pol[1])

#define get_DAG(A, p)                           \
  ((DAG_tmp_DAG_pol[A] && DAG_for_pol(A, p)) ?  \
   DAG_for_pol(A, p) : A)


#define set_DAG_pol(A, pol, B)                          \
  if (!DAG_tmp_DAG_pol[A])                              \
    {                                                   \
      MY_MALLOC(DAG_tmp_DAG_pol[A], 2 * sizeof(TDAG));  \
      DAG_tmp_DAG_pol[A]->pol[0] = DAG_NULL;            \
      DAG_tmp_DAG_pol[A]->pol[1] = DAG_NULL;            \
    }                                                   \
  assert(pol == POL_NEG || pol == POL_POS);             \
  if (pol == POL_NEG)                                   \
    DAG_tmp_DAG_pol[A]->pol[0] = B;                     \
  else                                                  \
    DAG_tmp_DAG_pol[A]->pol[1] = B;                     \


/*--------------------------------------------------------------*/

static void
DAG_tmp_reset_DAG_pol(TDAG DAG)
{
  unsigned i;
  if (!DAG_tmp_DAG_pol[DAG])
    return;
  if (DAG_tmp_DAG_pol[DAG]->pol[0])
    DAG_free(DAG_tmp_DAG_pol[DAG]->pol[0]);
  if (DAG_tmp_DAG_pol[DAG]->pol[1])
    DAG_free(DAG_tmp_DAG_pol[DAG]->pol[1]);
  free(DAG_tmp_DAG_pol[DAG]);
  DAG_tmp_DAG_pol[DAG] = NULL;
  for (i = 0; i < DAG_arity(DAG); ++i)
    DAG_tmp_reset_DAG_pol(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

static unsigned
NNF_new(TDAG DAG, Tpol pol)
{
  unsigned i, res = 0;
  TDAG dest;
  Tstack_DAG DAGs;
  Tsymb nnf_symbol;
  Tstack_DAGstack * Ptriggers, triggers;
  if (DAG_tmp_DAG_pol[DAG] && DAG_for_pol(DAG, pol))
    return DAG_for_pol(DAG, pol) != DAG;
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      /* Always push it down */
      NNF_new(DAG_arg0(DAG), INV_POL(pol));
      dest = DAG_dup(DAG_for_pol(DAG_arg0(DAG), INV_POL(pol)));
      set_DAG_pol(DAG, pol, dest);
      return 1;
    }
  if (DAG_symb(DAG) == CONNECTOR_AND || DAG_symb(DAG) == CONNECTOR_OR)
    {
      nnf_symbol = (pol == POL_POS) ? DAG_symb(DAG) :
        (DAG_symb(DAG) == CONNECTOR_OR? CONNECTOR_AND : CONNECTOR_OR);
      res = nnf_symbol != DAG_symb(DAG);
      for (i = 0; i < DAG_arity(DAG); ++i)
        res |= NNF_new(DAG_arg(DAG, i), pol);
      if (res)
        {
          stack_INIT(DAGs);
          for (i = 0; i < DAG_arity(DAG); ++i)
            stack_push(DAGs, DAG_for_pol(DAG_arg(DAG, i), pol));
          dest = DAG_dup(DAG_new_stack(nnf_symbol, DAGs));
          stack_free(DAGs);
          set_DAG_pol(DAG, pol, dest);
          return 1;
        }
      set_DAG_pol(DAG, pol, DAG_dup(DAG));
      return 0;
    }
  if (quantifier(DAG_symb(DAG)))
    {
      nnf_symbol = (pol == POL_POS)? DAG_symb(DAG) :
        (DAG_symb(DAG) == QUANTIFIER_FORALL? QUANTIFIER_EXISTS :
         QUANTIFIER_FORALL);
      res = NNF_new(DAG_arg_last(DAG), pol) || nnf_symbol != DAG_symb(DAG);
      if (res)
        {
          stack_INIT(DAGs);
          for (i = 0; i < DAG_arity(DAG) - 1; ++i)
            stack_push(DAGs, DAG_arg(DAG, i));
          stack_push(DAGs, DAG_for_pol(DAG_arg_last(DAG), pol));
          dest = DAG_dup(DAG_new_stack(nnf_symbol, DAGs));
          stack_free(DAGs);
          set_DAG_pol(DAG, pol, dest);
          Ptriggers = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
          if (Ptriggers)
            {
              triggers = copy_triggers(*Ptriggers);
              DAG_prop_set(dest, DAG_PROP_TRIGGER, &triggers);
            }
          return 1;
        }
      set_DAG_pol(DAG, pol, DAG_dup(DAG));
      return 0;
    }
  assert(DAG_literal(DAG));
  if (pol == POL_NEG)
    {
      dest = DAG_dup(DAG_neg(DAG));
      set_DAG_pol(DAG, pol, dest);
      return 1;
    }
  set_DAG_pol(DAG, pol, DAG_dup(DAG));
  return 0;
}

/*--------------------------------------------------------------*/

static unsigned
qnt_NNF_rec(TDAG DAG, Tpol pol)
{
  unsigned i, res = 0;
  bool weak_existential;
  Tpol qnt_pol;
  TDAG dest;
  Tstack_DAG DAGs;
  Tstack_DAGstack * Ptriggers, triggers;
  if (!DAG_quant(DAG) ||
      (DAG_literal(DAG) && !DAG_quant(DAG) && !quantifier(DAG_symb(DAG))))
    return 0;
  assert(pol != POL_NONE && pol != POL_BOTH);
  if (DAG_tmp_DAG_pol[DAG] && DAG_for_pol(DAG, pol))
    return DAG_for_pol(DAG, pol) != DAG;
  if (DAG_symb(DAG) == CONNECTOR_ITE)
    {
      res = qnt_NNF_rec(DAG_arg(DAG, 0), POL_BOTH) |
        qnt_NNF_rec(DAG_arg(DAG, 1), pol) |
        qnt_NNF_rec(DAG_arg(DAG, 2), pol);
      if (res)
        {
          /* [TODO] The first guy may have both polaties, so what about it??? */
          dest = DAG_dup(DAG_ite(get_DAG(DAG_arg(DAG, 0), pol),
                                 get_DAG(DAG_arg(DAG, 1), pol),
                                 get_DAG(DAG_arg(DAG, 2), pol)));
          set_DAG_pol(DAG, pol, dest);
          return 1;
        }
      set_DAG_pol(DAG, pol, DAG_dup(DAG));
      return 0;
    }
  if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    {
      res = qnt_NNF_rec(DAG_arg0(DAG), INV_POL(pol)) |
        qnt_NNF_rec(DAG_arg1(DAG), pol);
      if (res)
        {
          dest = DAG_dup(DAG_implies(get_DAG(DAG_arg0(DAG), INV_POL(pol)),
                                     get_DAG(DAG_arg1(DAG), pol)));
          set_DAG_pol(DAG, pol, dest);
          return 1;
        }
      set_DAG_pol(DAG, pol, DAG_dup(DAG));
      return 0;
    }
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      res = qnt_NNF_rec(DAG_arg0(DAG), INV_POL(pol));
      if (res)
        {
          dest = DAG_dup(DAG_not(get_DAG(DAG_arg0(DAG), INV_POL(pol))));
          set_DAG_pol(DAG, pol, dest);
          return 1;
        }
      set_DAG_pol(DAG, pol, DAG_dup(DAG));
      return 0;
    }
  assert(DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_symb(DAG) != CONNECTOR_XOR);
  if (boolean_connector(DAG_symb(DAG)))
    {
      for (i = 0; i < DAG_arity(DAG); ++i)
        res |= qnt_NNF_rec(DAG_arg(DAG, i), pol);
      if (res)
        {
          stack_INIT(DAGs);
          for (i = 0; i < DAG_arity(DAG); ++i)
            stack_push(DAGs, get_DAG(DAG_arg(DAG, i), pol));
          dest = DAG_dup(DAG_new_stack(DAG_symb(DAG), DAGs));
          stack_free(DAGs);
          set_DAG_pol(DAG, pol, dest);
          return 1;
        }
      set_DAG_pol(DAG, pol, DAG_dup(DAG));
      return 0;
    }
  if (quantifier(DAG_symb(DAG)))
    {
      /* Those will have been skolemized */
      assert(!QUANTIFIED_STRONG(DAG, pol));
      weak_existential = DAG_symb(DAG) == QUANTIFIER_EXISTS;
      qnt_pol = weak_existential? POL_NEG : POL_POS;
      res = NNF_new(DAG_arg_last(DAG), qnt_pol);
      assert(!weak_existential || res);
      if (res)
        {
          assert(DAG_tmp_DAG_pol[DAG_arg_last(DAG)] &&
                 DAG_for_pol(DAG_arg_last(DAG), qnt_pol));
          stack_INIT(DAGs);
          for (i = 0; i < DAG_arity(DAG) - 1; ++i)
            stack_push(DAGs, DAG_arg(DAG, i));
          stack_push(DAGs, DAG_for_pol(DAG_arg_last(DAG), qnt_pol));
          /* Turn weak existential into strong universal (which, given the
             negative polarity, is effectively a weak universal) */
          dest = weak_existential?
            DAG_dup(DAG_not(DAG_new_stack(QUANTIFIER_FORALL, DAGs))) :
            DAG_dup(DAG_new_stack(DAG_symb(DAG), DAGs));
          stack_free(DAGs);
          /* DAG_tmp_reset_DAG_pol(DAG_arg_last(DAG)); */
          set_DAG_pol(DAG, pol, dest);
          Ptriggers = DAG_prop_get(DAG, DAG_PROP_TRIGGER);
          if (Ptriggers)
            {
              triggers = copy_triggers(*Ptriggers);
              DAG_prop_set(dest, DAG_PROP_TRIGGER, &triggers);
            }
          return 1;
        }
      set_DAG_pol(DAG, pol, DAG_dup(DAG));
      return 0;
    }
  my_error ("qnt_NNF_rec: unable to NNF quantifier\n");
  return 0;
}

/*--------------------------------------------------------------*/

static TDAG
NNF_tree(TDAG DAG, Tpol pol)
{
  unsigned i;
  TDAG dest;
  Tstack_DAG DAGs;
  Tsymb nnf_symbol;
  /* Always push it down */
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    return NNF_tree(DAG_arg0(DAG), INV_POL(pol));
  if (DAG_symb(DAG) == CONNECTOR_AND || DAG_symb(DAG) == CONNECTOR_OR)
    {
      nnf_symbol = (pol == POL_POS) ? DAG_symb(DAG) :
        (DAG_symb(DAG) == CONNECTOR_OR? CONNECTOR_AND : CONNECTOR_OR);

      stack_INIT(DAGs);
      for (i = 0; i < DAG_arity(DAG); ++i)
        stack_push(DAGs, NNF_tree(DAG_arg(DAG, i), pol));
      dest = DAG_new_stack(nnf_symbol, DAGs);
      stack_free(DAGs);
      return dest;
    }
  if (quantifier(DAG_symb(DAG)))
    {
      nnf_symbol = (pol == POL_POS)? DAG_symb(DAG) :
        (DAG_symb(DAG) == QUANTIFIER_FORALL? QUANTIFIER_EXISTS :
         QUANTIFIER_FORALL);
      stack_INIT(DAGs);
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        stack_push(DAGs, DAG_arg(DAG, i));
      stack_push(DAGs, NNF_new(DAG_arg_last(DAG), pol));
      dest = DAG_new_stack(nnf_symbol, DAGs);
      stack_free(DAGs);
      return dest;
    }
  assert(DAG_literal(DAG));
  if (pol == POL_NEG)
    return DAG_neg(DAG);
  return DAG;
}

/*--------------------------------------------------------------*/

static TDAG
qnt_NNF_tree(TDAG DAG, Tpol pol)
{
  unsigned i;
  bool weak_existential;
  Tpol qnt_pol;
  TDAG dest;
  Tstack_DAG DAGs;
  if (!DAG_quant(DAG) ||
      (DAG_literal(DAG) && DAG_symb(DAG) != QUANTIFIER_FORALL))
    return DAG;
  assert(pol != POL_NONE && pol != POL_BOTH);
  if (DAG_symb(DAG) == CONNECTOR_ITE)
    {
      /* [TODO] The first guy may have both polaties, so what about it??? */
      dest = DAG_ite(qnt_NNF_tree(DAG_arg(DAG, 0), POL_BOTH),
                     qnt_NNF_tree(DAG_arg(DAG, 1), pol),
                     qnt_NNF_tree(DAG_arg(DAG, 2), pol));
      return dest;
    }
  if (DAG_symb(DAG) == CONNECTOR_IMPLIES)
    {
      dest = DAG_implies(qnt_NNF_tree(DAG_arg0(DAG), INV_POL(pol)),
                         qnt_NNF_tree(DAG_arg1(DAG), pol));
      return dest;
    }
  if (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      dest = DAG_not(qnt_NNF_tree(DAG_arg0(DAG), INV_POL(pol)));
      return dest;
    }
  assert(DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_symb(DAG) != CONNECTOR_XOR);
  if (boolean_connector(DAG_symb(DAG)))
    {
      stack_INIT(DAGs);
      for (i = 0; i < DAG_arity(DAG); ++i)
        stack_push(DAGs, qnt_NNF_tree(DAG_arg(DAG, i), pol));
      dest = DAG_new_stack(DAG_symb(DAG), DAGs);
      stack_free(DAGs);
      return dest;
    }
  if (quantifier(DAG_symb(DAG)))
    {
      /* Those will have been skolemized */
      assert(!QUANTIFIED_STRONG(DAG, pol));
      weak_existential = DAG_symb(DAG) == QUANTIFIER_EXISTS;
      qnt_pol = weak_existential? POL_NEG : POL_POS;

      stack_INIT(DAGs);
      for (i = 0; i < DAG_arity(DAG) - 1; ++i)
        stack_push(DAGs, DAG_arg(DAG, i));
      stack_push(DAGs, NNF_tree(DAG_arg_last(DAG), qnt_pol));
      /* Turn weak existential into strong universal (which, given the
         negative polarity, is effectively a weak universal) */
      dest = weak_existential?
        DAG_not(DAG_new_stack(QUANTIFIER_FORALL, DAGs)) :
        DAG_new_stack(DAG_symb(DAG), DAGs);
      stack_free(DAGs);
      return dest;
    }
  my_error ("qnt_NNF_tree: unable to NNF quantifier\n");
  return DAG_NULL;
}

/*--------------------------------------------------------------*/

TDAG
qnt_NNF(TDAG src)
{
  TDAG dest;
  /* dest = DAG_dup(qnt_NNF_tree(src, POL_POS)); */
  DAG_tmp_reserve();
  qnt_NNF_rec(src, POL_POS);
  dest = DAG_dup(get_DAG(src, POL_POS));
  DAG_tmp_reset_DAG_pol(src);
  DAG_tmp_release();
  return dest;
}

                                               /*--------------------------------------------------------------*/

TDAG
qnt_NF(TDAG src)
{
  TDAG dest;
  /* Remove conectives besides AND/OR/NOT from scope of quantifiers */
  dest = qnt_connectives(src);
  DAG_free(src);
  src = dest;
  /* Put quantified formulas in NNF, remove weak existentials */
  dest = qnt_NNF(src);
  DAG_free(src);
  src = dest;
  /* Rename variables so that none appear in more than one quantifier */
  dest = qnt_uniq_vars(src);
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

void
set_NFs(TDAG DAG)
{
  unsigned i, j;
  bool cnf_explosion;
  TDAG tmp_DAG, prenex_DAG;
  Tstack_DAG tmp;
  Tstack_DAGstack cnf;
  if (!enable_nnf_simp)
    {
      tmp_DAG = DAG_dup(NNF(DAG, true));
      prenex_DAG = DAG_dup(prenex(tmp_DAG));
      DAG_free(tmp_DAG);
    }
  else
    prenex_DAG = DAG_dup(prenex(DAG));
  /* Computes a set of sets representing CNF of given DAG */
  DAG_tmp_reserve();
  count_CNF_nodes(DAG_arg_last(prenex_DAG));
  /* Whether it exploded */
  cnf_explosion = !cnf_count[DAG_arg_last(prenex_DAG)] || !cnf_count_clauses(DAG_arg_last(prenex_DAG));
  DAG_tmp_reset_cnf_count(DAG_arg_last(prenex_DAG));
  DAG_tmp_release();
  if (cnf_explosion)
    {
      DAG_free(prenex_DAG);
      return;
    }
  DAG_tmp_reserve();
  set_CNF_rec(DAG_arg_last(prenex_DAG));
  stack_INIT(cnf);
  for (i = 0; i < stack_size(cnf_of[DAG_arg_last(prenex_DAG)]); ++i)
    {
      stack_COPY(tmp, stack_get(cnf_of[DAG_arg_last(prenex_DAG)], i));
      stack_apply(tmp, DAG_dup);
      stack_push(cnf, tmp);
    }
  DAG_prop_set(DAG, DAG_PROP_CNF, &cnf);
  DAG_tmp_reset_cnf(DAG_arg_last(prenex_DAG));
  DAG_tmp_release();
  /* [TODO] only one DAG_tmp for all... have a set_fvars_array/stack? */
  /* Sets bound variables of all DAGs in CNF */
  for (i = 0; i < stack_size(cnf); ++i)
    for (j = 0; j < stack_size(stack_get(cnf, i)); ++j)
      set_fvars(stack_get(stack_get(cnf, i), j));
  DAG_free(prenex_DAG);
}

/*--------------------------------------------------------------*/
