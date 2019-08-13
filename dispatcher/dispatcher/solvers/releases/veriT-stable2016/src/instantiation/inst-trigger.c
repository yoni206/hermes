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

#include "limits.h"
#include "options.h"
#include "statistics.h"

#include "DAG.h"
#include "DAG-ptr.h"
#include "DAG-print.h"

#include "congruence.h"
#include "unify.h"
#include "inst-index.h"
#include "inst-man.h"
#include "ccfv.h"
#include "inst-pre.h"
#include "inst-trigger.h"

#if defined(DEBUG_HEURISTICS)
#define DEBUG_TRIGGERS 1
#endif

Tstack_Tunifier unifiers;

/* [TODO] Awful workarounds for while E-unification is dependent on CCFV */
/* extern bool SAT_on; */
extern bool ccfv_ujobs_off;
extern int ccfv_exp_threshold;
extern int ccfv_index_threshold;
/* bool tmp_SAT_on; */
bool tmp_ujobs_off;
int tmp_exp_threshold;
int tmp_index_threshold;

/**
   \addtogroup arguments_developer

   - --triggers-m-inc

   Uses multi-triggers as last resort, if single and previous multi-triggers
   fail */
static bool triggers_multi_incremental;

static int ematch_exp_threshold;
static int ematch_index_threshold;

static unsigned triggers_stats_rounds;
static unsigned triggers_stats_time;

/*
  --------------------------------------------------------------
  Setting and releasing context information
  --------------------------------------------------------------
*/

/** \brief workaround to notify E-uni modulo it is doing E-matching for
    triggers */
bool ematch_on;

/*--------------------------------------------------------------*/

void
triggers_cycle_init()
{
  stats_counter_inc(triggers_stats_rounds);
  stats_timer_start(triggers_stats_time);
  stack_INIT(unifiers);
  stack_INIT(current_vars);
  stack_INIT(grounded_var_classes);
  vars_pos = NULL;
  /* tmp_SAT_on = SAT_on; */
  tmp_ujobs_off = ccfv_ujobs_off;
  tmp_exp_threshold = ccfv_exp_threshold;
  tmp_index_threshold = ccfv_index_threshold;
  /* SAT_on = false; */
  ccfv_ujobs_off = true;
  ccfv_exp_threshold = ematch_exp_threshold;
  ccfv_index_threshold = ematch_index_threshold;

  ematch_on = true;
}

/*--------------------------------------------------------------*/

void
triggers_cycle_done()
{
  stats_timer_stop(triggers_stats_time);
  stack_free(unifiers);
  stack_free(current_vars);
  if (vars_pos)
    free(vars_pos);
  stack_free(grounded_var_classes);

  /* SAT_on = tmp_SAT_on; */
  ccfv_ujobs_off = tmp_ujobs_off;
  ccfv_exp_threshold = tmp_exp_threshold;
  ccfv_index_threshold = tmp_index_threshold;
  ematch_on = false;
}

/*
  --------------------------------------------------------------
  Trigger instantiation
  --------------------------------------------------------------
*/

TSstack(_var, Tvar);
extern Tstack_var * index_lits;
extern Tstack_DAG * lit_qforms;
extern bool inst_check_loop;

/*--------------------------------------------------------------*/

/**
    \remark a DAG may be associated to several qform by its literal appearing in
    different inst rounds (or the two polarities in different quantified
    formulas of the same round) */
static bool
not_looping_SIG(TDAG qform, TDAG DAG)
{
  unsigned i;
  Tvar var;
  /* [TODO] For now only the first occurrence of a DAG is tracked. What should
     happen when a DAG appears in more than one literal? They should all be from
     the same qform otherwise it is not looping (in the criterion of qform
     originated it)? */
  assert(index_lits[DAG] && stack_size(index_lits[DAG]) == 1);
  for (i = 0; i < stack_size(index_lits[DAG]); ++i)
    {
      var = stack_get(index_lits[DAG], i);
      if (!lit_qforms[var])
        continue;
      /* [TODO] Is this OK when there are several quantified formulas?? */
      if (stack_DAG_contains(lit_qforms[var], qform))
        return false;
    }
  return true;
}

/*--------------------------------------------------------------*/

/* [TODO] This could be optimized to only retrieve signatures from the current
   level? It makes sense for triggers, no?? */


/** \brief If checking for loops, only retrieve signatures indexed from literals
    which were not created by the given quantified formula */
#define retrieve_sigs(qform, acc, sigs)                                 \
  do                                                                    \
    {                                                                   \
      unsigned ret_i;                                                   \
      if (!inst_check_loop)                                             \
        stack_merge(acc, sigs);                                         \
      else                                                              \
        for (ret_i = 0; ret_i < stack_size(sigs); ++ret_i)              \
          if (not_looping_SIG(qform, stack_get(sigs, ret_i)))           \
            stack_push(acc, stack_get(sigs, ret_i));                    \
    }                                                                   \
  while (0)

/*--------------------------------------------------------------*/

/**
    \author Haniel Barbosa
    \brief instantiate a set of patterns through E-matching
    \param trigger a set of patterns */
static void
trigger_ematch(TDAG qform, Tstack_DAG trigger)
{
  unsigned i;
  TDAG pattern;
  Tstack_DAG signatures;
  Findex f_index;
  Pindex p_index;
  Tstack_Tunifier result, old_result, result_pattern;
  /* Sets context based on patterns */
  for (i = 0; i < stack_size(trigger); ++i)
    {
      /* [TODO] Workaround because some triggers don't come from the original
         formula??? This should be done in the pre-processing */
      if (ground(stack_get(trigger, i)))
        set_fvars(stack_get(trigger, i));
      /* Some formulas may have been annotated with nonsense patterns */
      if (ground(stack_get(trigger, i)))
        return;
    }
  set_context_vars(trigger);
  assert(stack_size(current_vars));
  stack_INIT(result);
  for (i = 0; i < stack_size(trigger); ++i)
    {
#if DEBUG_INDEX
      my_DAG_message("trigger_ematch: Index signatures of %s:\n", DAG_symb_name2(DAG_symb(pattern)));
#endif
      pattern = stack_get(trigger, i);
      if (DAG_sort(pattern) == SORT_BOOLEAN)
        {
          if (!get_Pindex(DAG_symb(pattern), &p_index))
            break;
          stack_INIT(signatures);
          if (p_index.signatures[1])
            retrieve_sigs(qform, signatures, p_index.signatures[1]);
          if (p_index.signatures[0])
            retrieve_sigs(qform, signatures, p_index.signatures[0]);
        }
      else
        {
          if (!get_Findex(DAG_symb(pattern), &f_index))
            break;
          stack_INIT(signatures);
          if (f_index.signatures)
            retrieve_sigs(qform, signatures, f_index.signatures);
          if (f_index.diseq_terms)
            retrieve_sigs(qform, signatures, f_index.diseq_terms);
        }
#if DEBUG_INDEX
      print_Tstack_DAG(signatures);
#endif
      stack_INIT(result_pattern);
      match_DAGs(&result_pattern, pattern, signatures);
      stack_free(signatures);
      /* If matching of a pattern failed, give up */
      if (stack_is_empty(result_pattern))
        {
          stack_free(result_pattern);
          break;
        }
      /* This is the first pattern instantiated  */
      if (stack_is_empty(result))
        {
          stack_merge(result, result_pattern);
          stack_free(result_pattern);
          continue;
        }
      /* Combine each new set of instantiations with previous ones */
      stack_COPY(old_result, result);
      stack_reset(result);
      combine_unifiers(&result, old_result, result_pattern);
      stack_apply(old_result, unify_free);
      stack_free(old_result);
      if (stack_is_empty(result))
        break;
    }
  /* Trigger instantiation failed */
  if (i != stack_size(trigger))
    {
      stack_apply(result, unify_free);
      stack_free(result);
      return;
    }
  if (!stack_is_empty(result))
    stack_merge(unifiers, result);
  stack_free(result);
}

/*--------------------------------------------------------------*/

/* tests if some top-most symbols in trigger is interpreted */
/* [TODO] Check this.. */
static bool
trigger_is_interpreted(Tstack_DAG trigger)
{
  unsigned i;
  for (i = 0;i < stack_size(trigger); ++i)
    if (DAG_symb_type(DAG_symb(stack_get(trigger, i))) & SYMB_INTERPRETED)
      return true;
  return false;
}

/*--------------------------------------------------------------*/

extern bool triggers_new;

bool
triggers_qnt(TDAG qform)
{
  unsigned i;
  Tstack_DAGstack * Ptriggers =
    (Tstack_DAGstack *) DAG_prop_get(qform, DAG_PROP_TRIGGER);
  /* Formula not ammenable for trigger instantiation */
  if (!Ptriggers)
    return false;
  /* Instantiate first non-interpreted single triggers, then try each multi */
  if (triggers_new && triggers_multi_incremental)
    {
      /* Do single triggers */
      for (i = 0; i < stack_size(*Ptriggers); ++i)
        {
          if (trigger_is_interpreted(stack_get(*Ptriggers, i)))
            continue;
          if (stack_size(stack_get(*Ptriggers, i)) > 1)
            break;
          trigger_ematch(qform, stack_get(*Ptriggers, i));
        }
      /* Try multi-triggers only while no insts */
      while (stack_is_empty(unifiers) && i < stack_size(*Ptriggers))
        if (!trigger_is_interpreted(stack_get(*Ptriggers, i)))
          trigger_ematch(qform, stack_get(*Ptriggers, i++));
        else
          ++i;
    }
  else
    for (i = 0; i < stack_size(*Ptriggers); ++i)
      if (!trigger_is_interpreted(stack_get(*Ptriggers, i)))
        trigger_ematch(qform, stack_get(*Ptriggers, i));
  /* If no instances, instantiate interpreted triggers */
  if (stack_is_empty(unifiers))
    for (i = 0; i < stack_size(*Ptriggers); ++i)
      if (trigger_is_interpreted(stack_get(*Ptriggers, i)))
        trigger_ematch(qform, stack_get(*Ptriggers, i));
  return !stack_is_empty(unifiers);
}

/*--------------------------------------------------------------*/

Tstack_DAGinst
triggers(void)
{
  unsigned i, found_unifiers;
  Tstack_DAGinst result;
  triggers_cycle_init();
  found_unifiers = 0;
  stack_INIT(result);
  for (i = 0; i < stack_size(CC_quantified); ++i)
    if (triggers_qnt(stack_get(CC_quantified, i)))
      {
        stack_inc(result);
        stack_top(result).qform = stack_get(CC_quantified, i);
        stack_top(result).clause = NULL;
#if DEBUG_TRIGGERS > 1
        my_DAG_message("{%d}%D\n", stack_get(CC_quantified, i),
                       stack_get(CC_quantified, i));
        print_Tstack_Tunifier(unifiers);
#endif
        stack_COPY(stack_top(result).insts, unifiers);
        found_unifiers += stack_size(unifiers);
        stack_reset(unifiers);
      }
#if DEBUG_TRIGGERS
  my_message("\t\t(%2.2fs) Triggers %d: got %d unifiers\n",
             stats_timer_get(triggers_stats_time),
             stats_counter_get(triggers_stats_rounds), found_unifiers);
#endif
  triggers_cycle_done();
  if (stack_is_empty(result))
    stack_free(result);
  return result;
}

/*--------------------------------------------------------------*/

void
triggers_init(void)
{
  ematch_on = false;

  triggers_multi_incremental = false;
  options_new(0, "triggers-m-inc",
              "Use multi-triggers incrementally (if previous fail)",
              &triggers_multi_incremental);

  options_new_int(0, "ematch-exp",
                  "Limit to potential number of unifiers for Ematch [optimize]",
                  "10^7",
                  &ematch_exp_threshold);
  ematch_exp_threshold = 10000000;

  options_new_int(0, "ematch-index",
                  "Limit to size of indexes considered in Ematch [optimize]",
                  "10^4",
                  &ematch_index_threshold);
  ematch_index_threshold = 10000;

  triggers_stats_rounds =
    stats_counter_new("triggers/rounds",
                      "number of trigger instantiation rounds",
                      "%6d");
  triggers_stats_time =
    stats_timer_new("triggers_time", "Triggers Instantiation time", "%7.2f",
                    STATS_TIMER_ALL);
}

/*--------------------------------------------------------------*/

void
triggers_done(void)
{

}

/*--------------------------------------------------------------*/
