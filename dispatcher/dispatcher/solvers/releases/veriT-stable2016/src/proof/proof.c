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
   \file proof.c
   \author Pascal Fontaine

   \brief proof module.

   This module provides API functions to memorize the proofs done in
   veriT.
*/

#include "config.h"

#ifdef PROOF

#include <string.h>

#include "general.h"
#include "list.h"
#include "table.h"
#include "options.h"
#include "statistics.h"

#include "bool.h"
#include "DAG.h"
#include "DAG-flag.h"
#include "DAG-prop.h"
#include "DAG-print.h"
#include "DAG-ptr.h"
#include "DAG-tmp.h"
#include "hash.h"
#include "h-util.h"
#include "polarities.h"
#include "proof.h"
#include "veriT-status.h"
#include "veriT-state.h"
#include "free-vars.h"

/* #define DEBUG_PROOF */

bool proof_on = false;

static Tstatus status = OPEN;
static Tproof empty_clause = 0;

int option_proof_version = 0;
char * option_proof_filename = NULL;
static bool option_proof_with_sharing = false;
bool option_proof_prune = false;
bool option_proof_merge = false;
/**
   \addtogroup arguments_developer
   - --print-proof-file-from-input
   Set proof output file name from input file name by adding .proof */
bool option_proof_file_from_input;
/**
   \addtogroup arguments_developer
   - --proof-stats
   Output proof statistics (incompatible with actual proof output) */
bool option_proof_stat = false;

/*
  --------------------------------------------------------------
  generic help functions
  --------------------------------------------------------------
*/

static int
DAG_polarity(TDAG DAG)
/* PF returns the polarity of a literal */
{
  int polarity = 1;
  while (DAG_symb(DAG) == CONNECTOR_NOT)
    {
      DAG = DAG_arg0(DAG);
      polarity = ~polarity;
    }
  return polarity & 1;
}

/*--------------------------------------------------------------*/

static TDAG
DAG_atom(TDAG DAG)
/* PF returns the atom of a literal */
{
  while (DAG_symb(DAG) == CONNECTOR_NOT)
    DAG = DAG_arg0(DAG);
  return DAG;
}

/*--------------------------------------------------------------*/

#if 0
static void
clause_symb_fprint(FILE * file, Tclause clause)
/* PF prints clause from SAT solver (debugging) */
{
  unsigned i;
  if (!clause)
    fprintf(file, "NULL clause");
  else if (clause->nb_lits == 0)
    fprintf(file, "Empty clause");
  else
    {
      fprintf(file, "(or ");
      for (i = 0; i < clause->nb_lits; i++)
        {
          if (i)
            fprintf(file, " ");
          if (!lit_pol(clause->lits[i]))
            fprintf(file, "(not ");
          DAG_fprint(file, var_to_DAG(lit_var(clause->lits[i])));
          if (!lit_pol(clause->lits[i]))
            fprintf(file, ")");
        }
      fprintf(file, ")\n");
    }
}
#endif

/*
  --------------------------------------------------------------
  proof_clause
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine

   proof unit type: gives hint of the rule used to deduce
*/
typedef enum Tpc_type {
  pc_type_none,
  pc_type_input,
  pc_type_deep_res,
  pc_type_true,
  pc_type_false,
  pc_type_and_pos,
  pc_type_and_neg,
  pc_type_or_pos,
  pc_type_or_neg,
  pc_type_xor_pos1,
  pc_type_xor_pos2,
  pc_type_xor_neg1,
  pc_type_xor_neg2,
  pc_type_implies_pos,
  pc_type_implies_neg1,
  pc_type_implies_neg2,
  pc_type_equiv_pos1,
  pc_type_equiv_pos2,
  pc_type_equiv_neg1,
  pc_type_equiv_neg2,
  pc_type_ite_pos1,
  pc_type_ite_pos2,
  pc_type_ite_neg1,
  pc_type_ite_neg2,
  pc_type_eq_reflexive,
  pc_type_eq_transitive,
  pc_type_eq_congruent,
  pc_type_eq_congruent_pred,
  pc_type_eq_congruent_general,
  pc_type_distinct_elim,
  pc_type_chainable_elim,
  pc_type_right_assoc_elim,
  pc_type_left_assoc_elim,
  pc_type_la_rw_eq,
  pc_type_la_generic,
  pc_type_lia_generic,
  pc_type_nla_generic,
  pc_type_disequality_lemma,
  pc_type_totality_lemma,
  pc_type_arith_lemma,
  pc_type_forall_inst_lemma,
  pc_type_exists_inst_lemma,
  pc_type_skolem_ex_lemma,
  pc_type_skolem_all_lemma,
  pc_type_qnt_simp_lemma,
  pc_type_qnt_merge_lemma,
  pc_type_fol_lemma,
  pc_type_th_resolution,
  pc_type_SAT_resolution,
  pc_type_and,
  pc_type_not_or,
  pc_type_or,
  pc_type_not_and,
  pc_type_xor1,
  pc_type_xor2,
  pc_type_not_xor1,
  pc_type_not_xor2,
  pc_type_implies,
  pc_type_not_implies1,
  pc_type_not_implies2,
  pc_type_equiv1,
  pc_type_equiv2,
  pc_type_not_equiv1,
  pc_type_not_equiv2,
  pc_type_ite1,
  pc_type_ite2,
  pc_type_not_ite1,
  pc_type_not_ite2,
  pc_type_tmp_alphaconv,
  pc_type_tmp_let_elim,
  pc_type_tmp_nary_elim,
  pc_type_tmp_distinct_elim,
  pc_type_tmp_eq_norm,
  pc_type_tmp_simp_arith,
  pc_type_tmp_ite_elim,
  pc_type_tmp_macrosubst,
  pc_type_tmp_betared,
  pc_type_tmp_bfun_elim,
  pc_type_tmp_sk_connector,
  pc_type_tmp_pm_process,
  pc_type_tmp_qnt_tidy,
  pc_type_tmp_qnt_simplify,
  pc_type_tmp_skolemize,
  pc_type_tmp_LA_pre,

  pc_type_subproof,
  PC_TYPE_MAX
} Tpc_type;

/*
  sed "s/.*{\"\(.*\)\", \".*\"},/\1/;/^$/d;s/\(.*\)/  type_\1 = proof_clause_types_get(\"\1\");/" afile.txt
  echo "  pc_type_none,"; sed "s/.*{\"\(.*\)\", \".*\"},/\1/;/^$/d;s/\(.*\)/  pc_type_\1,/" afile.txt
*/

/**
   @author Pascal Fontaine

   Table of description of proof unit types.
*/
struct {
  char * name;  /**< name of clause type: specifies how it is deduced */
  char * descr; /**< human readable description for documentation */
  int nb_reasons;
  unsigned nb_params;
} pc_type_desc[] =
  { {NULL, NULL, 0, 0},
    {"input", "{input formula}", 0, 0},
    {"deep_res", "deep resolution in formula", -1, 0},
    {"true", "valid: {true}", 0, 0},
    {"false", "valid: {(not false)}", 0, 0},
    {"and_pos", "valid: {(not (and a_1 ... a_n)) a_i}", 0, 1},
    {"and_neg", "valid: {(and a_1 ... a_n) (not a_1) ... (not a_n)}", 0, 0},
    {"or_pos", "valid: {(not (or a_1 ... a_n)) a_1 ... a_n}", 0, 0},
    {"or_neg", "valid: {(or a_1 ... a_n) (not a_i)}", 0, 1},
    {"xor_pos1", "valid: {(not (xor a b)) a b}", 0, 0},
    {"xor_pos2", "valid: {(not (xor a b)) (not a) (not b)}", 0, 0},
    {"xor_neg1", "valid: {(xor a b) a (not b)}", 0, 0},
    {"xor_neg2", "valid: {(xor a b) (not a) b}", 0, 0},
    {"implies_pos", "valid: {(not (implies a b)) (not a) b}", 0, 0},
    {"implies_neg1", "valid: {(implies a b) a}", 0, 0},
    {"implies_neg2", "valid: {(implies a b) (not b)}", 0, 0},
    {"equiv_pos1", "valid: {(not (iff a b)) a (not b)}", 0, 0},
    {"equiv_pos2", "valid: {(not (iff a b)) (not a) b}", 0, 0},
    {"equiv_neg1", "valid: {(iff a b) (not a) (not b)}", 0, 0},
    {"equiv_neg2", "valid: {(iff a b) a b}", 0, 0},
    {"ite_pos1", "valid: {(not (if_then_else a b c)) a c}", 0, 0},
    {"ite_pos2", "valid: {(not (if_then_else a b c)) (not a) b}", 0, 0},
    {"ite_neg1", "valid: {(if_then_else a b c) a (not c)}", 0, 0},
    {"ite_neg2", "valid: {(if_then_else a b c) (not a) (not b)}", 0, 0},
    {"eq_reflexive", "valid: {(= x x)}", 0, 0},
    {"eq_transitive", "valid: {(not (= x_1 x_2)) ... (not (= x_{n-1} x_n)) (= x_1 x_n)}", 0, 0},
    {"eq_congruent", "valid: {(not (= x_1 y_1)) ... (not (= x_n y_n)) (= (f x_1 ... x_n) (f y_1 ... y_n))}", 0, 0},
    {"eq_congruent_pred", "valid: {(not (= x_1 y_1)) ... (not (= x_n y_n)) (not (p x_1 ... x_n)) (p y_1 ... y_n)}", 0, 0},
    {"eq_congruent_general", "valid: {(not (= x_1 y_1)) ... (not (= x_n y_n)) (not (p t_1 ... x_1 ... t_m ... x_n)) (p t_1 ... y_1 ... t_m ... y_n)}", 0, 0},
    {"distinct_elim", "valid: {(= DIST(...) ... neq ...)}", 0, 0},
    {"chainable_elim", "valid: {(= (f t1 ... tn ) (and (f t1 t2 ) (f t2 t3 ) ... (f tn−1 tn ))}", 0, 0},
    {"right_assoc_elim", "valid: {(= (f t1 ... tn ) (f t1 (f t2 ... (f tn−1 tn ) ... )}", 0, 0},
    {"left_assoc_elim", "valid: {(= (f t1 ... tn ) (f ... (f (f t1 t2 ) t3 ) ... tn )}", 0, 0},
    {"la_rw_eq", "valid: {(= (a = b) (and (a <= b) (b <= a))}", 0, 0},
    {"la_generic", "valid: not yet defined", 0, 0},
    {"lia_generic", "valid: not yet defined", 0, 0},
    {"nla_generic", "valid: not yet defined", 0, 0},
    {"la_disequality", "valid: not yet defined", 0, 0},
    {"la_totality", "valid: {(le t1 t2), (le t2 t1)}", 0, 0},
    {"la_tautology", "valid: linear arithmetic tautology without variable", 0, 0},
    {"forall_inst", "valid: {(implies (forall X (A X)) (A {X \\ t}))}", 0, 0},
    {"exists_inst", "valid: {(implies (A t) (exists X (A {t \\ X})))}", 0, 0},
    {"skolem_ex_ax", "valid: {(not (exists X (A X))), A(sk)} where sk is fresh", 0, 0},
    {"skolem_all_ax", "valid: {(not A(sk)), (forall X (A X))} where sk is fresh", 0, 0},
    {"qnt_simplify_ax", "valid: to be defined", 0, 0},
    {"qnt_merge_ax", "valid: {(not (Q x (Q y (F x y)))), (Q x y (F x y)))} where sk is fresh", 0, 0},
    {"fol_ax", "valid: to be defined [produced by the E prover]", 0, 0},
    {"th_resolution", "resolution of 2 or more clauses from theory reasoner", -1, 0},
    {"resolution", "resolution of 2 or more clauses from SAT solver", -1, 0},
    {"and", "{(and a_1 ... a_n)} --> {a_i}", 1, 1},
    {"not_or", "{(not (or a_1 ... a_n))} --> {(not a_i)}", 1, 1},
    {"or", "{(or a_1 ... a_n)} --> {a_1 ... a_n}", 1, 0},
    {"not_and", "{(not (and a_1 ... a_n))} --> {(not a_1) ... (not a_n)}", 1, 0},
    {"xor1", "{(xor a b)} --> {a b}", 1, 0},
    {"xor2", "{(xor a b)} --> {(not a) (not b)}", 1, 0},
    {"not_xor1", "{(not (xor a b))} --> {a (not b)}", 1, 0},
    {"not_xor2", "{(not (xor a b))} --> {(not a) b}", 1, 0},
    {"implies", "{(implies a b)} --> {(not a) b}", 1, 0},
    {"not_implies1", "{(not (implies a b))} --> {a}", 1, 0},
    {"not_implies2", "{(not (implies a b))} --> {(not b)}", 1, 0},
    {"equiv1", "{(iff a b)} --> {(not a) b}", 1, 0},
    {"equiv2", "{(iff a b)} --> {a (not b)}", 1, 0},
    {"not_equiv1", "{(not (iff a b))} --> {a b}", 1, 0},
    {"not_equiv2", "{(not (iff a b))} --> {(not a) (not b)}", 1, 0},
    {"ite1", "{(if_then_else a b c)} --> {a c}", 1, 0},
    {"ite2", "{(if_then_else a b c)} --> {(not a) b}", 1, 0},
    {"not_ite1", "{(not (if_then_else a b c))} --> {a (not c)}", 1, 0},
    {"not_ite2", "{(not (if_then_else a b c))} --> {(not a) (not b)}", 1, 0},
    {"tmp_alphaconv", "{formula} --> {alpha conversion with fresh symbols}", 1, 0},
    {"tmp_let_elim", "{formula} --> {formula where let have been eliminated}", 1, 0},
    {"tmp_nary_elim", "{formula} --> {formula where n-ary symbols have been eliminated}", 1, 0},
    {"tmp_distinct_elim", "{formula} --> {formula where distinct have been eliminated}", 1, 0},
    {"tmp_eq_norm", "{formula} --> {formula where eqs between propositions have been turned into equivs}", 1, 0},
    {"tmp_simp_arith", "{formula} --> {formula where arith terms have been normalized}", 1, 0},
    {"tmp_ite_elim", "{formula} --> {formula where ite terms have been eliminated}", 1, 0},
    {"tmp_macrosubst", "{formula} --> {formula where macros have been substituted}", 1, 0},
    {"tmp_betared", "{formula} --> {formula where beta reduction has been applied}", 1, 0},
    {"tmp_bfun_elim", "{formula} --> {formula where functions with Boolean arguments have been simplified}", 1, 0},
    {"tmp_sk_connector", "{formula} --> {formula where some connectors have been suppressed for skolemization}", 1, 0},
    {"tmp_pm_process", "{formula} --> {formula where polymorphism has been eliminated}", 1, 0},
    {"tmp_qnt_tidy", "{formula} --> {formula where quantifiers have been normalized}", 1, 0},
    {"tmp_qnt_simplify", "{formula} --> {formula where quantifiers have been simplified}", 1, 0},
    {"tmp_skolemize", "{formula} --> {Skolemized formula}", 1, 0},
    {"tmp_LA_pre", "{formula} --> {formula with = replaced by conjunction of two inequalities}", 1, 0},

    {"subproof", "", 1, 0},
    {NULL, NULL, 0, 0}
  };

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief Deduction unit datastructure. */
struct TSproof_clause {
  unsigned nb;      /**< Number of literals in the proof clause */
  unsigned na;      /**< Number of literals as arguments */
  unsigned misc;    /**< Used to eliminate unused parts in the derivation */
  TDAG * PDAG;      /**< PDAG array of the literals in the proof clause
                       followed by the literals as arguments */
  Tpc_type type;    /**< proof type */
  unsigned argc;    /**< Number of arguments */
  unsigned * argv;  /**< Numerical arguments (either proof clause ids
                       or position in referred clauses) */
};
typedef struct TSproof_clause * Tproof_clause;

/*--------------------------------------------------------------*/

struct TSproof_clause_subproof {
  unsigned nb;      /**< Number of literals in the proof clause */
  unsigned unused;
  unsigned misc;    /**< Used to eliminate unused parts in the derivation */
  TDAG * PDAG;      /**< PDAG array of the literals in the proof clause */
  Tpc_type type;    /**< proof type */
  Ttable context;
};
typedef struct TSproof_clause_subproof * Tproof_clause_subproof;

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief Creates proof clause
   \return a pointer to the proof clause */
static Tproof_clause
proof_clause_new(void)
{
  Tproof_clause proof_clause = NULL;
  MY_MALLOC(proof_clause, sizeof(struct TSproof_clause));
  proof_clause->nb = 0;
  proof_clause->na = 0;
  proof_clause->misc = 0;
  proof_clause->PDAG = NULL;
  proof_clause->type = pc_type_none;
  proof_clause->argc = 0;
  proof_clause->argv = NULL;
  return proof_clause;
}

/*--------------------------------------------------------------*/

static Tproof_clause
proof_clause_new_subproof(Ttable context)
{
  Tproof_clause_subproof proof_clause = NULL;
  MY_MALLOC(proof_clause, sizeof(struct TSproof_clause_subproof));
  proof_clause->nb = 0;
  proof_clause->unused = 0;
  proof_clause->misc = 0;
  proof_clause->PDAG = NULL;
  proof_clause->type = pc_type_subproof;
  proof_clause->context = context;
  return (Tproof_clause) proof_clause;
}

/*--------------------------------------------------------------*/

static void
proof_clause_add_reason(Tproof_clause proof_clause, Tproof proof_id)
{
  assert(proof_clause->type < pc_type_subproof);
  proof_clause->argc++;
  MY_REALLOC(proof_clause->argv, proof_clause->argc * sizeof(unsigned));
  proof_clause->argv[proof_clause->argc - 1] = proof_id;
}

/*--------------------------------------------------------------*/

static void
proof_clause_add_reason_unsigned(Tproof_clause proof_clause, unsigned i)
{
  assert(proof_clause->type < pc_type_subproof);
  proof_clause->argc++;
  MY_REALLOC(proof_clause->argv, proof_clause->argc * sizeof(unsigned));
  proof_clause->argv[proof_clause->argc - 1] = i;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief free proof clause
   \param Pproof_clause a pointer to the proof clause to free */
static void
proof_clause_free(Tproof_clause * Pproof_clause)
{
  unsigned i;
  if (!*Pproof_clause)
    return;
  for (i = 0; i < (*Pproof_clause)->nb + (*Pproof_clause)->na; i++)
    if ((*Pproof_clause)->PDAG[i])
      DAG_free((*Pproof_clause)->PDAG[i]);
  assert(!(*Pproof_clause)->misc);
  free((*Pproof_clause)->PDAG);
  if ((*Pproof_clause)->type == pc_type_subproof)
    {
      Ttable context = ((Tproof_clause_subproof) *Pproof_clause)->context;
      for (i = 1; i < table_length(context); i++)
        {
          Tproof_clause proof_clause = table_get(context, i);
          proof_clause_free(&proof_clause);
        }
      if (table_get(context, 0))
        my_error("proof_done: internal error\n");
      table_free(&context);
    }
  else
    free((*Pproof_clause)->argv);
  free(*Pproof_clause);
  *Pproof_clause = NULL;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief add DAG to proof clause
   \param proof_clause the proof clause
   \param DAG the DAG to add
   \remark all DAGs in the clause should be added before DAG arguments */
static void
proof_clause_add(Tproof_clause proof_clause, TDAG DAG)
{
  assert(!proof_clause->na);
  proof_clause->nb++;
  if (!proof_clause->nb)
    my_error("proof_clause_add: too many elements in clause\n");
  MY_REALLOC(proof_clause->PDAG, proof_clause->nb * sizeof(TDAG));
  proof_clause->PDAG[proof_clause->nb - 1] = DAG;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief add DAG as argument of proof step
   \param proof_clause the proof clause
   \param DAG the DAG to add
   \remark all DAGs in the clause should be added before DAG arguments */
static void
proof_clause_add_DAG_arg(Tproof_clause proof_clause, TDAG DAG)
{
  proof_clause->na++;
  if (!proof_clause->na)
    my_error("proof_clause_add_DAG_arg: too many arguments\n");
  MY_REALLOC(proof_clause->PDAG,
             (proof_clause->nb + proof_clause->na) * sizeof(TDAG));
  proof_clause->PDAG[proof_clause->nb + proof_clause->na - 1] = DAG;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief prints proof clause (for outputting the proof and debugging purposes)
   \param proof_clause the proof clause
   \param id the proof clause id
   \param file the file to write to */
static void
proof_clause_print(Tproof_clause proof_clause, Tproof id, FILE * file)
{
  unsigned i;
  if (proof_clause->type == pc_type_subproof)
    {
      Ttable context = ((Tproof_clause_subproof) proof_clause)->context;
      fprintf(file, "%d:(subproof\n", id);
      for (i = 1; i < table_length(context); i++)
        proof_clause_print(table_get(context, i), i, file);
      fprintf(file, "(");
      for (i = 0; i < proof_clause->nb; i++)
        {
          if (i) fprintf(file, " ");
          if (option_proof_with_sharing)
            DAG_fprint_sharing(file, proof_clause->PDAG[i]);
          else
            DAG_fprint(file, proof_clause->PDAG[i]);
        }
      fprintf(file, ")\n");
      return;
    }
  fprintf(file, "%d:(%s (", id, pc_type_desc[proof_clause->type].name);
  for (i = 0; i < proof_clause->nb; i++)
    {
      if (i) fprintf(file, " ");
      if (option_proof_with_sharing)
        DAG_fprint_sharing(file, proof_clause->PDAG[i]);
      else
        DAG_fprint(file, proof_clause->PDAG[i]);
    }
  fprintf(file, ")");
  for (i = 0; i < proof_clause->argc; i++)
    fprintf(file, " %d", proof_clause->argv[i]);
  fprintf(file, ")\n");
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
*/
static void
proof_clause_reset_misc(Tproof_clause proof_clause)
{
  unsigned i;
  for (i = 0; i < proof_clause->nb; i++)
    DAG_fprint_sharing_reset(proof_clause->PDAG[i]);
  if (proof_clause->type == pc_type_subproof)
    {
      Ttable context = ((Tproof_clause_subproof) proof_clause)->context;
      for (i = 1; i < table_length(context); i++)
        proof_clause_reset_misc(table_get(context, i));
    }
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief computes the clause from resolution of both first arguments
   \param proof_clause1 first proof clause
   \param proof_clause2 second proof clause
   \param DAG resolvant
*/
static Tproof_clause
proof_clause_resolve(Tproof_clause proof_clause1,
                     Tproof_clause proof_clause2,
                     TDAG DAG)
{
  unsigned i;
  int pol1 = -1, pol2 = -1;
  Tproof_clause result = proof_clause_new();

  for (i = 0; i < proof_clause1->nb; i++)
    if (DAG_atom(proof_clause1->PDAG[i]) == DAG)
      {
        if (pol1 != -1)
          goto proof_clause_resolve_exception;
        pol1 = DAG_polarity(proof_clause1->PDAG[i]);
      }
    else if (!DAG_flag(proof_clause1->PDAG[i]))
      {
        proof_clause_add(result, DAG_dup(proof_clause1->PDAG[i]));
        DAG_flag_set(proof_clause1->PDAG[i], 1);
      }
  for (i = 0; i < proof_clause2->nb; i++)
    if (DAG_atom(proof_clause2->PDAG[i]) == DAG)
      {
        if (pol2 != -1)
          goto proof_clause_resolve_exception;
        pol2 = DAG_polarity(proof_clause2->PDAG[i]);
      }
    else if (!DAG_flag(proof_clause2->PDAG[i]))
      {
        proof_clause_add(result, DAG_dup(proof_clause2->PDAG[i]));
        DAG_flag_set(proof_clause2->PDAG[i], 1);
      }
  if (pol1 == -1 || pol2 == -1 || pol1 == pol2)
    goto proof_clause_resolve_exception;
  for (i = 0; i < result->nb; i++)
    DAG_flag_set(result->PDAG[i], 0);
#ifdef DEBUG_PROOF
  my_message("Resolving:\n");
  my_message("Clause 1:\n");
  proof_clause_print(proof_clause1, 0, stderr);
  my_message("Clause 2:\n");
  proof_clause_print(proof_clause2, 0, stderr);
  my_DAG_message("Resolvant: %D\n", DAG);
#endif
  return result;
 proof_clause_resolve_exception :
  my_message("Clause 1:\n");
  proof_clause_print(proof_clause1, 0, stderr);
  my_message("Clause 2:\n");
  proof_clause_print(proof_clause2, 0, stderr);
  my_DAG_message("Resolvant: %D\n", DAG);
  my_error("proof_clause_resolve: error\n");
  return NULL;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine

   Simplifies clause.
   - if clause contains X = X literals, returns TRUE clause
   - if clause contains complementary literals, returns TRUE clause
   - otherwise eliminates NOT(X = X) literals and repeated literals.
   - NOT(NOT P) is recursively rewritten as P
*/
static Tproof_clause
proof_clause_clean(Tproof_clause proof_clause)
{
  unsigned i, tmp;
  Tproof_clause result;
  /* PF check for valid clauses, and use loop to detect
     if literals to eliminate (NOT X=X or repeated) */
  for (tmp = 0, i = 0; i < proof_clause->nb; i++)
    {
      TDAG DAG = proof_clause->PDAG[i];
      int pol = DAG_polarity(proof_clause->PDAG[i]);
      while (DAG_symb(proof_clause->PDAG[i]) == CONNECTOR_NOT &&
             DAG_symb(DAG_arg0(proof_clause->PDAG[i])) == CONNECTOR_NOT)
        {
          proof_clause->PDAG[i] = DAG_dup(DAG_arg0(DAG_arg0(DAG)));
          DAG_free(DAG);
          DAG = proof_clause->PDAG[i];
        }
      DAG = DAG_atom(DAG);
#if 0
      if (DAG_symb(DAG) == PREDICATE_EQ && DAG_arg0(DAG) == DAG_arg1(DAG))
        {
          if (pol)
            {
              tmp = 2; /* Valid clause */
              break;
            }
          tmp = 1; /* Literal to eliminate */
        }
      else
#endif
        if (DAG_flag(DAG))
          {
            DAG_flag_set(DAG, DAG_flag(DAG) | (pol ? POL_POS : POL_NEG));
            if (DAG_flag(DAG) == POL_BOTH)
              {
                tmp = 2; /* Valid clause */
                break;
              }
            tmp = 1; /* Literal to eliminate */
          }
        else
          DAG_flag_set(DAG, DAG_flag(DAG) | (pol ? POL_POS : POL_NEG));
    }
  if (tmp == 0)
    {
      /* No transformation has to occur */
      for (i = 0; i < proof_clause->nb; i++)
        DAG_flag_set(DAG_atom(proof_clause->PDAG[i]), 0);
      return proof_clause;
    }
  result = proof_clause_new();
  result->type = proof_clause->type;
  result->argc = proof_clause->argc;
  MY_MALLOC(result->argv, result->argc * sizeof(unsigned));
  for (i = 0; i < result->argc; i++)
    result->argv[i] = proof_clause->argv[i];
  if (tmp == 2)
    {
      /* Valid clause */
      for (i = 0; i < proof_clause->nb; i++)
        DAG_flag_set(DAG_atom(proof_clause->PDAG[i]), 0);
      proof_clause_add(result, DAG_dup(DAG_TRUE));
#ifdef DEBUG_PROOF
      my_message("proof_clause_clean:\n");
      my_message("proof_clause:\n");
      proof_clause_print(proof_clause, 0, stderr);
      my_message("result:\n");
      proof_clause_print(result, 0, stderr);
#endif
      proof_clause_free(&proof_clause);
      return result;
    }
  /* Literal to eliminate */
  for (i = 0; i < proof_clause->nb; i++)
    if (DAG_flag(DAG_atom(proof_clause->PDAG[i])))
      {
        proof_clause_add(result, DAG_dup(proof_clause->PDAG[i]));
        DAG_flag_set(DAG_atom(proof_clause->PDAG[i]), 0);
      }
#ifdef DEBUG_PROOF
  my_message("proof_clause_clean:\n");
  my_message("proof_clause:\n");
  proof_clause_print(proof_clause, 0, stderr);
  my_message("result:\n");
  proof_clause_print(result, 0, stderr);
#endif
  proof_clause_free(&proof_clause);
  return result;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief computes SAT solver clause from proof clause
*/
#if 0
static Tclause
proof_clause_clause(Tproof_clause proof_clause)
{
  int i;
  Tclause clause = clause_new(proof_clause->nb);
  for (i = 0; i < proof_clause->nb; i++)
    clause_set_literal(clause, i, DAG_to_lit(proof_clause->PDAG[i]));
  clause_clean(clause);
  return clause;
}
#endif

/*
  --------------------------------------------------------------
  Proof Context hash
  --------------------------------------------------------------
*/

/* This module is used for proof merging */

typedef struct TSproof_clause_hash
{
  Tproof_clause proof_clause;
  Tproof proof_id;
} * Tproof_clause_hash;

static Thash context_hash;

/*--------------------------------------------------------------*/

static Tproof_clause_hash
context_hash_new(Tproof_clause proof_clause, Tproof proof_id)
{
  Tproof_clause_hash proof_clause_hash;
  MY_MALLOC(proof_clause_hash, sizeof(struct TSproof_clause_hash));
  proof_clause_hash->proof_clause = proof_clause;
  proof_clause_hash->proof_id = proof_id;
  return proof_clause_hash;
}

/*--------------------------------------------------------------*/

static unsigned int
context_hash_function(Tproof_clause_hash proof_clause_hash)
{
  Tproof_clause proof_clause = proof_clause_hash->proof_clause;
  unsigned i, key;
  key = hash_one_at_a_time_u_inc(0, proof_clause->nb);
  for (i = 0; i < proof_clause->nb; i++)
    key = hash_one_at_a_time_u_inc(key, DAG_key(proof_clause->PDAG[i]));
  return key;
}

/*--------------------------------------------------------------*/

static unsigned int
context_hash_equal(Tproof_clause_hash proof_clause_hash1,
                   Tproof_clause_hash proof_clause_hash2)
{
  unsigned i;
  if (proof_clause_hash1->proof_clause->nb !=
      proof_clause_hash2->proof_clause->nb)
    return 0;
  for (i = 0; i < proof_clause_hash1->proof_clause->nb; i++)
    if (proof_clause_hash1->proof_clause->PDAG[i] !=
        proof_clause_hash2->proof_clause->PDAG[i])
      return 0;
  return 1;
}

/*--------------------------------------------------------------*/

static void
context_hash_free(Tproof_clause_hash proof_clause_hash)
{
  free(proof_clause_hash);
}

/*--------------------------------------------------------------*/

static void
context_hash_push(Tproof_clause proof_clause, Tproof proof_id)
{
  hash_insert(context_hash, context_hash_new(proof_clause, proof_id));
}

/*--------------------------------------------------------------*/

static Tproof
context_hash_get(Tproof_clause proof_clause)
{
  struct TSproof_clause_hash Sproof_clause_hash;
  Tproof_clause_hash proof_clause_hash;
  Sproof_clause_hash.proof_clause = proof_clause;
  Sproof_clause_hash.proof_id = 0;
  proof_clause_hash = hash_lookup(context_hash, &Sproof_clause_hash);
  if (proof_clause_hash)
    return proof_clause_hash->proof_id;
  return 0;
}

/*--------------------------------------------------------------*/

static void
context_hash_remove(Tproof_clause proof_clause)
{
  struct TSproof_clause_hash Sproof_clause_hash;
  Tproof_clause_hash proof_clause_hash;
  Sproof_clause_hash.proof_clause = proof_clause;
  Sproof_clause_hash.proof_id = 0;
  proof_clause_hash = hash_lookup(context_hash, &Sproof_clause_hash);
  if (proof_clause_hash)
    hash_remove(context_hash, &Sproof_clause_hash);
}

/*
  --------------------------------------------------------------
  Proof Context
  --------------------------------------------------------------
*/

static Ttable context = NULL;
static Tlist context_list = NULL;

static void
context_init(void)
{
  context = table_new(100, 100);
  context_list = list_cons(context, context_list);
  table_push(context, NULL);
  context_hash = hash_new(100,
                          (TFhash) context_hash_function,
                          (TFequal) context_hash_equal,
                          (TFfree) context_hash_free);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief adds clause to context, after simplification
*/
static Tproof
context_push(Tproof_clause proof_clause)
{
  proof_clause = proof_clause_clean(proof_clause);
  if (!proof_clause->type)
    my_error("context_push: proof_clause without type\n");
  table_push(context, proof_clause);
  if (!proof_clause->nb)
    empty_clause = table_length(context) - 1;
#ifdef DEBUG_PROOF
  my_message("Adding clause to context (%d)\n", table_length(context) - 1);
  proof_clause_print(proof_clause, table_length(context) - 1, stderr);
#endif
  return table_length(context) - 1;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief get clause in context with proof_id
*/
static Tproof_clause
context_get(Tproof proof_id)
{
  if (!context ||
      proof_id <= 0 ||
      proof_id >= table_length(context))
    my_error("proof_context_get: value out of bounds\n");
  return table_get(context, proof_id);
}

/*--------------------------------------------------------------*/

static void
context_prune(void)
{
  unsigned i, j;
  assert(table_length(context));
  assert(list_length(context_list) == 1);
  while (table_length(context) > 0 &&
         context_get(table_length(context) - 1)->nb != 0)
    table_pop(context);
  assert(table_length(context) > 0);
  assert(context_get(table_length(context) - 1)->nb == 0);
  /* PF first mark all used clauses (from the end) with misc */
  context_get(table_length(context) - 1)->misc = 1;
  for (i = table_length(context); --i > 0; )
    {
      Tproof_clause proof_clause = context_get(i);
      Tpc_type type = proof_clause->type;
      unsigned max = 0;
      if (!proof_clause->misc)
        continue;
      if (type == pc_type_subproof)
        continue;
      assert(pc_type_desc[type].nb_reasons != -1 ||
             pc_type_desc[type].nb_params == 0);
      assert(pc_type_desc[type].nb_reasons == -1 ||
             (((unsigned) pc_type_desc[type].nb_reasons) +
              pc_type_desc[type].nb_params == proof_clause->argc));
      max = (pc_type_desc[type].nb_reasons == -1)?
        proof_clause->argc:((unsigned) pc_type_desc[type].nb_reasons);
      for (j = 0; j < max; j++)
        {
          Tproof_clause proof_clause2 = context_get((Tproof)
                                                    proof_clause->argv[j]);
          assert(proof_clause2);
          proof_clause2->misc = 1;
        }
    }
  /* PF number all used clauses in a dense manner */
  for (i = 1, j = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = context_get(i);
      if (!proof_clause->misc)
        continue;
      proof_clause->misc = j++;
    }

  /* PF renumber clause_ids, and eliminate all unused clauses */
  for (i = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = context_get(i);
      Tpc_type type = proof_clause->type;
      unsigned max = 0;
      if (!proof_clause->misc)
        {
          proof_clause_free(&proof_clause);
          table_set(context, i, NULL);
          continue;
        }
      if (type == pc_type_subproof)
        continue;
      max = (pc_type_desc[type].nb_reasons == -1)?
        proof_clause->argc:((unsigned) pc_type_desc[type].nb_reasons);
      for (j = 0; j < max; j++)
        {
          Tproof_clause proof_clause2 = context_get((Tproof)
                                                    proof_clause->argv[j]);
          assert(proof_clause2);
          proof_clause->argv[j] = proof_clause2->misc;
        }
    }
  /* PF eliminate all the garbage */
  i = 1; j = 1;
  while (i < table_length(context))
    {
      Tproof_clause proof_clause = context_get(i);
      if (proof_clause)
        {
          table_set(context, j++, proof_clause);
          proof_clause->misc = 0;
        }
      i++;
    }
  table_resize(context, j);
}

/*--------------------------------------------------------------*/

static void
context_merge(void)
{
  unsigned i, j;
  assert(list_length(context_list) == 1);
  /* PF first enter every clause into a hash table, and mark all
     repeated clauses with the number of the original one */
  for (i = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = context_get(i);
      Tproof proof_id = context_hash_get(proof_clause);
      if (proof_id)
        proof_clause->misc = proof_id;
      else
        context_hash_push(proof_clause, i);
    }
  /* PF renumber clause_ids */
  for (i = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = context_get(i);
      Tpc_type type = proof_clause->type;
      unsigned max = 0;
      if (type == pc_type_subproof)
        continue;
      max = (pc_type_desc[type].nb_reasons == -1)?
        proof_clause->argc:((unsigned) pc_type_desc[type].nb_reasons);
      for (j = 0; j < max; j++)
        {
          Tproof_clause proof_clause2 = context_get(proof_clause->argv[j]);
          assert(proof_clause2);
          if (proof_clause2->misc)
            proof_clause->argv[j] = proof_clause2->misc;
        }
    }
  /* PF remove from hash table and tidy */
  for (i = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = context_get(i);
      context_hash_remove(proof_clause);
      proof_clause->misc = 0;
    }
}

/*--------------------------------------------------------------*/

static void
context_subproof_begin(void)
{
  context = table_new(5, 1);
  context_list = list_cons(context, context_list);
  table_push(context, NULL);
}

/*--------------------------------------------------------------*/

static Tproof
context_subproof_end(void)
{
  unsigned i, j;
  Tproof_clause pc_subproof, pc;
  assert(context_list);
  assert(context == list_car(context_list));
  pc_subproof = proof_clause_new_subproof(context);
  for (i = 1; i < table_length(context) - 1; i++)
    if ((pc = table_get(context, i))->type == pc_type_input)
      for (j = 0; j < pc->nb; j++)
        proof_clause_add(pc_subproof, DAG_dup(DAG_not(pc->PDAG[j])));
  pc = table_get(context, i);
  for (j = 0; j < pc->nb; j++)
    proof_clause_add(pc_subproof, DAG_dup(pc->PDAG[j]));
  context_list = list_remove(context_list);
  assert(context_list);
  context = list_car(context_list);
  return context_push(pc_subproof);
}

/*--------------------------------------------------------------*/

static void
context_subproof_remove(void)
{
  unsigned i;
  Tproof_clause pc;
  assert(context_list);
  assert(context == list_car(context_list));
  for (i = 1; i < table_length(context); i++)
    {
      pc = (Tproof_clause)table_get(context, i);
      proof_clause_free(&pc);
    }
  if (table_get(context, 0))
    my_error("context_subproof_remove: internal error\n");
  table_free(&context);
  context_list = list_remove(context_list);
  assert(context_list);
  context = list_car(context_list);
}

/*--------------------------------------------------------------*/

static void
context_done(void)
{
  unsigned i;
  assert(list_length(context_list) == 1);
  if (!context)
    my_error("context_done: no context_init\n");
  list_free(&context_list);
  hash_free(&context_hash);
  for (i = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = context_get(i);
      proof_clause_free(&proof_clause);
    }
  if (table_get(context, 0))
    my_error("proof_done: internal error\n");
  table_free(&context);
}

/*
  --------------------------------------------------------------
  Clause checking
  --------------------------------------------------------------
*/

static void
proof_error(char * str, Tproof_clause proof_clause)
{
  /* PF There is a conception problem that force to put 0 here */
  if (proof_clause)
    proof_clause_print(proof_clause, 0, stderr);
  my_error("%s : proof error\n", str);
}

/*--------------------------------------------------------------*/

static void
proof_check_eq_congruent_pred(Tproof_clause proof_clause)
{
  TDAG pred1, pred2;
  unsigned i;
  if (DAG_polarity(proof_clause->PDAG[proof_clause->nb - 2]) ==
      DAG_polarity(proof_clause->PDAG[proof_clause->nb - 1]))
    proof_error("eq_congruent_pred", proof_clause);
  pred1 = DAG_atom(proof_clause->PDAG[proof_clause->nb - 2]);
  pred2 = DAG_atom(proof_clause->PDAG[proof_clause->nb - 1]);
  if (DAG_symb(pred1) != DAG_symb(pred2) ||
      DAG_arity(pred1) != DAG_arity(pred2) ||
      DAG_arity(pred1) != proof_clause->nb - 2)
    proof_error("eq_congruent_pred", proof_clause);
  for (i = 0; i < DAG_arity(pred1); i++)
    {
      TDAG eq = DAG_atom(proof_clause->PDAG[i]);
      if (DAG_polarity(proof_clause->PDAG[i]))
        proof_error("eq_congruent_pred", proof_clause);
      if (DAG_symb(eq) != PREDICATE_EQ ||
          ((DAG_arg0(eq) != DAG_arg(pred1,i) ||
            DAG_arg1(eq) != DAG_arg(pred2,i)) &&
           (DAG_arg1(eq) != DAG_arg(pred1,i) ||
            DAG_arg0(eq) != DAG_arg(pred2,i))))
        proof_error("eq_congruent_pred", proof_clause);
    }
}

/*--------------------------------------------------------------*/

static void
proof_check_eq_congruent(Tproof_clause proof_clause)
{
  TDAG concl = proof_clause->PDAG[proof_clause->nb - 1];
  unsigned i;
  if (!DAG_polarity(concl))
    proof_error("eq_congruent", proof_clause);
  concl = DAG_atom(concl);
  if (DAG_symb(concl) != PREDICATE_EQ ||
      DAG_symb(DAG_arg0(concl)) != DAG_symb(DAG_arg1(concl)) ||
      DAG_arity(DAG_arg0(concl)) != DAG_arity(DAG_arg1(concl)) ||
      DAG_arity(DAG_arg0(concl)) != proof_clause->nb - 1)
    proof_error("eq_congruent", proof_clause);
  for (i = 0; i < DAG_arity(DAG_arg0(concl)); i++)
    {
      TDAG eq = DAG_atom(proof_clause->PDAG[i]);
      if (DAG_polarity(proof_clause->PDAG[i]))
        proof_error("eq_congruent", proof_clause);
      if (DAG_symb(eq) != PREDICATE_EQ ||
          ((DAG_arg0(eq) != DAG_arg(DAG_arg0(concl),i) ||
            DAG_arg1(eq) != DAG_arg(DAG_arg1(concl),i)) &&
           (DAG_arg1(eq) != DAG_arg(DAG_arg0(concl),i) ||
            DAG_arg0(eq) != DAG_arg(DAG_arg1(concl),i))))
        proof_error("eq_congruent", proof_clause);
    }
}

/*--------------------------------------------------------------*/

static void
proof_check_eq_reflexive(Tproof_clause proof_clause)
{
  if (proof_clause->nb != 1 ||
      DAG_symb(proof_clause->PDAG[0]) != PREDICATE_EQ ||
      DAG_arg0(proof_clause->PDAG[0]) != DAG_arg1(proof_clause->PDAG[0]))
    proof_error("eq_reflexive", proof_clause);
}

/*--------------------------------------------------------------*/

static void
proof_check_eq_transitive(Tproof_clause proof_clause)
{
  TDAG eq1, eq2;
  unsigned i, start, orient;
  assert(proof_clause->nb > 0);
  if (proof_clause->nb < 3)
    proof_error("eq_transitive", proof_clause);
  for (i = 0; i < proof_clause->nb - 1; i++)
    if (DAG_polarity(proof_clause->PDAG[i]) ||
        DAG_symb(DAG_atom(proof_clause->PDAG[i])) != PREDICATE_EQ ||
        DAG_arity(DAG_atom(proof_clause->PDAG[i])) != 2)
      proof_error("eq_transitive", proof_clause);
  i = proof_clause->nb - 1;
  if (!DAG_polarity(proof_clause->PDAG[i]) ||
      DAG_symb(DAG_atom(proof_clause->PDAG[i])) != PREDICATE_EQ ||
      DAG_arity(DAG_atom(proof_clause->PDAG[i])) != 2)
    proof_error("eq_transitive", proof_clause);
  /* PF first detect where the chain start is */
  eq1 = DAG_atom(proof_clause->PDAG[0]);
  eq2 = DAG_atom(proof_clause->PDAG[1]);
  DAG_flag_set(DAG_arg0(eq2), 1);
  DAG_flag_set(DAG_arg1(eq2), 1);
  start = (DAG_flag(DAG_arg0(eq1)) == 1);
  DAG_flag_set(DAG_arg0(eq2), 0);
  DAG_flag_set(DAG_arg1(eq2), 0);
  orient = 1 - start;
  for (i = 0; i < proof_clause->nb - 2; i++)
    {
      eq1 = DAG_atom(proof_clause->PDAG[i]);
      eq2 = DAG_atom(proof_clause->PDAG[i + 1]);
      if (DAG_arg(eq1,orient) == DAG_arg0(eq2))
        {
          orient = 1;
          continue;
        }
      if (DAG_arg(eq1,orient) == DAG_arg1(eq2))
        {
          orient = 0;
          continue;
        }
      proof_error("eq_transitive", proof_clause);
    }
  eq1 = DAG_atom(proof_clause->PDAG[proof_clause->nb - 1]);
  eq2 = DAG_atom(proof_clause->PDAG[0]);
  if (DAG_arg(eq2,start) == DAG_arg0(eq1))
    {
      eq2 = DAG_atom(proof_clause->PDAG[proof_clause->nb - 2]);
      if (DAG_arg(eq2,orient) != DAG_arg1(eq1))
        proof_error("eq_transitive", proof_clause);
    }
  else if (DAG_arg(eq2,start) == DAG_arg1(eq1))
    {
      eq2 = DAG_atom(proof_clause->PDAG[proof_clause->nb - 2]);
      if (DAG_arg(eq2,orient) != DAG_arg0(eq1))
        proof_error("eq_transitive", proof_clause);
    }
}

/*
  --------------------------------------------------------------
  Clause adding (CNF definitions)
  --------------------------------------------------------------
*/

Tproof
proof_true(void)
/* TRUE */
{
  TDAG DAG = DAG_TRUE;
  Tproof_clause proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause->type = pc_type_true;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_false(void)
/* NOT FALSE */
{
  TDAG DAG = DAG_FALSE;
  Tproof_clause proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause->type = pc_type_false;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_and_pos(TDAG DAG, unsigned i)
/* NOT [A_1 AND ... A_n] OR A_i */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_AND || i >= DAG_arity(DAG))
    proof_error("proof_and_pos", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg(DAG, i)));
  proof_clause->type = pc_type_and_pos;
  proof_clause_add_reason_unsigned(proof_clause, i);
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_and_neg(TDAG DAG)
/* [A_1 AND ... A_n] OR NOT A_1 OR ... NOT A_n */
{
  unsigned i;
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_AND)
    proof_error("proof_and_neg", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  for (i = 0; i < DAG_arity(DAG); i++)
    proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, i))));
  proof_clause->type = pc_type_and_neg;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_or_pos(TDAG DAG)
/* NOT [A_1 OR ... A_n] OR A_1 OR ... NOT A_n */
{
  unsigned i;
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_OR)
    proof_error("proof_or_pos", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  for (i = 0; i < DAG_arity(DAG); i++)
    proof_clause_add(proof_clause, DAG_dup(DAG_arg(DAG, i)));
  proof_clause->type = pc_type_or_pos;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_or_neg(TDAG DAG, unsigned i)
/* [A_1 OR ... A_n] OR NOT A_i */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_OR || i >= DAG_arity(DAG))
    proof_error("proof_or_neg", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, i))));
  proof_clause->type = pc_type_or_neg;
  proof_clause_add_reason_unsigned(proof_clause, i);
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_xor_pos1(TDAG DAG)
/* NOT [A_1 XOR A_2] OR A_1 OR A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_XOR || DAG_arity(DAG) != 2)
    proof_error("proof_xor_pos1", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg1(DAG)));
  proof_clause->type = pc_type_xor_pos1;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_xor_pos2(TDAG DAG)
/* NOT [A_1 XOR A_2] OR NOT A_1 OR NOT A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_XOR || DAG_arity(DAG) != 2)
    proof_error("proof_xor_pos2", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  proof_clause->type = pc_type_xor_pos2;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_xor_neg1(TDAG DAG)
/* [A_1 XOR A_2] OR A_1 OR NOT A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_XOR || DAG_arity(DAG) != 2)
    proof_error("proof_xor_neg1", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  proof_clause->type = pc_type_xor_neg1;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_xor_neg2(TDAG DAG)
/* [A_1 XOR A_2] OR NOT A_1 OR A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_XOR || DAG_arity(DAG) != 2)
    proof_error("proof_xor_neg2", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg1(DAG)));
  proof_clause->type = pc_type_xor_neg2;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_implies_pos(TDAG DAG)
/* NOT[A_1 IMPLIES A_2] OR NOT A_1 OR A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_IMPLIES || DAG_arity(DAG) != 2)
    proof_error("proof_implies_pos", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg1(DAG)));
  proof_clause->type = pc_type_implies_pos;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_implies_neg1(TDAG DAG)
/* [A_1 IMPLIES A_2] OR A_1 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_IMPLIES || DAG_arity(DAG) != 2)
    proof_error("proof_implies_neg1", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause->type = pc_type_implies_neg1;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_implies_neg2(TDAG DAG)
/* [A_1 IMPLIES A_2] OR NOT A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_IMPLIES || DAG_arity(DAG) != 2)
    proof_error("proof_implies_neg2", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  proof_clause->type = pc_type_implies_neg2;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_equiv_pos1(TDAG DAG)
/* NOT [A_1 EQUIV A_2] OR A_1 OR NOT A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_arity(DAG) != 2)
    proof_error("proof_equiv_pos1", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  proof_clause->type = pc_type_equiv_pos1;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_equiv_pos2(TDAG DAG)
/* NOT [A_1 EQUIV A_2] OR NOT A_1 OR A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_arity(DAG) != 2)
    proof_error("proof_equiv_pos2", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg1(DAG)));
  proof_clause->type = pc_type_equiv_pos2;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_equiv_neg1(TDAG DAG)
/* [A_1 EQUIV A_2] OR NOT A_1 OR NOT A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_arity(DAG) != 2)
    proof_error("proof_equiv_neg1", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  proof_clause->type = pc_type_equiv_neg1;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_equiv_neg2(TDAG DAG)
/* [A_1 EQUIV A_2] OR A_1 OR A_2 */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_arity(DAG) != 2)
    proof_error("proof_equiv_neg2", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg1(DAG)));
  proof_clause->type = pc_type_equiv_neg2;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_ite_pos1(TDAG DAG)
/* NOT [IF A THEN B ELSE C] OR A OR C */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_ITE || DAG_arity(DAG) != 3)
    proof_error("proof_ite_pos1", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg(DAG, 0)));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg(DAG, 2)));
  proof_clause->type = pc_type_ite_pos1;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_ite_pos2(TDAG DAG)
/* NOT [IF A THEN B ELSE C] OR NOT A OR B */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_ITE || DAG_arity(DAG) != 3)
    proof_error("proof_ite_pos2", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG)));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 0))));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg(DAG, 1)));
  proof_clause->type = pc_type_ite_pos2;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_ite_neg1(TDAG DAG)
/* [IF A THEN B ELSE C] OR A OR NOT C */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_ITE || DAG_arity(DAG) != 3)
    proof_error("proof_ite_neg1", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_arg(DAG, 0)));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 2))));
  proof_clause->type = pc_type_ite_neg1;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_ite_neg2(TDAG DAG)
/* [IF A THEN B ELSE C] OR NOT A OR NOT B */
{
  Tproof_clause proof_clause = proof_clause_new();
  if (DAG_symb(DAG) != CONNECTOR_ITE || DAG_arity(DAG) != 3)
    proof_error("proof_ite_neg2", NULL);
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 0))));
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 1))));
  proof_clause->type = pc_type_ite_neg2;
  return context_push(proof_clause);
}

/*
  --------------------------------------------------------------
  Clause adding (CNF)
  --------------------------------------------------------------
*/

/*--------------------------------------------------------------*/

/* A_1 AND ... A_i ... AND A_n --> A_i */
Tproof
proof_and(Tproof clause, unsigned i)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_and", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_AND || i >= DAG_arity(DAG))
    proof_error("proof_and", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg(DAG, i)));
  new_proof_clause->type = pc_type_and;
  proof_clause_add_reason(new_proof_clause, clause);
  proof_clause_add_reason_unsigned(new_proof_clause, i);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A_1 OR ... A_i ... OR A_n) --> NOT A_i */
Tproof
proof_not_or(Tproof clause, unsigned i)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_or", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT || DAG_arity(DAG) != 1)
    proof_error("proof_not_or", proof_clause);
  DAG = DAG_arg0(DAG);
  if (DAG_symb(DAG) != CONNECTOR_OR || i >= DAG_arity(DAG))
    proof_error("proof_not_or", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, i))));
  new_proof_clause->type = pc_type_not_or;
  proof_clause_add_reason(new_proof_clause, clause);
  proof_clause_add_reason_unsigned(new_proof_clause, i);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* A_1 OR ... A_n --> {A_1, ... A_n} */
Tproof
proof_or(Tproof clause)
{
  unsigned i;
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_or", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_OR)
    proof_error("proof_or", proof_clause);
  for (i = 0; i < DAG_arity(DAG); i++)
    proof_clause_add(new_proof_clause, DAG_dup(DAG_arg(DAG, i)));
  new_proof_clause->type = pc_type_or;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A_1 AND ... A_n) --> {NOT A_1, ... NOT A_n} */
Tproof
proof_not_and(Tproof clause)
{
  unsigned i;
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_and", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT || DAG_symb(DAG_arg0(DAG)) != CONNECTOR_AND)
    proof_error("proof_not_and", proof_clause);
  DAG = DAG_arg0(DAG);
  for (i = 0; i < DAG_arity(DAG); i++)
    proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, i))));
  new_proof_clause->type = pc_type_not_and;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* A XOR B --> {A, B} */
Tproof
proof_xor1(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_xor1", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_XOR || DAG_arity(DAG) != 2)
    proof_error("proof_xor1", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg1(DAG)));
  new_proof_clause->type = pc_type_xor1;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* A XOR B --> {NOT A, NOT B} */
Tproof
proof_xor2(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_xor2", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_XOR || DAG_arity(DAG) != 2)
    proof_error("proof_xor2", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  new_proof_clause->type = pc_type_xor2;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A XOR B) --> {A, NOT B} */
Tproof
proof_not_xor1(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_xor1", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg0(DAG)) != CONNECTOR_XOR ||
      DAG_arity(DAG_arg0(DAG)) != 2)
    proof_error("proof_not_xor1", proof_clause);
  DAG = DAG_arg0(DAG);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  new_proof_clause->type = pc_type_not_xor1;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A XOR B) --> {NOT A, B} */
Tproof
proof_not_xor2(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_xor2", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg0(DAG)) != CONNECTOR_XOR ||
      DAG_arity(DAG_arg0(DAG)) != 2)
    proof_error("proof_not_xor2", proof_clause);
  DAG = DAG_arg0(DAG);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg1(DAG)));
  new_proof_clause->type = pc_type_not_xor2;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* A IMPLIES B --> {NOT A, B} */
Tproof
proof_implies(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_implies", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_IMPLIES || DAG_arity(DAG) != 2)
    proof_error("proof_implies", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg1(DAG)));
  new_proof_clause->type = pc_type_implies;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A IMPLIES B) --> A */
Tproof
proof_not_implies1(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_implies1", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg0(DAG)) != CONNECTOR_IMPLIES ||
      DAG_arity(DAG_arg0(DAG)) != 2)
    proof_error("proof_not_implies1", proof_clause);
  DAG = DAG_arg0(DAG);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg0(DAG)));
  new_proof_clause->type = pc_type_not_implies1;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A IMPLIES B) --> NOT B */
Tproof
proof_not_implies2(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_implies2", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg0(DAG)) != CONNECTOR_IMPLIES ||
      DAG_arity(DAG_arg0(DAG)) != 2)
    proof_error("proof_not_implies2", proof_clause);
  DAG = DAG_arg0(DAG);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  new_proof_clause->type = pc_type_not_implies2;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* A EQUIV B --> {NOT A, B} */
Tproof
proof_equiv1(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_equiv1", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_arity(DAG) != 2)
    proof_error("proof_equiv1", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg1(DAG)));
  new_proof_clause->type = pc_type_equiv1;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* A EQUIV B --> {A, NOT B} */
Tproof
proof_equiv2(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_equiv2", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_EQUIV || DAG_arity(DAG) != 2)
    proof_error("proof_equiv2", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  new_proof_clause->type = pc_type_equiv2;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A EQUIV B) --> A OR B */
Tproof
proof_not_equiv1(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_equiv1", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg0(DAG)) != CONNECTOR_EQUIV ||
      DAG_arity(DAG_arg0(DAG)) != 2)
    proof_error("proof_not_equiv1", proof_clause);
  DAG = DAG_arg0(DAG);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg0(DAG)));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg1(DAG)));
  new_proof_clause->type = pc_type_not_equiv1;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(A EQUIV B) --> NOT A OR NOT B */
Tproof
proof_not_equiv2(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_equiv2", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg0(DAG)) != CONNECTOR_EQUIV ||
      DAG_arity(DAG_arg0(DAG)) != 2)
    proof_error("proof_not_equiv2", proof_clause);
  DAG = DAG_arg0(DAG);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg0(DAG))));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg1(DAG))));
  new_proof_clause->type = pc_type_not_equiv2;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* IF A THEN B ELSE C --> A OR C */
Tproof
proof_ite1(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_ite1", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_ITE || DAG_arity(DAG) != 3)
    proof_error("proof_ite1", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg(DAG, 0)));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg(DAG, 2)));
  new_proof_clause->type = pc_type_ite1;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* IF A THEN B ELSE C --> NOT A OR B */
Tproof
proof_ite2(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_ite2", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_ITE || DAG_arity(DAG) != 3)
    proof_error("proof_ite2", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 0))));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg(DAG, 1)));
  new_proof_clause->type = pc_type_ite2;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(IF A THEN B ELSE C) --> A OR NOT C */
Tproof
proof_not_ite1(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_ite1", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg(DAG, 0)) != CONNECTOR_ITE ||
      DAG_arity(DAG_arg(DAG, 0)) != 3)
    proof_error("proof_not_ite1", proof_clause);
  DAG = DAG_arg(DAG, 0);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_arg(DAG, 0)));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 2))));
  new_proof_clause->type = pc_type_not_ite1;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

/*--------------------------------------------------------------*/

/* NOT(IF A THEN B ELSE C) --> NOT A OR NOT B */
Tproof
proof_not_ite2(Tproof clause)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  TDAG DAG;
  if (proof_clause->nb != 1)
    proof_error("proof_not_ite2", proof_clause);
  DAG = proof_clause->PDAG[0];
  if (DAG_symb(DAG) != CONNECTOR_NOT ||
      DAG_symb(DAG_arg(DAG, 0)) != CONNECTOR_ITE ||
      DAG_arity(DAG_arg(DAG, 0)) != 3)
    proof_error("proof_not_ite2", proof_clause);
  DAG = DAG_arg(DAG, 0);
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 0))));
  proof_clause_add(new_proof_clause, DAG_dup(DAG_not(DAG_arg(DAG, 1))));
  new_proof_clause->type = pc_type_not_ite2;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

#define TMP_PROOF(A)                                            \
  Tproof                                                        \
  proof_tmp_##A (Tproof clause, TDAG DAG)                       \
  {                                                             \
    Tproof_clause proof_clause = context_get(clause);           \
    Tproof_clause new_proof_clause = proof_clause_new();	\
    if (proof_clause->nb != 1)                                  \
      proof_error("proof_tmp_##A", proof_clause);               \
    proof_clause_add(new_proof_clause, DAG_dup(DAG));           \
    new_proof_clause->type = pc_type_tmp_ ## A;                 \
    proof_clause_add_reason(new_proof_clause, clause);          \
    return context_push(new_proof_clause);                      \
  }                                                             \

/*--------------------------------------------------------------*/

Tproof
proof_tmp_alphaconv(Tproof clause, TDAG DAG)
{
  Tproof_clause proof_clause = context_get(clause);
  Tproof_clause new_proof_clause = proof_clause_new();
  if (proof_clause->nb != 1)
    proof_error("proof_tmp_alphaconv", proof_clause);
  proof_clause_add(new_proof_clause, DAG_dup(DAG));
  new_proof_clause->type = pc_type_tmp_alphaconv;
  proof_clause_add_reason(new_proof_clause, clause);
  return context_push(new_proof_clause);
}

TMP_PROOF(let_elim)
TMP_PROOF(nary_elim)
TMP_PROOF(distinct_elim)
TMP_PROOF(eq_norm)
TMP_PROOF(simp_arith)
TMP_PROOF(ite_elim)
TMP_PROOF(macrosubst)
TMP_PROOF(betared)
TMP_PROOF(bfun_elim)
TMP_PROOF(sk_connector)
TMP_PROOF(pm_process)
TMP_PROOF(qnt_tidy)
TMP_PROOF(qnt_simplify)
TMP_PROOF(skolemize)
TMP_PROOF(LA_pre)

/*
  --------------------------------------------------------------
  SAT solver
  --------------------------------------------------------------
*/

static unsigned clause_id_to_context_size = 0;
static Tproof * clause_id_to_context = NULL;
static Tproof last_context_add = 0;

/*--------------------------------------------------------------*/

static inline void
proof_SAT_set_proof_id(SAT_Tclause clause_id, Tproof proof_id)
{
  unsigned i;
  if (clause_id_to_context_size <= clause_id)
    {
      if (!clause_id_to_context_size)
        {
          clause_id_to_context_size = 1;
          MY_MALLOC(clause_id_to_context,
                    clause_id_to_context_size * sizeof(Tproof));
          clause_id_to_context[0] = 0;
        }
      while (clause_id_to_context_size <= clause_id)
        {
          clause_id_to_context_size *= 2;
          MY_REALLOC(clause_id_to_context,
                     clause_id_to_context_size * sizeof(Tproof));
          for (i = clause_id_to_context_size >> 1;
               i < clause_id_to_context_size;
               i++)
            clause_id_to_context[i] = 0;
        }
    }
  clause_id_to_context[clause_id] = proof_id;
#ifdef DEBUG_PROOF
  fprintf(stderr, "SAT proof id (_%d_): %d\n", clause_id, proof_id);
#endif
}

/*--------------------------------------------------------------*/

static inline Tproof
proof_SAT_get_proof_id(SAT_Tclause clause_id)
{
  if (clause_id >= clause_id_to_context_size)
    return 0;
  return clause_id_to_context[clause_id];
}

/*--------------------------------------------------------------*/

static inline Tproof_clause
proof_SAT_get_proof(SAT_Tclause clause_id)
{
  return context_get(proof_SAT_get_proof_id(clause_id));
}

/*--------------------------------------------------------------*/

void
proof_SAT_reset(void)
{
  memset(clause_id_to_context, 0, clause_id_to_context_size * sizeof(int));
}

/*--------------------------------------------------------------*/

static void
proof_SAT_init(void)
{
  clause_id_to_context_size = 0;
  clause_id_to_context = NULL;
  last_context_add = 0;
}

/*--------------------------------------------------------------*/

static void
proof_SAT_done(void)
{
  clause_id_to_context_size = 0;
  free(clause_id_to_context);
  last_context_add = 0;
}

/*
  --------------------------------------------------------------
  SAT solver (new)
  --------------------------------------------------------------
*/

void
proof_SAT_insert(Tclause clause)
{
  assert (!last_context_add);
  if (clause->proof_id == 0)
    {
      my_warning("Adding a clause without proof\n");
      return;
    }
  last_context_add = clause->proof_id;
}

/*--------------------------------------------------------------*/

void
SAT_proof_set_id(SAT_Tclause clause_id)
{
  proof_SAT_set_proof_id(clause_id, last_context_add);
  last_context_add = 0;
}

/*--------------------------------------------------------------*/

void
SAT_proof_notify(SAT_Tclause clause)
{
  unsigned i;
  Tproof_clause result;
  result =
    proof_clause_resolve(proof_SAT_get_proof(SAT_proof_stack_clause[0]),
                         proof_SAT_get_proof(SAT_proof_stack_clause[1]),
                         var_to_DAG(lit_var(SAT_proof_stack_lit[0])));
  for (i = 2; i < SAT_proof_stack_n; ++i)
    {
      Tproof_clause result_new =
        proof_clause_resolve(result,
                             proof_SAT_get_proof(SAT_proof_stack_clause[i]),
                             var_to_DAG(lit_var(SAT_proof_stack_lit[i - 1])));
      proof_clause_free(&result);
      result = result_new;
    }
  result->type = pc_type_SAT_resolution;
  for (i = 0; i < SAT_proof_stack_n; i++)
    proof_clause_add_reason(result,
                            proof_SAT_get_proof_id(SAT_proof_stack_clause[i]));
  proof_SAT_set_proof_id(clause, context_push(result));
}

/*
  --------------------------------------------------------------
  Lemmas
  --------------------------------------------------------------
*/

typedef struct TSproof_lemma
{
  TDAG DAG;
  Tproof proof_id;
} * Tproof_lemma;

static Thash lemma_hash;

/*--------------------------------------------------------------*/

static Tproof_lemma
lemma_hash_new(TDAG DAG, Tproof proof_id)
{
  Tproof_lemma proof_lemma;
  MY_MALLOC(proof_lemma, sizeof(struct TSproof_lemma));
  proof_lemma->DAG = DAG_dup(DAG);
  proof_lemma->proof_id = proof_id;
  return proof_lemma;
}

/*--------------------------------------------------------------*/

static unsigned int
lemma_hash_function(Tproof_lemma proof_lemma)
{
  return DAG_key(proof_lemma->DAG);
}

/*--------------------------------------------------------------*/

static unsigned int
lemma_hash_equal(Tproof_lemma proof_lemma1, Tproof_lemma proof_lemma2)
{
  return proof_lemma1->DAG == proof_lemma2->DAG;
}

/*--------------------------------------------------------------*/

static void
lemma_hash_free(Tproof_lemma proof_lemma)
{
  DAG_free(proof_lemma->DAG);
  free(proof_lemma);
}

/*--------------------------------------------------------------*/

static void
proof_lemma_init(void)
{
  lemma_hash = hash_new(100, (TFhash) lemma_hash_function,
                        (TFequal) lemma_hash_equal,
                        (TFfree) lemma_hash_free);
}

/*--------------------------------------------------------------*/

static void
proof_lemma_done(void)
{
  hash_free(&lemma_hash);
}

/*--------------------------------------------------------------*/

static void
proof_lemma_push(TDAG DAG, Tproof proof_id)
{
  hash_insert(lemma_hash, lemma_hash_new(DAG, proof_id));
}

/*--------------------------------------------------------------*/

static Tproof
proof_lemma_get(TDAG DAG)
{
  struct TSproof_lemma Sproof_lemma;
  Tproof_lemma proof_lemma;
  Sproof_lemma.DAG = DAG;
  Sproof_lemma.proof_id = 0;
  proof_lemma = hash_lookup(lemma_hash, &Sproof_lemma);
  if (proof_lemma)
    return proof_lemma->proof_id;
  return 0;
}

/*
  --------------------------------------------------------------
  unsat-core output
  --------------------------------------------------------------
*/

/*--------------------------------------------------------------*/
static Tstack_DAG hypotheses = NULL; /**< already printed hypotheses */
static bool hypothesis_first; /**< first hypothesis is to be printed */

/*--------------------------------------------------------------*/

/**
   \author David Deharbe
   \brief handler for clauses of type pc_type_input in
   proof_clause_hyp
   \param file the file to write to
   \seealso proof_clause_hyp proof_hyp */
static void
proof_clause_hyp_input(Tproof_clause proof_clause, FILE * file)
{
  char ** Pname;
  assert(proof_clause->type == pc_type_input);

  if (DAG_tmp_bool[proof_clause->PDAG[0]])
    return;
  if (proof_clause->nb != 1)
    my_error("proof_clause_hyp: internal error\n");
  Pname = DAG_prop_get(proof_clause->PDAG[0], DAG_PROP_NAMED);
  if (!Pname)
    return;
  stack_push(hypotheses, proof_clause->PDAG[0]);
  DAG_tmp_bool[proof_clause->PDAG[0]] = true;
  fprintf(file, hypothesis_first?"%s":" %s", *Pname);
  hypothesis_first = false;
}

/*--------------------------------------------------------------*/

/**
   \author David Deharbe
   \brief prints hypothesis label found in proof clause
   (in response to SMT command get-unsat-core)
   \param proof_clause the proof clause
   \param id the proof clause id
   \param file the file to write to
   \param first the first hypothesis is yet to be printed
   \seealso proof_clause proof_hyp  */
static void
proof_clause_hyp(Tproof_clause proof_clause, FILE * file)
{
  if (proof_clause->type == pc_type_input)
    {
      proof_clause_hyp_input(proof_clause, file);
    }
  else if (proof_clause->type == pc_type_subproof)
    {
      unsigned i;
      Ttable old_context = context;
      context = ((Tproof_clause_subproof) proof_clause)->context;
      for (i = 1; i < table_length(context); i++)
        proof_clause_hyp((Tproof_clause) table_get(context,i), file);
      context = old_context;
    }
  else
    {
      unsigned n = proof_clause->argc;
      if (proof_clause->type == pc_type_and_pos ||
          proof_clause->type == pc_type_or_neg ||
          proof_clause->type == pc_type_and ||
          proof_clause->type == pc_type_not_or)
        {
          if (!proof_clause->argc)
            my_error("proof_clause_print_hyp: internal error\n");
          n--;
        }
      /* gen_clause */
      if (n)
        {
          unsigned i;
          for (i = 0; i < n; i++)
            {
              Tproof_clause proof_clause2 = (Tproof_clause)
                context_get(proof_clause->argv[i]);
              if (proof_clause2->type == pc_type_input)
                proof_clause_hyp_input(proof_clause2, file);
            }
        }
    }
}

/*--------------------------------------------------------------*/

void
proof_hyp(FILE * file)
{
  unsigned i;
  /* the proof tree is first reduced (this is optional) */
  context_merge();
  context_prune();
  /* initialization of variables used to avoid duplicates */
  DAG_tmp_reserve();
  stack_INIT(hypotheses);
  /* print hypotheses found in each proof clause */
  fprintf(file, "(");
  hypothesis_first = true;
  for (i = 1; i < table_length(context); i++)
    proof_clause_hyp((Tproof_clause) context_get(i), file);
  fprintf(file, ")\n");
  /* finalization of variables used to avoid duplicates */
  for (i = 0; i < hypotheses->size; ++i)
    DAG_tmp_bool[hypotheses->data[i]] = 0;
  stack_free(hypotheses);
  DAG_tmp_release();
}

/*
  --------------------------------------------------------------
  Proof output
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief prints proof clause (for outputting the proof and debugging purposes)
   \param proof_clause the proof clause
   \param id the proof clause id
   \param file the file to write to */
static void
proof_clause_print_v1(Tproof_clause proof_clause, Tproof id, FILE * file)
{
  unsigned i;
  if (proof_clause->type == pc_type_input)
    {
      char ** Pname = DAG_prop_get(proof_clause->PDAG[0], DAG_PROP_NAMED);
      if (proof_clause->nb != 1)
        my_error("proof_clause_print: internal error\n");
      Pname = DAG_prop_get(proof_clause->PDAG[0], DAG_PROP_NAMED);
      if (Pname)
        return;
    }
  fprintf(file, "(set .c%d ", id);
  if (proof_clause->type == pc_type_subproof)
    {
      Ttable old_context = context;
      context = ((Tproof_clause_subproof) proof_clause)->context;
      fprintf(file, "(subproof \n");
      for (i = 1; i < table_length(context); i++)
        proof_clause_print_v1((Tproof_clause) table_get(context,i), i, file);
      context = old_context;
    }
  else
    {
      unsigned n = proof_clause->argc;
      if (proof_clause->type == pc_type_and_pos ||
          proof_clause->type == pc_type_or_neg ||
          proof_clause->type == pc_type_and ||
          proof_clause->type == pc_type_not_or)
        {
          if (!proof_clause->argc)
            my_error("proof_clause_print: internal error\n");
          n--;
        }
      /* gen_clause */
      fprintf(file, "(%s ", pc_type_desc[proof_clause->type].name);
      if (n)
        {
          fprintf(file, ":clauses (");
          for (i = 0; i < n; i++)
            {
              Tproof_clause proof_clause2 = (Tproof_clause)
                context_get(proof_clause->argv[i]);
              if (proof_clause2->type == pc_type_input)
                {
                  char ** Pname;
                  if (proof_clause2->nb != 1)
                    my_error("proof_clause_print: internal error\n");
                  Pname = DAG_prop_get(proof_clause2->PDAG[0], DAG_PROP_NAMED);
                  if (Pname)
                    {
                      fprintf(file, i?" %s":"%s", *Pname);
                      continue;
                    }
                }
              fprintf(file, i?" .c%d":".c%d", proof_clause->argv[i]);
            }
          fprintf(file, ") ");
        }
    }
  if (proof_clause->na)
    {
      fprintf(file, ":args (");
      for (i = 0; i < proof_clause->na; i++)
        {
          if (i) fprintf(file, " ");
          if (!proof_clause->PDAG[proof_clause->nb + i])
            {
              fprintf(file, "()");
              continue;
            }
          if (option_proof_with_sharing)
            DAG_fprint_sharing(file, proof_clause->PDAG[proof_clause->nb + i]);
          else
            DAG_fprint(file, proof_clause->PDAG[proof_clause->nb + i]);
        }
      fprintf(file, ") "); /* conclusion */
    }
  fprintf(file, ":conclusion (");
  for (i = 0; i < proof_clause->nb; i++)
    {
      if (i) fprintf(file, " ");
      if (option_proof_with_sharing)
        DAG_fprint_sharing(file, proof_clause->PDAG[i]);
      else
        DAG_fprint(file, proof_clause->PDAG[i]);
    }
  fprintf(file, ")"); /* conclusion */
  fprintf(file, ")"); /* gen_clause */
  fprintf(file, ")\n"); /* set */
}

/*--------------------------------------------------------------*/

static void
proof_out_v2(FILE * file)
{
  unsigned i;
  if (option_proof_prune)
    {
      if (option_proof_merge)
        context_merge();
      context_prune();
    }
  for (i = 1; i < table_length(context); i++)
    proof_clause_print_v1((Tproof_clause) context_get(i), i, file);
  if (option_proof_with_sharing)
    for (i = 1; i < table_length(context); i++)
      proof_clause_reset_misc((Tproof_clause) context_get(i));
}

/*--------------------------------------------------------------*/

static void
proof_out_v1(FILE * file)
{
  unsigned i;
  for (i = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = (Tproof_clause) context_get(i);
      if (proof_clause->type == pc_type_th_resolution)
        proof_clause->type = pc_type_SAT_resolution;
    }
  proof_out_v2(file);
}

/*--------------------------------------------------------------*/

static void
proof_out_v0(FILE * file)
{
  unsigned i;
  if (option_proof_prune)
    {
      if (option_proof_merge)
        context_merge();
      context_prune();
    }
  for (i = 1; i < table_length(context); i++)
    {
      Tproof_clause proof_clause = (Tproof_clause) context_get(i);
      if (proof_clause->type == pc_type_th_resolution)
        proof_clause->type = pc_type_SAT_resolution;
    }
  for (i = 1; i < table_length(context); i++)
    proof_clause_print((Tproof_clause) context_get(i), i, file);
  if (option_proof_with_sharing)
    for (i = 1; i < table_length(context); i++)
      proof_clause_reset_misc((Tproof_clause) context_get(i));
}

/*
  --------------------------------------------------------------
  Statistics
  --------------------------------------------------------------
*/

static unsigned
proof_size(void)
{
  unsigned i;
  unsigned size = 0;
  for (i = 1; i < table_length(context); i++)
    size += ((Tproof_clause) context_get(i))->nb;
  return size;
}

/*--------------------------------------------------------------*/

static unsigned
proof_length(void)
{
  return table_length(context);
}

/*--------------------------------------------------------------*/

static void
proof_stat_compute(void)
{
  unsigned stat_proof_time;
  unsigned stat_proof_length;
  unsigned stat_proof_size;
  unsigned stat_proof_length_pruned;
  unsigned stat_proof_size_pruned;
  unsigned stat_proof_length_merged;
  unsigned stat_proof_size_merged;
  stat_proof_time =
    stats_timer_new("proof_time", "Time to compute proof stats", "%7.2f",
                    STATS_TIMER_ALL);
  stat_proof_length =
    stats_counter_new("proof_length", "Number of proof steps", "%7d");
  stat_proof_size =
    stats_counter_new("proof_size", "Number of literals in proof", "%7d");
  stat_proof_length_pruned =
    stats_counter_new("proof_length_pruned", "Number of proof steps (pruned)",
                      "%7d");
  stat_proof_size_pruned =
    stats_counter_new("proof_size_pruned",
                      "Number of literals in proof (pruned)", "%7d");
  stat_proof_length_merged =
    stats_counter_new("proof_length_merged",
                      "Number of proof steps (merged)", "%7d");
  stat_proof_size_merged =
    stats_counter_new("proof_size_merged",
                      "Number of literals in proof (merged)", "%7d");
  stats_timer_start(stat_proof_time);
  stats_counter_set(stat_proof_length, (int) proof_length());
  stats_counter_set(stat_proof_size, (int) proof_size());
  context_prune();
  stats_counter_set(stat_proof_length_pruned, (int) proof_length());
  stats_counter_set(stat_proof_size_pruned, (int) proof_size());
  context_merge();
  context_prune();
  stats_counter_set(stat_proof_length_merged, (int) proof_length());
  stats_counter_set(stat_proof_size_merged, (int) proof_size());
  stats_timer_stop(stat_proof_time);
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

Tproof
proof_add_formula(TDAG DAG)
{
  Tproof_clause proof_clause = proof_clause_new();
  TDAG tmp = DAG;
  while (DAG_symb(tmp) == CONNECTOR_NOT &&
         DAG_symb(DAG_arg0(tmp)) == CONNECTOR_NOT)
    {
      char ** Pname = DAG_prop_get(tmp, DAG_PROP_NAMED);
      if (Pname)
        {
          char * name = strmake(*Pname);
          DAG_prop_set(DAG_arg0(DAG_arg0(tmp)), DAG_PROP_NAMED, &name);
        }
      tmp = DAG_arg0(DAG_arg0(tmp));
    }
  proof_clause_add(proof_clause, DAG);
  proof_clause->type = pc_type_input;
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_add_disequality_lemma(TDAG DAG)
{
  Tproof_clause proof_clause;
  Tproof proof_id = proof_lemma_get(DAG);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG);
  proof_clause->type = pc_type_disequality_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_totality_lemma(TDAG DAG)
{
  Tproof_clause proof_clause;
  Tproof proof_id = proof_lemma_get(DAG);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG);
  proof_clause->type = pc_type_totality_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_arith_lemma(TDAG DAG)
{
  Tproof_clause proof_clause;
  Tproof proof_id = proof_lemma_get(DAG);
  if (proof_id)
    {
      DAG_free(DAG);
      return proof_id;
    }
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG);
  proof_clause->type = pc_type_arith_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_forall_inst_lemma(TDAG DAG, unsigned n, TDAG * PDAG)
{
  unsigned i;
  Tproof_clause proof_clause;
  Tproof proof_id;
  proof_id = proof_lemma_get(DAG);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause->type = pc_type_forall_inst_lemma;
  for (i = 0; i < n; i++)
    {
      if (PDAG[i])
        DAG_dup(PDAG[i]);
      proof_clause_add_DAG_arg(proof_clause, PDAG[i]);
    }
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_exists_inst_lemma(TDAG DAG, unsigned n, TDAG * PDAG)
{
  unsigned i;
  Tproof_clause proof_clause;
  Tproof proof_id;
  proof_id = proof_lemma_get(DAG);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause->type = pc_type_exists_inst_lemma;
  proof_id = context_push(proof_clause);
  for (i = 0; i < n; i++)
    {
      if (PDAG[i])
        DAG_dup(PDAG[i]);
      proof_clause_add_DAG_arg(proof_clause, PDAG[i]);
    }
  proof_lemma_push(DAG, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_skolem_ex_lemma(TDAG DAG1, TDAG DAG2)
{
  Tproof_clause proof_clause;
  Tproof proof_id;
  TDAG DAG3;

  assert(quantifier(DAG_symb(DAG1)));
  DAG3 = DAG_implies(DAG1, DAG2);
  proof_id = proof_lemma_get(DAG3);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG1)));
  proof_clause_add(proof_clause, DAG_dup(DAG2));
  proof_clause->type = pc_type_skolem_ex_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG3, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_skolem_all_lemma(TDAG DAG1, TDAG DAG2)
{
  Tproof_clause proof_clause;
  Tproof proof_id;
  TDAG DAG3;

  assert(quantifier(DAG_symb(DAG1)));
  DAG3 = DAG_implies(DAG2, DAG1);
  proof_id = proof_lemma_get(DAG3);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG2)));
  proof_clause_add(proof_clause, DAG_dup(DAG1));
  proof_clause->type = pc_type_skolem_all_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG3, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_qnt_simp_lemma(TDAG DAG1, TDAG DAG2)
{
  Tproof_clause proof_clause;
  Tproof proof_id;
  TDAG DAG3;

  assert(quantifier(DAG_symb(DAG1)));
  DAG3 = DAG_implies(DAG1, DAG2);
  proof_id = proof_lemma_get(DAG3);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG1)));
  proof_clause_add(proof_clause, DAG_dup(DAG2));
  proof_clause->type = pc_type_qnt_simp_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG3, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_qnt_merge_lemma(TDAG DAG1, TDAG DAG2)
{
  Tproof_clause proof_clause;
  Tproof proof_id;
  TDAG DAG3;

  assert(quantifier(DAG_symb(DAG1)));
  DAG3 = DAG_implies(DAG1, DAG2);
  proof_id = proof_lemma_get(DAG3);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG_not(DAG1)));
  proof_clause_add(proof_clause, DAG_dup(DAG2));
  proof_clause->type = pc_type_qnt_merge_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG3, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_add_fol_lemma(TDAG DAG)
{
  Tproof_clause proof_clause;
  Tproof proof_id = proof_lemma_get(DAG);
  if (proof_id)
    return proof_id;
  proof_clause = proof_clause_new();
  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause->type = pc_type_fol_lemma;
  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG, proof_id);
  return proof_id;
}

/*--------------------------------------------------------------*/

Tproof
proof_get_lemma_id(TDAG DAG)
{
  Tproof proof_id = proof_lemma_get(DAG);
  if (!proof_id)
    my_error("proof_get_lemma_id: no lemma\n");
  return proof_id;
}

/*--------------------------------------------------------------*/

void
proof_set_lemma_id(TDAG DAG, Tproof id)
{
  Tproof_clause pc;
  if (!context)
    my_error("no context\n");
  if (list_length(context_list) != 1)
    my_error("not available in subproof\n");
  pc = context_get(id);
  if (pc->nb != 1 || pc->PDAG[0] != DAG)
    my_error("proof_set_lemma_id: proof error\n");
  proof_lemma_push(DAG, id);
}

/*--------------------------------------------------------------*/

/* PF add a valid clause, and returns its context id
   arguments (and elmnts of lits) are DAGs
   Implemented for eq_* */
Tproof
proof_clause(Tproof_type type, unsigned nb_lits, ...)
{
  unsigned i;
  va_list adpar;
  Tproof_clause proof_clause = proof_clause_new();
  va_start(adpar, nb_lits);
  for (i = 0; i < nb_lits; i++)
    proof_clause_add(proof_clause, va_arg(adpar, TDAG));

  switch (type)
    {
    case eq_congruent_pred :
      proof_check_eq_congruent_pred(proof_clause);
      proof_clause->type = pc_type_eq_congruent_pred;
      break;
    case eq_congruent :
      proof_check_eq_congruent(proof_clause);
      proof_clause->type = pc_type_eq_congruent;
      break;
    case eq_transitive :
      proof_check_eq_transitive(proof_clause);
      proof_clause->type = pc_type_eq_transitive;
      break;
    case eq_reflexive :
      proof_check_eq_reflexive(proof_clause);
      proof_clause->type = pc_type_eq_reflexive;
      break;
    case eq_congruent_general :
      proof_clause->type = pc_type_eq_congruent_general;
      break;
    case p_distinct_elim :
      proof_clause->type = pc_type_distinct_elim;
      break;
    case p_chainable_elim :
      proof_clause->type = pc_type_chainable_elim;
      break;
    case p_right_assoc_elim :
      proof_clause->type = pc_type_right_assoc_elim;
      break;
    case p_left_assoc_elim :
      proof_clause->type = pc_type_left_assoc_elim;
      break;
    case p_la_rw_eq :
      proof_clause->type = pc_type_la_rw_eq;
      break;
    case la_generic :
      /*      proof_check_la_generic(proof_clause); */
      proof_clause->type = pc_type_la_generic;
      break;
    case lia_generic :
      /*      proof_check_lia_generic(proof_clause); */
      proof_clause->type = pc_type_lia_generic;
      break;
    case nla_generic :
      /*      proof_check_nla_generic(proof_clause); */
      proof_clause->type = pc_type_nla_generic;
      break;
    default :
      my_error("proof_deduce: unknown type\n");
    }
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

/* PF add a valid clause, and returns its context id
   arguments (and elmnts of lits) are DAGs
   Implemented for eq_* */
Tproof
proof_clause_stack(Tproof_type type, Tstack_DAG lits)
{
  unsigned i;
  Tproof_clause proof_clause = proof_clause_new();
  for (i = 0; i < lits->size; i++)
    proof_clause_add(proof_clause, DAG_dup(lits->data[i]));
#ifdef DEBUG_PROOF
  my_message("proof_clause_list: input clause:\n");
  proof_clause_print(proof_clause, 0, stderr);
#endif
  switch (type)
    {
    case eq_congruent_pred :
      proof_check_eq_congruent_pred(proof_clause);
      proof_clause->type = pc_type_eq_congruent_pred;
      break;
    case eq_congruent :
      proof_check_eq_congruent(proof_clause);
      proof_clause->type = pc_type_eq_congruent;
      break;
    case eq_transitive :
      proof_check_eq_transitive(proof_clause);
      proof_clause->type = pc_type_eq_transitive;
      break;
    case eq_congruent_general :
      proof_clause->type = pc_type_eq_congruent_general;
      break;
    case p_distinct_elim :
      proof_clause->type = pc_type_distinct_elim;
      break;
    case p_chainable_elim :
      proof_clause->type = pc_type_chainable_elim;
      break;
    case p_right_assoc_elim :
      proof_clause->type = pc_type_right_assoc_elim;
      break;
    case p_left_assoc_elim :
      proof_clause->type = pc_type_left_assoc_elim;
      break;
    case p_la_rw_eq :
      proof_clause->type = pc_type_la_rw_eq;
      break;
    case la_generic :
      /*      proof_check_la_generic(proof_clause); */
      proof_clause->type = pc_type_la_generic;
      break;
    case lia_generic :
      /*      proof_check_lia_generic(proof_clause); */
      proof_clause->type = pc_type_lia_generic;
      break;
    case nla_generic :
      /*      proof_check_la_generic(proof_clause); */
      proof_clause->type = pc_type_nla_generic;
      break;
    default :
      my_error("proof_deduce: unknown type\n");
    }
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

#ifdef SAT_MINISAT
void
proof_clause_check(Tclause clause)
{
  int i;
  Tclause clause2;
  Tproof_clause proof_clause;
#ifdef DEBUG_PROOF
  my_message("Checking clause:\n");
  clause_symb_fprint(stderr, clause);
#endif
  if (clause->proof_id == 0)
    {
      my_warning("Adding a clause without proof\n");
      return;
    }
  last_context_add = clause->proof_id;
  proof_clause = context_get(clause->proof_id);
  clause2 = clause_new(proof_clause->nb);
  for (i = 0; i < proof_clause->nb; i++)
    clause_set_literal(clause2, i,
                       DAG_to_lit(proof_clause->PDAG[i]));
  clause_clean(clause2);
  if (!clause_same(clause, clause2))
    {
      my_message("Clause added to SAT solver: \n");
      clause_symb_fprint(stderr, clause);
      clause_fprint(stderr, clause);
      my_message("Computed clause: \n");
      clause_symb_fprint(stderr, clause2);
      clause_fprint(stderr, clause2);
      my_error("Proof does not seem to provide added clause\n");
    }
  clause_free(clause2);
}
#endif

/*--------------------------------------------------------------*/

Tproof_clause * Pproof_clause_tmp = NULL;
unsigned Pproof_clause_tmp_nb = 0;

/* PF
   It would be nice to change n-resolution in 2-resolution.
   1. Identify atoms that are explained
   In fact those atoms that appear positively and negatively
   2. Use flag to assign a number to each atom
   3. For each explained atom, associate a clause, explanation[atom],
   that explains it
   4. For each explained atom A, associate a list of clauses A.clauses
   requiring explanation
   5. Associate to each clause C a number C.depth initialised to 0
   and the explained atom C.expl
   6. The first clause does not require an explanation (conflict)
   7. For the first clause C, call N(C)

   N(C)
   {
   if (C.depth > 0) return;
   For each C' in (C.expl).clauses
   {
   N(C');
   C.depth = max(C.depth, C'.depth);
   }
   }
   8. Sort clauses according to depth
   9. Binary resolve the first clause with clauses of increasing depth
*/

Tproof
proof_resolve_array(unsigned nb_clauses, Tproof * clauses)
{
  unsigned i, j;
  Tproof_clause proof_clause;
  if (nb_clauses < 1)
    proof_error("proof_resolve_array", NULL);
  if (nb_clauses == 1)
    {
      if (clauses[0] == 0)
        proof_error("proof_resolve_array", NULL);
      return clauses[0];
    }
  proof_clause = proof_clause_new();
#ifdef DEBUG_PROOF
  my_message("Resolving from\n");
  for (i = 0; i < nb_clauses; i++)
    my_message("  clause %d\n", clauses[i]);
#endif
  if (nb_clauses > Pproof_clause_tmp_nb)
    {
      MY_REALLOC(Pproof_clause_tmp, nb_clauses * sizeof(Tproof_clause));
      Pproof_clause_tmp_nb = nb_clauses;
    }
  for (i = 0; i < nb_clauses; i++)
    if (clauses[i] == 0)
      proof_error("proof_resolve_array", NULL);
    else
      Pproof_clause_tmp[i] = context_get(clauses[i]);
  for (i = 0; i < nb_clauses; i++)
    for (j = 0; j < Pproof_clause_tmp[i]->nb; j++)
      {
        TDAG DAG = (Pproof_clause_tmp[i])->PDAG[j];
        TDAG DAG2 = DAG_atom(DAG);
        DAG_misc_set(DAG2, DAG_misc(DAG2) | 1 << DAG_polarity(DAG));
      }
  for (i = 0; i < nb_clauses; i++)
    for (j = 0; j < Pproof_clause_tmp[i]->nb; j++)
      {
        if (DAG_misc(DAG_atom(Pproof_clause_tmp[i]->PDAG[j])) == 1 ||
            DAG_misc(DAG_atom(Pproof_clause_tmp[i]->PDAG[j])) == 2)
          proof_clause_add(proof_clause,
                           DAG_dup(Pproof_clause_tmp[i]->PDAG[j]));
        DAG_misc_set(DAG_atom(Pproof_clause_tmp[i]->PDAG[j]), 0);
      }

  proof_clause->type = pc_type_th_resolution;
  for (i = 0; i < nb_clauses; i++)
    proof_clause_add_reason(proof_clause, clauses[i]);
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/

Tproof
proof_resolve(unsigned nb_clauses, ...)
{
  unsigned i;
  va_list adpar;
  Tproof * clauses;
  MY_MALLOC(clauses, nb_clauses * sizeof(Tproof));
  if (nb_clauses < 1)
    proof_error("proof_resolve_array", NULL);
  va_start(adpar, nb_clauses);
  for (i = 0; i < nb_clauses; i++)
    clauses[i] = va_arg(adpar, Tproof);
  va_end(adpar);
  i = proof_resolve_array(nb_clauses, clauses);
  free(clauses);
  return i;
}

/*--------------------------------------------------------------*/

Tproof
proof_bin_resolve(Tproof i_clause1, Tproof i_clause2)
{
  unsigned i;
  int tmp;
  Tproof_clause proof_clause = proof_clause_new();
  Tproof_clause clause1, clause2;
  if (!i_clause1 || !i_clause2)
    proof_error("proof_bin_resolve", NULL);
#ifdef DEBUG_PROOF
  my_message("Binary resolving from\n");
  my_message("  clause %d\n", i_clause1);
  my_message("  clause %d\n", i_clause2);
#endif
  clause1 = context_get(i_clause1);
  clause2 = context_get(i_clause2);
  /* PF count polarities.  The misc field of DAGs is used
     876543210
     bit 0 : DAG is used with negative polarity in clause1
     bit 1 : DAG is used with positive polarity in clause1
     bit 2 : DAG is used with negative polarity in clause2
     bit 3 : DAG is used with positive polarity in clause2
     bit 4 : DAG is resolvent
  */
  for (i = 0; i < clause1->nb; i++)
    {
      TDAG DAG = DAG_atom(clause1->PDAG[i]);
      DAG_misc_set(DAG, DAG_misc(DAG) | 1 << DAG_polarity(clause1->PDAG[i]));
    }
  for (i = 0; i < clause2->nb; i++)
    {
      TDAG DAG = DAG_atom(clause2->PDAG[i]);
      DAG_misc_set(DAG, DAG_misc(DAG) | 1 << (DAG_polarity(clause2->PDAG[i]) + 2));
    }
  /* PF find resolvent
     Not merged with previous step for clarity
     Optimize if required */
  for (i = 0; i < clause1->nb; i++)
    {
      tmp = DAG_misc(DAG_atom(clause1->PDAG[i]));
      if ((tmp & 1) && (tmp & (1 << 3)))
        {
          DAG_misc_set(DAG_atom(clause1->PDAG[i]), (1 << 4) | (1 << 3) | 1);
          break;
        }
      else if ((tmp & (1 << 1)) && (tmp & (1 << 2)))
        {
          DAG_misc_set(DAG_atom(clause1->PDAG[i]), (1 << 4) | (1 << 1) | (1 << 2));
          break;
        }
    }
  if (i == clause1->nb)
    {
      my_message("Binary resolving from\n");
      my_message("  clause %d\n", i_clause1);
      my_message("  clause %d\n", i_clause2);
      my_error("Nothing to resolve\n");
    }
  /* PF now build new clause */
  tmp = 0;
  for (i = 0; i < clause1->nb; i++)
    if (!tmp &&
        (DAG_misc(DAG_atom(clause1->PDAG[i])) & (1 << 4)) &&
        (DAG_misc(DAG_atom(clause1->PDAG[i])) &
         (1 << DAG_polarity(clause1->PDAG[i]))))
      tmp = 1;
    else
      proof_clause_add(proof_clause, DAG_dup(clause1->PDAG[i]));
  if (!tmp)
    my_error ("proof_bin_resolve: internal error\n");

  tmp = 0;
  for (i = 0; i < clause2->nb; i++)
    if (!tmp &&
        (DAG_misc(DAG_atom(clause2->PDAG[i])) & (1 << 4)) &&
        (DAG_misc(DAG_atom(clause2->PDAG[i])) &
         (1 << (DAG_polarity(clause2->PDAG[i]) + 2))))
      tmp = 1;
    else
      proof_clause_add(proof_clause, DAG_dup(clause2->PDAG[i]));
  if (!tmp)
    my_error("proof_bin_resolve: internal error\n");
  /* PF reinitialise misc */
  for (i = 0; i < clause1->nb; i++)
    DAG_misc_set(DAG_atom(clause1->PDAG[i]), 0);
  for (i = 0; i < clause2->nb; i++)
    DAG_misc_set(DAG_atom(clause2->PDAG[i]), 0);
  proof_clause->type = pc_type_th_resolution;
  proof_clause_add_reason(proof_clause, i_clause1);
  proof_clause_add_reason(proof_clause, i_clause2);
  return context_push(proof_clause);
}

/*--------------------------------------------------------------*/
#if OLDPROOF

Tproof
proof_deep_res(TDAG DAG, Tproof formula, Tstack_proof table)
{
  unsigned i;
  Tproof_clause proof_clause = proof_clause_new();
  Tproof proof_id;

  if (!stack_size(table))
    proof_error("proof_deep_res", NULL);

  proof_clause_add(proof_clause, DAG_dup(DAG));
  proof_clause->type = pc_type_deep_res;
  proof_clause_add_reason(proof_clause, formula);
  for (i = 0; i < stack_size(table); i++)
    proof_clause_add_reason(proof_clause, stack_size(table, i));

  proof_id = context_push(proof_clause);
  proof_lemma_push(DAG, proof_id);

  return proof_id;
}

#endif
/*--------------------------------------------------------------*/

void
proof_satisfiable(void)
{
  if (empty_clause)
    my_warning("proof_satisfiable: empty clause derived\n");
  if (status != OPEN)
    my_warning("proof_satisfiable: status not open\n");
  status = SAT;
}

/*--------------------------------------------------------------*/

void
proof_unsatisfiable(void)
{
  if (!empty_clause)
    my_error("proof_unsatifiable: no empty clause derived\n");
  if (status != OPEN)
    my_warning("proof_unsatifiable: status not open\n");
  status = UNSAT;
}

/*--------------------------------------------------------------*/

void
proof_subproof_begin(void)
{
  context_subproof_begin();
}

/*--------------------------------------------------------------*/

Tproof
proof_subproof_end(void)
{
  return context_subproof_end();
}

/*--------------------------------------------------------------*/

void
proof_subproof_remove(void)
{
  context_subproof_remove();
}

/*--------------------------------------------------------------*/

void
proof_init(void)
{
  options_new_int(0, "proof-version",
                  "Proof format version", "(0|1|2)",
                  &option_proof_version);
  options_new_string(0, "proof",
                     "Sets a file name to output proof (- for stdout)",
                     "filename",
                     &option_proof_filename);
  options_new(0, "proof-with-sharing",
              "Use sharing in the output proof",
              &option_proof_with_sharing);
  options_new(0, "proof-prune",
              "Prune the proof of unused deduction",
              &option_proof_prune);
  options_new(0, "proof-merge",
              "Merge identical clauses in the proof",
              &option_proof_merge);
  options_new (0, "proof-file-from-input",
               "Use filename+.proof as output file",
               &option_proof_file_from_input);
  /* TODO make proof stat compatible with proof output */
  options_new (0, "proof-stats",
               "Output proof statistics (incompatible with actual proof output)",
               &option_proof_stat);

  context_init();
  proof_SAT_init();
  proof_lemma_init();
}

/*--------------------------------------------------------------*/

void
proof_out(FILE * file)
{
  switch (option_proof_version)
    {
    case 0:
      proof_out_v0(file);
      break;
    case 1:
      proof_out_v1(file);
      break;
    case 2:
      proof_out_v2(file);
      break;
    default:
      my_error("proof_out: unknown version\n");
    }
}

/*--------------------------------------------------------------*/

void
proof_doc(FILE * file)
{
  int i;
  fprintf(file, "The proof format is a sequence of lines\n"
          "    n:(type clause clause_ids params)\nwhere\n"
          " - n is a number (starting from 1).  It is the identifier of the deduced clause\n"
          " - type is a deduction type\n"
          " - clause is a list (L1 ... Lm) of the literals in the clause\n"
          " - clause_ids is a (possibly empty) sequence of clause identifiers\n"
          " - params is a (possibly empty) sequence of integers.\n"
          "   The number of those (clause_ids and params) arguments depend on the type\n"
          "The following types are currently output\n");

  for (i = 1; i < PC_TYPE_MAX; i++)
    fprintf(file, " * %-17s : %s\n",
            pc_type_desc[i].name, pc_type_desc[i].descr);

  fprintf(file, "The following deduction types require exactly one clause_id argument:\n");
  for (i = 1; i < PC_TYPE_MAX; i++)
    if (pc_type_desc[i].nb_reasons == 1)
      fprintf(file, " * %-17s\n", pc_type_desc[i].name);
  fprintf(file, "The following deduction types may have any number of clause_id arguments:\n");
  for (i = 1; i < PC_TYPE_MAX; i++)
    if (pc_type_desc[i].nb_reasons == -1)
      fprintf(file, " * %-17s\n", pc_type_desc[i].name);
  fprintf(file, "The following deduction types require exactly one integer parameter:\n");
  for (i = 1; i < PC_TYPE_MAX; i++)
    if (pc_type_desc[i].nb_params == 1)
      fprintf(file, " * %-17s\n", pc_type_desc[i].name);

  fprintf(file, "\n");
  fprintf(file, "Please notice that\n"
          " - double negations are silently simplified\n"
          " - clauses are silently simplified to eliminate repeated"
          " literals\n"
          " - clauses with complementary literals are silently simplified"
          " to true\n"
          " - symmetry and reflexivity of equality is silently used\n\n");

  fprintf(file, "Currently, QF_UF/QF_IDL/QF_RDL/QF_UFIDL are covered"
          " by proof production.\n");
  fprintf(file, "Also notice that the fragments using difference logic (DL) "
          "may require\npreprocessing steps that are not proof producing.\n"
          "Formulas with quantifiers also require preprocessing steps\n"
          "that are not proof-producing.\n"
          "Skolemization is proof producing though.\n"
          "The user is responsible for providing an adequately written formula.\n\n");

  fprintf(file, "Option --proof-with-sharing uses DAG sharing in the"
          " output proof.\n"
          "Every first occurrence of a term or formula (except negations and"
          " 0-ary terms and formulas)\n"
          "is written as #n:term, where n is its identifier.  Every later occurrence"
          " is simply #n\n");
  fprintf(file, "Option --proof-prune eliminates every unused step in the proof.\n\n");

  fprintf(file, "The following features will be implemented in the future:\n"
          " - Eliminate similar deductions\n"
          " - Output proof for full linear arithmetics\n"
          " - Output proof for E-prover inferences (maybe?)\n");
  fprintf(file, "The following features may be implemented if requested:\n"
          " - Eliminate redundancy in the proof format\n"
          " - Transform n-ary resolution to binary resolution\n"
          " - Make symmetry, reflexivity of equality explicit\n"
          " - Make double negation simplification explicit\n");
}

/*--------------------------------------------------------------*/

static char * input_filename = NULL;

void
proof_set_input_file(char * filename)
{
  input_filename = strmake(filename);
}

/*--------------------------------------------------------------*/

void
proof_done(void)
{
  if (proof_on && status == OPEN)
    my_warning("proof_done: status is still open\n");
  proof_lemma_done();
  proof_SAT_done();
  if (proof_on && option_proof_file_from_input && input_filename)
    {
      free(option_proof_filename);
      MY_MALLOC(option_proof_filename, strlen(input_filename) + 6 + 1);
      strcpy(option_proof_filename, input_filename);
      strcat(option_proof_filename, ".proof");
    }
  if (proof_on &&
      option_proof_stat &&
      !option_proof_filename &&
      !option_proof_file_from_input &&
      status == UNSAT)
    proof_stat_compute();
  else if (proof_on && option_proof_filename)
    {
      FILE * file = stdout;
      if (strcmp(option_proof_filename, "-"))
        if (!(file = fopen(option_proof_filename, "w")))
          {
            my_warning("Unable to open proof file %s\n", option_proof_filename);
            file = stdout;
          }
      if (status == SAT)
        fprintf(file, "Formula is Satisfiable\n");
      else if (status == UNSAT)
        proof_out(file);
      if (strcmp(option_proof_filename, "-"))
        fclose(file);
    }
  context_done();
  free(input_filename);
  free(Pproof_clause_tmp);
}

#else

#ifdef PEDANTIC

#include "proof.h"

void
proof_done(void)
{
}
#endif

#endif /* PROOF */
