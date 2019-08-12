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
  \file proof.h
  \author Pascal Fontaine

  \brief proof module.

  This module provides API functions to memorize the proofs done in
  veriT. */

#ifndef __PROOF_H
#define __PROOF_H

#include "config.h"

#ifdef PROOF

#include <stdarg.h>
#include <stdio.h>

#include "proof_id.h"

#include "bool.h"
#include "DAG.h"
#include "stack.h"

extern bool proof_on;

TSstack(_proof, Tproof);

extern char * option_proof_filename;
extern bool option_proof_file_from_input;
extern bool option_proof_stat;

extern bool option_proof_prune;
extern bool option_proof_merge;
extern int option_proof_version;
/**
   \author Pascal Fontaine
   \brief adds a formula in the context
   \param DAG is the formula to add
   \remark the formula either comes from the user input or
   is an hypothesis (for subproofs)
   \return the id of the formula in the proof
   \attention The formula is not checked, and not deduced */
Tproof    proof_add_formula(TDAG DAG);

/**
   \author Pascal Fontaine
   \brief adds a formula (a disequality lemma) in the context
   \param DAG is the formula to add
   \return the id of the formula in the proof
   \attention The formula is not checked, and not deduced */
/* TODO CHECK!!!!! */
Tproof    proof_add_disequality_lemma(TDAG DAG);

/**
   \author David Deharbe
   \brief adds a formula (a totality lemma) in the context
   \param DAG is the formula to add
   \return the id of the formula in the proof
   \attention The formula is not checked, and not deduced */
/* TODO CHECK!!!!! */
Tproof    proof_add_totality_lemma(TDAG DAG);

/**
   \author Pascal Fontaine
   \brief adds a formula (an arithmetical tautology) in the context
   \param DAG is the formula to add
   \return the id of the formula in the proof
   \attention The formula is not checked, and not deduced */
/* TODO CHECK!!!!! */
Tproof    proof_add_arith_lemma(TDAG DAG);

/**
   \author David Deharbe
   \brief adds a formula (a universal instantiation lemma) in the context
   \param DAG is the formula to add
   \param n is the number of instantiated variables
   \param PDAG is the array of instance terms
   \return the id of the formula in the proof
   \note an instance lemma is \f$ \forall X . A(X) \rightarrow A(X \ t) \f$
*/
/* TODO CHECK!!! */
Tproof    proof_add_forall_inst_lemma(TDAG DAG, unsigned n, TDAG * PDAG);

/**
   \author David Deharbe
   \brief adds a formula (an existential instantiation lemma) in the context
   \param DAG is the formula to add
   \param n is the number of instantiated variables
   \param PDAG is the array of instance terms
   \return the id of the formula in the proof
   \note an instance lemma is \f$ A(t) \rightarrow \exists X . A(t \ X) \f$
*/
/* TODO CHECK!!! */
Tproof    proof_add_exists_inst_lemma(TDAG DAG, unsigned n, TDAG * PDAG);

/**
   \author David Deharbe
   \brief adds an instance of Skolemization of an existential quantifier with
   positive polarity as a binary clause in the context
   \param DAG1 the quantified formula
   \param DAG2 the Skolemized formula
   \return the id of the proof
   \note a Skolem lemma is \f$ \{ \neg \exists X . A(X), A(X \ sk) \} \f$,
   where \f$ sk \f$ is a fresh constant symbol. */
Tproof    proof_add_skolem_ex_lemma(TDAG DAG1, TDAG DAG2);

/**
   \author David Deharbe
   \brief adds an instance of Skolemization of a universal quantifier with negative
   polarity as a binary clause in the context
   \param DAG1 the quantified formula
   \param DAG2 the Skolemized formula
   \return the id of the proof
   \note a Skolem lemma is \f$ \{ \forall X . A(X), (not A(X \ sk)) \} \f$,
   where \f$ sk \f$ is a fresh constant symbol. */
Tproof    proof_add_skolem_all_lemma(TDAG DAG1, TDAG DAG2);

/**
   \author David Deharbe
   \brief Adds a binary clause for quantifier simplification (alpha conversion
   and elimination of unused variables) in the context.
   \param DAG1 the original formula
   \param DAG2 the result formula
   \return the id of the proof */
Tproof    proof_add_qnt_simp_lemma(TDAG DAG1, TDAG DAG2);

/**
   \author David Deharbe
   \brief Adds a binary clause for quantifier merge in the context.
   \param DAG1 is the original formula
   \param DAG2 the result formula
   \return the id of the proof */
Tproof    proof_add_qnt_merge_lemma(TDAG DAG1, TDAG DAG2);

Tproof    proof_add_fol_lemma(TDAG DAG);

/**
   \author Pascal Fontaine
   \brief get the id associated with the lemma
   \param DAG is the lemma
   \return the id of the lemma in the proof */
Tproof    proof_get_lemma_id(TDAG DAG);
/**
   \author Pascal Fontaine
   \brief link a DAG and a proof_id for later lemma addition
   \param DAG the formula
   \param id the proof id of the unit clause with DAG */
void      proof_set_lemma_id(TDAG DAG, Tproof id);

/* PF next functions add to the context a clause C' deduced from a clause C, and
   return context id for C' */
/* NOT NOT A --> A */
Tproof    proof_not_not(Tproof clause);
/* A_1 AND ... A_i ... AND A_n --> A_i */
Tproof    proof_and(Tproof clause, unsigned i);
/* NOT(A_1 OR ... A_i ... OR A_n) --> NOT A_i */
Tproof    proof_not_or(Tproof clause, unsigned i);
/* A_1 OR ... A_n --> {A_1, ... A_n} */
Tproof    proof_or(Tproof clause);
/* NOT(A_1 AND ... A_n) --> {NOT A_1, ... NOT A_n} */
Tproof    proof_not_and(Tproof clause);
/* A XOR B --> {A, B} */
Tproof    proof_xor1(Tproof clause);
/* A XOR B --> {NOT A, NOT B} */
Tproof    proof_xor2(Tproof clause);
/* NOT(A XOR B) --> {A, NOT B} */
Tproof    proof_not_xor1(Tproof clause);
/* NOT(A XOR B) --> {NOT A, B} */
Tproof    proof_not_xor2(Tproof clause);
/* A IMPLIES B --> {NOT A, B} */
Tproof    proof_implies(Tproof clause);
/* NOT(A IMPLIES B) --> A */
Tproof    proof_not_implies1(Tproof clause);
/* NOT(A IMPLIES B) --> NOT B */
Tproof    proof_not_implies2(Tproof clause);
/* A EQUIV B --> {NOT A, B} */
Tproof    proof_equiv1(Tproof clause);
/* A EQUIV B --> {A, NOT B} */
Tproof    proof_equiv2(Tproof clause);
/* NOT(IF A THEN B ELSE C) --> A OR NOT C */
Tproof    proof_not_equiv1(Tproof clause);
/* NOT(IF A THEN B ELSE C) --> NOT A OR NOT B */
Tproof    proof_not_equiv2(Tproof clause);
/* IF A THEN B ELSE C --> A OR C */
Tproof    proof_ite1(Tproof clause);
/* IF A THEN B ELSE C --> NOT A OR B */
Tproof    proof_ite2(Tproof clause);
/* NOT(IF A THEN B ELSE C) --> A OR NOT C */
Tproof    proof_not_ite1(Tproof clause);
/* NOT(IF A THEN B ELSE C) --> NOT A OR NOT B */
Tproof    proof_not_ite2(Tproof clause);

/* PF next functions add to the context a valid clause C
   to define connectors */
/* TRUE */
Tproof    proof_true(void);
/* NOT FALSE */
Tproof    proof_false(void);
/* NOT [A_1 AND ... A_n] OR A_i */
Tproof    proof_and_pos(TDAG DAG, unsigned i);
/* [A_1 AND ... A_n] OR NOT A_1 OR ... NOT A_n */
Tproof    proof_and_neg(TDAG DAG);
/* NOT [A_1 OR ... A_n] OR A_1 OR ... A_n */
Tproof    proof_or_pos(TDAG DAG);
/* [A_1 OR ... A_n] OR NOT A_i */
Tproof    proof_or_neg(TDAG DAG, unsigned i);
/* NOT [A_1 XOR A_2] OR A_1 OR A_2 */
Tproof    proof_xor_pos1(TDAG DAG);
/* NOT [A_1 XOR A_2] OR NOT A_1 OR NOT A_2 */
Tproof    proof_xor_pos2(TDAG DAG);
/* [A_1 XOR A_2] OR A_1 OR NOT A_2 */
Tproof    proof_xor_neg1(TDAG DAG);
/* [A_1 XOR A_2] OR NOT A_1 OR A_2 */
Tproof    proof_xor_neg2(TDAG DAG);
/* NOT[A_1 IMPLIES A_2] OR NOT A_1 OR A_2 */
Tproof    proof_implies_pos(TDAG DAG);
/* [A_1 IMPLIES A_2] OR A_1 */
Tproof    proof_implies_neg1(TDAG DAG);
/* [A_1 IMPLIES A_2] OR NOT A_2 */
Tproof    proof_implies_neg2(TDAG DAG);
/* NOT [A_1 EQUIV A_2] OR A_1 OR NOT A_2 */
Tproof    proof_equiv_pos1(TDAG DAG);
/* NOT [A_1 EQUIV A_2] OR NOT A_1 OR A_2 */
Tproof    proof_equiv_pos2(TDAG DAG);
/* [A_1 EQUIV A_2] OR NOT A_1 OR NOT A_2 */
Tproof    proof_equiv_neg1(TDAG DAG);
/* [A_1 EQUIV A_2] OR A_1 OR A_2 */
Tproof    proof_equiv_neg2(TDAG DAG);
/* NOT [IF A THEN B ELSE C] OR A OR C */
Tproof    proof_ite_pos1(TDAG DAG);
/* NOT [IF A THEN B ELSE C] OR NOT A OR B */
Tproof    proof_ite_pos2(TDAG DAG);
/* [IF A THEN B ELSE C] OR A OR NOT C */
Tproof    proof_ite_neg1(TDAG DAG);
/* [IF A THEN B ELSE C] OR NOT A OR NOT B */
Tproof    proof_ite_neg2(TDAG DAG);

/**
   \author David Deharbe
   \brief adds an instance of alpha conversion as a unary clause in the context
   \param clause is the original formula
   \parm DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule
*/
Tproof     proof_tmp_alphaconv(Tproof clause, TDAG DAG);

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief deduce a formula through let elimination
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_let_elim(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through elimination of n-ary operators
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_nary_elim(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through elimination of n-ary operators
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_distinct_elim(Tproof clause, TDAG DAG);
/**
   \author Pascal Fontaine
   \brief deduce a formula through normalization of arithmetic
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_simp_arith(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through ite elimination
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_ite_elim(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through macro substitution
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_macrosubst(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through beta reduction
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_betared(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce formula through elimination of functions with Boolean argument
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_bfun_elim(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through elimination of connectors for skolemization
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_sk_connector(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through polymorphism elimination
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_pm_process(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through normalization of quantifiers
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_qnt_tidy(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through simplification of quantifiers
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_qnt_simplify(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief deduce a formula through Skolemization
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_skolemize(Tproof clause, TDAG DAG);

/**
   \author Pascal Fontaine
   \brief formula transformation for linear arithmetic
   \param clause is the original formula
   \param DAG the result formula
   \return the id of the proof
   \remark this is a temporary, high level, proof rule */
Tproof    proof_tmp_LA_pre(Tproof clause, TDAG DAG);

typedef enum Tproof_type
{
  eq_reflexive,
  eq_transitive,
  eq_congruent,
  eq_congruent_pred,
  eq_congruent_general,
  p_distinct_elim,
  p_chainable_elim,
  p_right_assoc_elim,
  p_left_assoc_elim,
  p_la_rw_eq,
  la_generic,
  lia_generic,
  nla_generic
} Tproof_type;

/**
   \author Pascal Fontaine
   \brief add a valid clause, and returns its context id
   \param type is the type of valid clause
   \param nb_lits is the number of component formulas
   \remark the remaining arguments are the component formulas (DAGs)
   \return the id of the tautology in the proof */
Tproof    proof_clause(Tproof_type type, unsigned nb_lits, ...);
/**
   \author Pascal Fontaine
   \brief add a valid clause, and returns its context id
   \param type is the type of valid clause
   \param lits is the stack of component formulas (DAGs)
   \return the id of the tautology in the proof */
Tproof    proof_clause_stack(Tproof_type type, Tstack_DAG lits);

/* PF add a clause resolved from others, and returns its context id */
Tproof    proof_resolve(unsigned nb_clauses, ...);
Tproof    proof_resolve_array(unsigned nb_clauses, Tproof *clauses);

/**
   \author David Deharbe
   \brief adds an equisatisfiable formula, and return its context id
   \param DAG the resulting formula
   \param formula the id of the derivation to a formula
   \param table contains the id of binary clauses corresponding to
   individual subformulas that are substituted in orig
   \return the id of the rewritten formula
*/
Tproof    proof_deep_res(TDAG DAG, Tproof formula, Tstack_proof table);

/**
   \author Pascal Fontaine
   \brief computes the resolution of two clauses, and returns its context id
   \param i_clause1 first clause id
   \param i_clause2 second clause id
   \return id of resolved clause
   \remark restricted version of resolution:
   a OR a OR b   resolved with c OR \neg a
   gives a OR b OR c */
Tproof    proof_bin_resolve(Tproof i_clause1, Tproof i_clause2);

/**
   \author Pascal Fontaine
   \brief check if a clause is in the context
   \param clause clause id
   \remark fails if not
   \remark Used to verify that clauses added to external SAT solver are right */
void      proof_clause_check(Tclause clause);

/*
  --------------------------------------------------------------
  Structural recursion transformations
  --------------------------------------------------------------
*/

/** \brief associates a DAG to its proof */
typedef struct TDAG_proof {
  TDAG DAG;
  Tproof proof;
} TDAG_proof;

TSstack(_DAG_proof, TDAG_proof); /* typedefs Tstack_DAG_proof */

#define PROVE_TRANSFORMATION(src_D, dest, type)                         \
  do                                                                    \
    {                                                                   \
      Tstack_DAG stack_proof;                                           \
      stack_INIT(stack_proof);                                          \
      stack_push(stack_proof, DAG_dup(DAG_equiv(src_D, dest.DAG)));     \
      dest.proof = proof_clause_stack(type, stack_proof);               \
      DAG_free(stack_top(stack_proof));                                 \
      stack_free(stack_proof);                                          \
    }                                                                   \
  while (0)

/*
  --------------------------------------------------------------
  SAT solver
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief notify the module that a clause has been added to SAT solver
   \param clause_id the clause id for the SAT solver
   \param clause_size the number of literals
   \param literals the literals */
void      proof_SAT_add(int clause_id, int clause_size, int * literals);
/**
   \author Pascal Fontaine
   \brief notify the module that a clause has been learnt by SAT solver
   \param clause_id the clause id for the SAT solver
   \param clause_size the number of literals
   \param literals the literals */
void      proof_SAT_recheck(int clause_id, int clause_size, int * literals);
/**
   \author Pascal Fontaine
   \brief notify the module that a clause been deduced by SAT solver
   \param clause_id the clause id for the SAT solver
   \param size the number of clauses in the resolution
   \param clauses the clauses in the chain resolution
   \param vars the resolvants */
void      proof_SAT_resolve(int clause_id, int size, int * clauses, int * vars);
/**
   \author Pascal Fontaine
   \brief notify the module that SAT solver has been restarted */
void      proof_SAT_reset(void);

/*
  --------------------------------------------------------------
  SAT solver (new)
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief notify the module that a clause is inserted in the SAT solver
   \param clause the clause */
void      proof_SAT_insert(Tclause clause);
/**
   \author Pascal Fontaine
   \brief notify the module of the id (for the SAT solver) of
   inserted clause
   \param clause_id the clause id for the SAT solver
   \remark hook is necessary because adding clause may introduce several
   of clauses (if simplifies).  Proof module cannot wait for end of clause
   addition to be notified of clause id, since resolution may occur mentioning
   this clause id before end of clause addition */
void      SAT_proof_set_id(SAT_Tclause clause_id);
/**
   \author Pascal Fontaine
   \brief notify the module that a clause is learnt
   \param clause the clause id for the SAT solver
   \remark called by SAT solver
   \remark the full proof in SAT solver datastruct (see corresp. .h file) */
void      SAT_proof_notify(SAT_Tclause clause);

/*
  --------------------------------------------------------------
  Other functions
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief notify the module of the unsatisfiability of the formula
   \remark fails if no empty clause has been derived, an error (a
   warning at the present time) is issued */
void      proof_unsatisfiable(void);
/**
   \author Pascal Fontaine
   \brief notify the module of the satisfiability of the formula */
void      proof_satisfiable(void);

/**
   \author Pascal Fontaine
   \brief notify the module that a new subproof starts */
void      proof_subproof_begin(void);
/**
   \author Pascal Fontaine
   \brief notify the module that the subproof stops */
Tproof    proof_subproof_end(void);
/**
   \author Pascal Fontaine
   \brief notify the module that the subproof is not useful */
void      proof_subproof_remove(void);
/**
   \author Pascal Fontaine
   \brief module initialisation */
void      proof_init(void);
/**
   \author Pascal Fontaine
   \brief module release */
void      proof_done(void);

/**
   \author Pascal Fontaine
   \brief outputs proof documentation to file */
void      proof_doc(FILE * file);
/**
   \author Pascal Fontaine
   \brief outputs proof to file */
void      proof_out(FILE * file);
/**
   \author David Deharbe
   \param file an output stream
   \brief outputs to file the labels of hypotheses used in proof
   \pre the status is unsatisfiable */
void      proof_hyp(FILE * file);
/**
   \author Pascal Fontaine
   \brief notifies module of the input file name */
void proof_set_input_file(char * filename);

#endif /* PROOF */

#ifdef PEDANTIC
void      proof_done(void);
#endif

#endif /* __PROOF_H */
