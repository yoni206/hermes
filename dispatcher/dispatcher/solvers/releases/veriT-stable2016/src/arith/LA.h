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

#ifndef LA_H
#define LA_H

#include "config.h"

#include "DAG.h"
#include "literal.h"
#include "veriT-status.h"

#ifdef PROOF
#include "proof.h"
#endif

extern bool LA_overflow;

/*
  --------------------------------------------------------------
  Command-line options
  --------------------------------------------------------------
*/

extern bool LA_enable_lemmas;
extern bool LA_enable_theory_propagation;
extern bool LA_disable_bbvsh;

/*
  --------------------------------------------------------------
  Init/done
  --------------------------------------------------------------
*/

/**
   \brief initializes the module
   \remarks must be called before any other function of the module */
extern void     LA_init(void);

/**
   \brief set the module according to options
   \remarks must be called before any other function of the module, after init */
extern void     LA_set(void);

/**
   \brief releases the module */
extern void     LA_done(void);

/*
  --------------------------------------------------------------
  IO interface
  --------------------------------------------------------------
*/

/**
   \brief notifies the module that atoms from this DAG may be asserted
   positively or negatively, and equalities between arithmetic-relevant
   terms are to be given
   \param DAG a formula
   \param aDAG_tag function to tag a DAG as being relevant for arithmetic */
extern void     (*LA_notify_formula)(TDAG DAG);

/**
   \brief Finds pairs of atoms that have been notified that correspond to bounds
   on the same expression and create a lemma relating those atoms.
   \remark Created lemmas are stacked onto veriT_lemmas */
extern void     (*LA_unate_propagation)(void);

/**
   \brief asserts a literal
   \param lit a literal
   \return UNSAT if the module can quickly detect that the asserted literal is 
   an unsatisfiable constraint
   \return SAT otherwise
   \note If the literal is a negation of equality A != B, the module stacks the
   DAG for A = B or A < B or A > B onto veriT_lemmas.
   \note The SAT result value is generally not correct: LA_solve needs to be
   run.
   \see LA_solve */
extern Tstatus  (*LA_assert)(Tlit lit);

/**
   \brief asserts an equality between two terms
   \param DAG1 a term
   \param DAG2 a term */
extern Tstatus  (*LA_assert_eq)(TDAG DAG1, TDAG DAG2);

/**
   \brief asserts the negation of an equality between two terms
   such that DAG1 != DAG2 is in the original formula
   \param DAG1 a term
   \param DAG2 a term
   \remark this induces a lemma.  Never used in conflicts. */
extern Tstatus  (*LA_assert_neq)(TDAG DAG1, TDAG DAG2);

/**
   \brief known term DAG1 will now be referred as DAG2
   \param DAG1 a term
   \param DAG2 a term */
extern Tstatus  (*LA_rename)(TDAG DAG1, TDAG DAG2);

/**
   \brief check satisfiability of the given set of literals
   \param integer enable/disable solving of integrality constraints
   \return UNSAT if the set of literals, excluding negations of
   equalities, is unsatisfiable.
   \return SAT if the set of literals, excluding negations of
   equalities, is satisfiable. */
extern Tstatus  (*LA_solve)(const bool integer);

/**
   \brief check satisfiability of the given set of literals in
   the theory of real arithmetics
   \return UNSAT if the set of literals, excluding negations of
   equalities, is unsatisfiable.
   \return SAT if the set of literals, excluding negations of
   equalities, is satisfiable. */
extern Tstatus  (*LA_solve_r)(void);

/**
   \brief check satisfiability of the given set of literals in
   the theory of integers
   \param integer enable/disable solving of integrality constraints
   \return UNSAT if the set of literals, excluding negations of
   equalities, is unsatisfiable.
   \return SAT if the set of literals, excluding negations of
   equalities, is satisfiable. */
extern Tstatus  (*LA_solve_z)(void);

/**
   \brief simplifies the set of "facts", assuming the constraints already given
   will never be backtracked */
extern void     (*LA_simp)(void);

/**
   \brief puts the module back in a normal state
   \remark should be call on backtrack from an UNDEF or UNSAT state
   before any assert */
extern void     (*LA_repair)(void);

/**
   \brief stacks in veriT_conflict the set of lits that led to the conflict
   \pre status is UNSAT
   \return the proof id of the clause */
extern void     (*LA_conflict)(void);
#ifdef PROOF
extern Tproof   (*LA_conflict_proof)(void);
#endif

/**
   \brief stacks in veriT_conflict the set of lits that led to the conflict
   \pre status is UNSAT
   \return the proof id of the clause */
extern void     (*LA_conflict_z)(void);
#ifdef PROOF
extern Tproof   (*LA_conflict_proof_z)(void);
#endif

/**
   \brief Finds model equalities between shared variables
   \remark enqueue in xqueue the equalities
   \return true iff there has been equalities enqueued */
extern bool (*LA_model_eq)(void);

/**
   \brief stores in veriT_conflict a hint and its cause
   \param lit the hinted literal
   \pre lit must have been previously hinted by LA
*/
extern void (*LA_hint_explain)(Tlit);

/**
   \brief switch the module to multiprecision */
extern void LA_switch_to_mp(void);

#endif /* LA_H */
