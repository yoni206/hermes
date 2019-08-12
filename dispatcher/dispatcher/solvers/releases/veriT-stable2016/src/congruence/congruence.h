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
  Module for congruence closure
  --------------------------------------------------------------
*/

#ifndef __CONGRUENCE_H
#define __CONGRUENCE_H

/* PF Decision for (dis)equality and uninterpreted functions.
   Incrementally takes a set of literals.
   Computes if this set is satisfiable with respect to equality only.

   Quantified formulas and lambda terms are treated as constants:
   \forall x (x = a), \not \forall x (x = b), a = b is "satisfiable"
   boolean connectors and ite function are not interpreted here
   (p(a) and not p(b)), a = b is "satisfiable"
   So better only give atoms and quantified formulas */

#include <stdarg.h>

#include "config.h"

#include "DAG.h"
#include "literal.h"
#include "veriT-status.h"
#include "veriT-state.h"

#ifdef PROOF
#include "proof.h"
#endif

/*
  --------------------------------------------------------------
  Init/done
  --------------------------------------------------------------
*/

/**
   \brief initializes the module
   \remarks must be called before any other function of the module */
extern void     CC_init(void);

/**
   \brief releases the module */
extern void     CC_done(void);

/*
  --------------------------------------------------------------
  IO interface
  --------------------------------------------------------------
*/

/**
   \brief status of congruence closure (SAT/UNSAT) */
extern Tstatus  CC_status;

/**
   \brief notifies the module that atoms from this DAG may be asserted
   positively or negatively, and equalities between terms may be given
   \param DAG a formula
   \remark literals are remembered for future assertions
   \remark literals are stored for theory propagation
   \remark terms are built in CC */
extern void     CC_notify_formula(TDAG DAG);

/**
   \brief notifies the module that DAG is relevant for arithmetic
   \param DAG a formula */
/* IMPROVE THIS IS CURRENTLY NEVER BACKTRACKED */
extern void     CC_DAG_arith(TDAG DAG);

/**
   \brief asserts a literal
   \param lit a literal
   \return UNSAT if the set of asserted things so for is unsatisfiable
   \return SAT otherwise */
extern Tstatus  CC_assert(Tlit lit);

/**
   \brief asserts an equality between two terms
   \param DAG1 a term
   \param DAG2 a term
   \param lit a literal as a placeholder for premisses of equality
   \return UNSAT if the set of asserted things so for is unsatisfiable */
extern Tstatus  CC_assert_eq(TDAG DAG1, TDAG DAG2, Tlit lit);

/**
   \brief stores in veriT_conflict all literals that lead to inconsistency
   \return the proof id of the clause
   \pre CC_satus == UNSAT
   \remark should only be called once after conflict detection */
extern void    CC_conflict(void);
#ifdef PROOF
extern Tproof  CC_conflict_proof(void);
#endif

/**
   \brief stores in veriT_conflict all literals implying lit
   \param lit the literal set as hint by congruence closure
   \return the proof id of the clause */
extern void     CC_hint_explain(Tlit lit);
#ifdef PROOF
extern Tproof   CC_hint_explain_proof(Tlit lit);
#endif

/**
   \brief stores in veriT_conflict all literals that lead to DAG0 == DAG1
   \param DAG1 the first DAG in the equality
   \param DAG2 the second DAG in the equality
   \return the proof id of the clause
   \pre DAG0 and DAG1 should be equal according to CC */
extern void     CC_premisses_eq(TDAG DAG1, TDAG DAG2);
#ifdef PROOF
extern Tproof   CC_premisses_eq_proof(TDAG DAG1, TDAG DAG2);
#endif

/**
   \brief stores in veriT_conflict all literals that lead to DAG0 != DAG1
   \param DAG1 the first DAG in the inequality
   \param DAG2 the second DAG in the inequality
   \param ineq the inequality
   \return the proof id of the clause
   \pre DAG0 and DAG1 should be different according to CC */
extern void     CC_premisses_ineq(TDAG DAG1, TDAG DAG2, TDAG ineq);
#ifdef PROOF
extern Tproof   CC_premisses_ineq_proof(TDAG DAG1, TDAG DAG2, TDAG ineq);
#endif

/*
  --------------------------------------------------------------
  Utilities for models
  --------------------------------------------------------------
*/

extern void     CC_model(void (out) (char *format, ...));

/*
  --------------------------------------------------------------
  Utilities for instantiation
  --------------------------------------------------------------
*/

/**
   \author Palcal Fontaine
   \brief applies f to every element in the signature table
   \param f function operating on signature */
extern void CC_sig_apply(void (*f)(TDAG));

/**
    \author Haniel Barbosa
    \brief get the DAG that is signature equivalent with symb and parameters
    given
    \param symb topsymbol
    \param params parameters
    \return the DAG equivalent to arguments, DAG_NULL if none
    \remark public function */
extern TDAG sig_query_params(Tsymb symb, Tstack_DAG params);

/**
   \brief returns the representative for input in congruence closure
   \param DAG a term
   \return a DAG representing the congruence class of DAG */
extern TDAG     CC_abstract(TDAG DAG);

/**
   \brief returns the boolean value of predicate over representative
   for input in congruence closure
   \param DAG a term
   \return a DAG representing the congruence class of DAG */
extern TDAG     CC_abstract_p(TDAG DAG);

/**
   \author Haniel Barbosa
   \brief checks if two terms are desiqual in CC
   \param D0 a term
   \param D1 a term
   \return true if CC asserts them disequal, false otherwise */
extern bool     CC_disequal(TDAG D0, TDAG D1);

/**
   \author Haniel Barbosa
   \brief collects all classes disequal to class of DAG
   \param DAG a term
   \return a (possibly empty) set of classes */
extern Tstack_DAG CC_diseqs(TDAG DAG);

/**
   \brief returns all signatures for symbol
   \param symb a symbol
   \return the stack of signatures
   \remark if f(a) and f(b) exist, but a = b, then only one is returned */
extern Tstack_DAG CC_get_sig(Tsymb symb);

/**
   \brief returns all signatures congruent to DAG for symbol
   \param symb a symbol
   \param DAG a DAG
   \return the stack of signatures
   \remark if f(a) and f(b) exist, but a = b, then only one is returned */
extern Tstack_DAG CC_get_sig_DAG(Tsymb symb, TDAG DAG);

/**
   \brief returns one element per class that has the sort given in argument
   \param sort the sort
   \return the stack of class representatives */
extern Tstack_DAG CC_get_sort_classes(Tsort sort);

/**
   \author Haniel Barbosa
   \brief sets symbol bitmask of the given DAG's class according to top symbols
   of all function applications in class
   \remark the bitmask only comports 64 function symbols, therefore if a symbol
   is above this threshold it does not appear in the bitmask
   \remark traverses the whole congruence class to set the bitmask, so that
   whatever subsequent call with the same class has no effect
   \remark sets the "symbols" parameter of given class */
extern void CC_set_symbols(TDAG DAG);

/**
   \author Haniel Barbosa
   \brief resets all bitmasks in classes */
extern void CC_reset_symbols(void);

/**
   \author Haniel Barbosa
   \brief checks if a given symbol is not present in the class of DAG
   \param DAG the DAG whose class is checked for symbol
   \param symbol the symbol to be checked
   \return false if symbol has a defined bitmask and it is not in the class,
   true otherwise
   \remark since a bit mask is used for fast check, up to 64 function symbols
   can be checked this way. For all other symbols above this threshold this
   function is useless */
extern bool class_has_symbol(TDAG DAG, Tsymb symbol);

/**
   \author Haniel Barbosa
   \brief given a disequality, sets the classes of its arguments as disequal
   \param DAG a disequality
   \remark modifies the "diseqs" parameter of each class */
extern void CC_set_diseqs(TDAG DAG);

/**
   \author Haniel Barbosa
   \brief releases all associations regarding disequalities between classes */
extern void CC_free_diseqs(void);

#endif /* __CONGRUENCE_H */
