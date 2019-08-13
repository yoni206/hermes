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
  Module for handling higher order constants, beta reduction,...
  --------------------------------------------------------------
*/

#ifndef __HOL_H
#define __HOL_H

#include "DAG.h"

/**
   \author Pascal Fontaine
   \brief check a formula for higher-order constructions
   \param src the term (or formula) to check
   \return true iff src is FOL (no HOL construction), false otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remarks beware though that it does not check for non-expanded definitions
   e.g. define-fun that would not be applied */
bool    is_FOL(TDAG src);

/**
   \author Pascal Fontaine
   \brief check a formula for higher-order constructions
   \param src the term (or formula) to check
   \return true if src is FOL (no HOL construction), false otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remarks Compared to is_FOL, checks also for let, polymorphic sorts,
   and booleans as arguments of functions or as quantified vars
   \remarks beware though that it does not check for non-expanded definitions
   e.g. define-fun that would not be applied */
bool    is_FOL_strict(TDAG src);

/**
   \author Pascal Fontaine
   \brief check a formula for binders (lambda, quantifier, let)
   \param src the term (or formula) to check
   \return true if src does not contain binders, false otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers) */
bool    is_binder_free(TDAG src);

/**
   \author Pascal Fontaine
   \brief check a formula for quantifiers
   \param src the term (or formula) to check
   \return true if src does not contain quantifiers, false otherwise
   \remarks Non destructive
   \remarks DAG-linear
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers) */
bool    is_quantifier_free(TDAG src);

/**
   \author Pascal Fontaine
   \brief eliminates higher-order constructions
   - applies beta-reduction
   - replaces defined-functions by their definition, i.e. handles the
   define-fun SMT-LIB construct
   - eliminates let
   - applies equality lowering wherever it can be.  Rewrites equalities
   T1 = T2 where T1 and T2 have function (or predicate) sort into
   forall x_1 ... x_n . T1(x_1, ... , x_n) = T2(x_1, ... , x_n)
   - rename every quantified variable to a fresh variable
   - check that the result is strictly FOL
   \param src the term (or formula) to rewrite
   \return the rewritten term
   \remark non destructive
   \remark DAG-linear on the binder-free part.  Tree linear below binders
   \remark no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \remark ite-, quantifier-, lambda-, apply-tolerant, let-tolerant
   \remark does not handle every HOL constructs, but if such an unsupported
   construct is met, an error message is issued
   \pre no requirement
   \post binder_rename invariant is satisfied */
TDAG    HOL_to_FOL(TDAG src);

/**
   \brief array version of the HOL_to_FOL function
   \remark Destructive
   \see HOL_to_FOL */
void    HOL_to_FOL_array(unsigned n, TDAG * Psrc);

#endif /* __HOL_H */
