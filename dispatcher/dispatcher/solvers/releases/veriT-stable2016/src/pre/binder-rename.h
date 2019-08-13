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
  Module for removing let constructs in formulas
  --------------------------------------------------------------
*/

#ifndef BINDER_RENAME_H
#define BINDER_RENAME_H

#include "DAG.h"

/**
   \author David Déharbe and Pascal Fontaine
   \brief computes an equivalent term (or formula) where each bound variable
   is bounded by one binder only
   \param DAG the input term (or formula)
   \return the term (or formula) with binder renamed
   \remarks uses Pflag on DAG descendent nodes that represent bound symbols
   \remarks non destructive
   \remarks tree-linear (DAG-exponential)
   \remarks this high complexity is acceptable because this is applied on the
   input formula before let expansion (i.e, before the tree explodes) so this
   is linear with respect to the size of the input
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \pre none
   \post two different binders bound different variables in the formula seen
   as a tree

   \remarks there is a mismatch in the semantics of the let between
   SMT-LIB 1 and SMT-LIB 2.  This function should only be called with
   SMT-LIB 2.  This let is a parallel let i.e. for (let ((x t1) (y
   t2)) t3), if t2 contains x, it is NOT the one associated to t1 but
   a free constant in this let construction.
   This is not a problem since SMT-LIB 1 lets are suppressed on parsing */
TDAG      binder_rename(TDAG DAG);

/**
   \author David Déharbe and Pascal Fontaine
   \brief computes an equivalent term (or formula) where each bound variable
   is bounded by one binder only
   \param n the number of input terms (or formulas)
   \param Psrc the input terms (or formulas)
   \remarks uses Pflag on DAG descendent nodes that represent bound symbols
   \remarks destructive
   \remarks tree-linear (DAG-exponential)
   \remarks this high complexity is acceptable because this is applied on the
   input formula before let expansion (i.e, before the tree explodes) so this
   is linear with respect to the size of the input
   \remarks no particular requirements on formula (no variable capture,
   behaves honestly with quantifiers)
   \pre none
   \post two different binders bound different variables in the formula seen
   as a tree

   \remarks there is a mismatch in the semantics of the let between
   SMT-LIB 1 and SMT-LIB 2.  This function should only be called with
   SMT-LIB 2.  This let is a parallel let i.e. for (let ((x t1) (y
   t2)) t3), if t2 contains x, it is NOT the one associated to t1 but
   a free constant in this let construction.
   This is not a problem since SMT-LIB 1 lets are suppressed on parsing */
void      binder_rename_array(unsigned n, TDAG * Psrc);

#endif
