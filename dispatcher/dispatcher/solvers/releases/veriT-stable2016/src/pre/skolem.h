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
  Module for skolemizing quantified formulas
  --------------------------------------------------------------
*/

#ifndef __SKOLEM_H
#define __SKOLEM_H

#include "DAG.h"

/* DD+PF We assume no variable appears both free and bound.
   (In SMT, this is a requirement)
   We also assume that the formula is lambda-free.  Indeed,
   lambda may intervene also in the quantification process:
   \lambda u. \exists u (x) --> \lambda u. u (f(u)).
   Update : on 20070816, PF+DD do not understand the previous comment
   anymore, but agree that lambda may hurt
   More generally, we assume (and check) that the input is FOL.
   No macro should be used anywhere.
   The process is linear with respect to the DAG size of the
   ground part of the DAG, and linear with respect of the tree
   size of the DAG.  In other words, it is linear (% DAG) for
   ground formulas, but potentially exponential for formulas with
   quantifiers.
   Process is structural, outer Skolemization.
   It would be better to implement Andrews' (inner) Skolemization, but
   there are some complexity issues and technical difficulties that are
   not that easy to solve quickly, in a first approach.
   To be left as a student work?  If it is needed.
   No quantifier should appear inside a term.
   Non-destructive
   The reference counter of result DAG is at least one.
   TODO: this is a restriction for ite terms.

   Code reviewed by PF in august 2008

   DD 20110510 Added option for so-called shallow Skolemization. Skolemization
   is not applied within essentially universal quantifiers: only
   Skolem constants are generated. If universal quantifiers are instantiated, 
   Skolemization is applied to the instances and may generate new Skolem
   constants.
*/

void skolemize_init(void);
void skolemize_done(void);
TDAG skolemize (TDAG DAG);

#endif /* __SKOLEM_H */
