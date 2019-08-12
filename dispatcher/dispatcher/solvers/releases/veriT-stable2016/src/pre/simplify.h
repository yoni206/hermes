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
  Module for simplifying formulas and terms
  --------------------------------------------------------------
*/

#ifndef __SIMPLIFY_H
#define __SIMPLIFY_H

/* PF

   simplify_formula:
   simple transformation rules applied to obtain a formula that is
   logically equivalent to the input and hopefully simpler.
   The transformation is linear with respect to the size of the formula.
   src may contain quantifiers, lambda, apply, ...

   Code reviewed by PF in august 2008
*/

#include "DAG.h"

void      simplify_init(void);
void      simplify_done(void);

/* PF some simple linear rules - DD destructive 
   the reference counter of result is at least 1. */
TDAG      simplify_formula(TDAG src);

/* PF some simple linear rules - DD destructive 
   the reference counter of result is at least 1. 
   obs. differs from simplify_formula in that it does
   not assume that it is a conjunction. */
TDAG      simplify_instance(TDAG src);

/**
   \author Pascal Fontaine
   \brief realizes some unit clause propagation, i.e, for
   x = T and phi(x), rewrites to phi(T)
   \remarks this is programmed in an quadratic way, can be improved
   \remarks should not be applied in incremental mode */
TDAG      simplify_formula_sat(TDAG src);

/* DD remove useless assumptions - assumes that src is a conjunction s.t.
   assumptions come first, followed by goal formula */
TDAG      simplify_benchmark(TDAG src);

#endif /* __SIMPLIFY_H */
