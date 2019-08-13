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
  Module for polishing quantified formulas
  --------------------------------------------------------------
*/

/*
  DD+PF
  Originally created by DD+PF (august 2007?)
  Code review (EXCEPT Canonize) by PF in april 2008
  Code review global by PF in august 2008
*/

#ifndef __QNT_TIDY_H
#define __QNT_TIDY_H

#include "DAG.h"

/**
   \brief rename quantified variables so that no formula is in the
   scope of two quantifiers on the same variable
   \remarks two different variables may have the same name, if they
   have different sorts
   \remarks outermost variables are renamed first
   \remarks DAG should be lambda-free and apply-free (test included)
   \remarks Tolerant to ite terms
   \remarks DAG-Linear with respect to the quantifier-free part,
   tree-Linear with respect to the quantified part
   \remarks Non-destructive
   \pre DAG should be lambda-free (test included) */
TDAG     qnt_tidy(TDAG DAG);

/**
   \brief PF Sets the DAG->ground bit of ground formulas inside 
   quantified formulas.
   \par(Complexity) DAG-Linear with respect to the quantifier-free part DAG
   should be lambda-free and apply-free (test included). Tree-Linear
   with respect to the quantified part
   \remark Tolerant to apply, macros, ite terms
   \pre DAG should be lambda-free (test included)
   \pre DAG should not contain nested quantifiers on the same variable
   (qnt_tidy rewrites such cases) */
void     qnt_ground(TDAG DAG);

/**
   \brief DD Performs the following simplifications:
   \f{eqnarray*}{
   \forall x, x \neq T \lor \phi(x) & \longrightarrow & \phi(T) \\
   \exists x, x = T \land \phi(x) & \longrightarrow & \phi(T) 
   \f}
   if \f$T\f$ only contains variables that have a larger scope than \f$x\f$.
   \note better call (boolean) simplify after
   \note Non-destructive */
TDAG     qnt_simplify(TDAG src);

void     qnt_simplify_init(void);
void     qnt_simplify_done(void);

#endif /* __QNT_TIDY_H */

