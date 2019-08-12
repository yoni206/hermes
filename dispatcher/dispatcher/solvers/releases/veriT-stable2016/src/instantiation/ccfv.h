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
   \file ccfv.h
   \author Haniel Barbosa
   \brief Module for searching conflicting instances

   Given a set of groundly consistent literals L and a quantified formula
   Ax1..xn.F a conflicting instantiation \sigma is a substitution s.t. L \wedge
   F\sigma is unsatisfiable. */
#ifndef __CCFV_H
#define __CCFV_H

#include "unify.h"
#include "ujobs.h"

#ifdef PROOF
#include "proof.h"
#endif

/**
    [TODO] Ugly workaround to have clause as well */
typedef struct TDAGinst
{
  TDAG qform;
  Tstack_DAG clause;
  Tstack_Tunifier insts;
} TDAGinst;

TSstack(_DAGinst, TDAGinst); /* typedefs Tstack_DAGinsts */

/*
  --------------------------------------------------------------
  IO interface
  --------------------------------------------------------------
*/

/**
   \author Haniel Barbosa
   \brief initializes module */
extern void CCFV_init(void);

/**
   \author Haniel Barbosa
   \brief releases module */
extern void CCFV_done(void);

extern void CCFV_cycle_init(void);
extern void CCFV_cycle_done(void);

/**
    \author Haniel Barbosa
    \brief checks all quantified formulas (inedependently) and builds
    conflicting instantiations
    \return all instances created along with the quantified formula/clause they
    instantiate */
extern Tstack_DAGinst CCFV(void);

/*
  --------------------------------------------------------------
  Workaround for triggers
  --------------------------------------------------------------
*/

extern void match_DAGs(Tstack_Tunifier * result, TDAG NGDAG, Tstack_DAG terms);

extern
void combine_unifiers(Tstack_Tunifier *result, Tstack_Tunifier base,
                      Tstack_Tunifier new);

#endif
