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
  Conjunctive normal form
  --------------------------------------------------------------
*/

#ifndef __CNF_H
#define __CNF_H

#include "config.h"

#include "DAG.h"
#include "bool.h"
#include "proof_id.h"

/*--------------------------------------------------------------*/

/**
   \brief add clauses for cnf associated with DAG
   \param DAG the formula
   \param Pclauses a pointer to a stack of clauses where to add cnf */
void cnf(TDAG DAG, Tstack_clause *Pclauses);

/*--------------------------------------------------------------*/

#ifdef PROOF
/**
   \brief add clauses for cnf associated with DAG
   \param DAG the formula
   \param Pclauses a pointer to a stack of clauses where to add cnf
   \param proof the proof */
void cnf_proof(TDAG DAG, Tstack_clause * Pclauses, Tproof proof);
#endif

/*--------------------------------------------------------------*/

void cnf_init(void);
void cnf_done(void);
void cnf_reset(void);

#endif /* __CNF_H */
