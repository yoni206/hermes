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

#ifndef NLA_H
#define NLA_H

#include "literal.h"
#include "veriT-status.h"

#include "proof.h"

extern char * reduce_path;

/**
   \brief initializes the module
   \remarks must be called before any other function of the module */
extern void      NLA_init(void);

/**
   \brief releases the module */
extern void      NLA_done(void);

/**
   \brief activate NLA module */
extern void      NLA_activate(void);

/**
   \brief asserts a literal
   \param lit a literal */
extern Tstatus   NLA_assert(Tlit lit);

/**
   \brief clear the set of literals */
extern void      NLA_clear(void);

/**
   \brief check satisfiability of the set of given clues
   \return status of satisfiability after the check */
extern Tstatus   NLA_solve(void);

/**
   \brief Pushes onto veriT_conflict the set of lits that led to the conflict
   \pre NLA_status() yields UNSAT */
extern void      NLA_conflict(void);

#ifdef PROOF
extern Tproof    NLA_conflict_proof(void);
#endif

/**
   \brief Verifies if the module has a lemma to produce.
   \return \e true if it has a lemma to return, \e false otherwise. */
extern bool      NLA_has_lemma(void);

/**
   \brief Finds model equalities between shared variables
   \remark enqueue in xqueue the equalities
   \return true iff there has been equalities enqueued */
extern bool      NLA_model_eq(void);

#endif
