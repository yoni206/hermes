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
  Literal management Module
  --------------------------------------------------------------
*/

#ifndef __LITERAL_H
#define __LITERAL_H

#include <limits.h>

#include "config.h"

#include "stack.h"

#include "veriT-DAG.h"

#define INSIDE_VERIT
#include "veriT-SAT.h"

typedef SAT_Tvar Tvar;
typedef SAT_Tlit Tlit;

#define LIT_UNDEF SAT_LIT_UNDEF
#define LIT_MODEL_EQ UINT_MAX
#define LIT_BRANCH_Z UINT_MAX /** internal branch and bound in LA(Z) */

TSstack(_lit, Tlit);

extern Tvar var_max;
/**
   \brief flag to record if literal is required for theories */
extern bool * bool_required;

/** \brief for three valued logic use */
typedef enum Tboolean_value {FALSE = 0, TRUE = 1, UNDEFINED} Tboolean_value;

/* DD+PF Get the literal associated to DAG */
Tlit DAG_to_lit(TDAG DAG);
/* DD+PF Same as above, but returns 0 if no literal associated to DAG
   Does not set a boolean variable */
Tlit DAG_is_lit(TDAG DAG);
/* DD+PF Get the literal bounded to DAG (lit should be positive) */
TDAG lit_to_DAG(Tlit lit);
/* DD+PF Get var bounded to DAG */
TDAG DAG_to_var(Tvar var);
/* DD+PF Get DAG bounded to var */
TDAG var_to_DAG(Tvar var);

#ifdef POLARITY_FILTER
/**
   \author Pascal Fontaine
   \brief add 1 to number of occurrences of lit
   \param[in] lit the literal
   \remark the side effect is to mark bool_required[lit] to true if
   more than one occurrence AND lit is not a Tseitin variable (i.e.
   if its top symbol is not a boolean connector) */
void bool_lit_inc(Tlit lit);

/**
   \author Pascal Fontaine
   \brief decreases 1 to number of occurrences of lit
   \param[in] lit the literal
   \remark the side effect is to mark bool_required[lit] to false if
   the number of occurrences falls to 0 */
void bool_lit_dec(Tlit lit);

/* \brief Original formula (pre-processed), not the CNF one. */
extern Tstack_DAG orig_formula;
/* \brief Whether literals from the SAT_stack are required for
   satisfying original formula. */
extern bool * original_required;

/**
    \author Haniel Barbosa
    \brief goes through original formula and added lemmas and checks which
    elements of the model for its CNF are indeed required for satisfiability */
void prune_cnf_model(void);
#endif

#define lit_make SAT_lit
#define lit_var  SAT_lit_var
#define lit_neg  SAT_lit_neg
#define lit_pol  SAT_lit_pol

void literal_init(void);
void literal_reset(void);
void literal_done(void);

#endif /* __LITERAL_H */
