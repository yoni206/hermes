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

#ifndef __INST_MAN_H
#define __INST_MAN_H

/*
  --------------------------------------------------------------
  Handles instances creation, management and deletion
  --------------------------------------------------------------
*/

/** Activates basic debugging in instantiation heuristics */
/* #define DEBUG_HEURISTICS */

#include "bool.h"
#include "free-vars.h"
#include "congruence.h"
#include "unify.h"
#include "ccfv.h"
#include "ccfv-bckt.h"
#include "inst-trigger.h"

typedef struct Tinst Tinst;

/** \brief A tree of instantiations. The first node is the DAG being
    instantiated */
struct Tinst
{
  TDAG DAG;
  unsigned size;
  Tinst * next;
};

TSstack(_Tinst, Tinst); /* typedefs Tstack_Tinst */

/*
  --------------------------------------------------------------
  IO interface
  --------------------------------------------------------------
*/

extern void inst(Tstack_DAG * Plemmas);

extern void inst_mark_instances(void);
extern void inst_mark_clause(Tclause clause, unsigned clause_id);

extern void inst_init(void);
extern void inst_done(void);

/** \brief Quantified formulas asserted in CC */
extern Tstack_DAG CC_quantified;

/* Macro for checking whether terms are congruent. CC_abstract of a fresh term
   is DAG_NULL, therefore the further tests to avoid that two fresh terms which
   are not the same are wrongly seem as congruent */
#define congruent(t1, t2) ((CC_abstract(t1) && \
                            CC_abstract(t1) == CC_abstract(t2)) || t1 == t2)

/*
  --------------------------------------------------------------
  Scoring, Symbols
  --------------------------------------------------------------
*/

/**
   \brief marks the symbol occurrences throughout a given DAG
   \remark Only occurrences in non-ground DAGs count */
typedef struct OSymb
{
  Tsymb symbol;
  unsigned nb_occurs;
} OSymb;

TSstack(_OSymb, OSymb); /* typedefs Tstack_OSymb */

extern void DAG_prop_symbols_free(Tstack_OSymb * symbs);

/**
   \author Haniel Barbesa
   \briefs recursevely resets DAG_tmp casted as Tstack_OSymb for DAG
   \param DAG a DAG */
extern void DAG_tmp_reset_symbs(TDAG DAG);

/**
   \author Haniel Barbesa
   \briefs collects all predicate and function symbols occurring in non-ground
   sub-DAGs of given DAG
   \param DAG the DAG being evaluated
   \param is_pred whether DAG is an atom or a term
   \param vars the variables to define groundness */
extern void set_symbs(TDAG DAG, bool is_pred, Tstack_DAG vars);

/**
   \author Haniel Barbesa
   \briefs computes unification potential of an atom along with its polarity
   \param DAG an atom
   \param pol polarity
   \return the scoring value, with the smaller meaning the easier
   \remark Currently the features considered are:
   - whether DAG has only variables or fresh terms
   - polarity (positives first)
   - index size of predicate/function symbols occurring in the DAG */
extern unsigned score_lit(TDAG DAG, bool pol);

#endif
