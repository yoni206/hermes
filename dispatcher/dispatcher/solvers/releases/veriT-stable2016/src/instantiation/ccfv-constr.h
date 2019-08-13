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

#ifndef __CCFV_CONSTR_H
#define __CCFV_CONSTR_H

#include "free-vars.h"
#include "unify.h"
#include "ccfv-mod.h"

/*
    \author Haniel Barbosa
    \brief Handles constraints creation and management */

/*
  --------------------------------------------------------------
  Data structures
  --------------------------------------------------------------
*/

/* [TODO] probably add a CCFV_ASSIGN_FRESH, which would be as bad as
   CCFV_ASSIGN_FAPP */
typedef enum Tconstr_type {
  CCFV_UNDEF = 0,
  CCFV_GROUND_SIG,
  CCFV_GROUND_PRED,
  CCFV_ASSIGN,
  CCFV_PRED,
  CCFV_EMATCH_FRESH,
  CCFV_EMATCH,
  CCFV_EUNI_VAR,
  CCFV_EUNI_FAPP,
  CCFV_ASSIGN_FAPP
} Tconstr_type;

/* weight according to branching potential:
   - GROUND_SIG, GROUND_PRED
   - ASSIGN
   - PRED, EMATCH(_FRESH),
   - EUNI_VAR
   - EUNI_FAPP)
   - ASSIGN_FAPP */

/**
    \brief a unifying constraint
    \remark for now it is its simplest form, but more structure can be added,
    reflecting that it only makes sense to some jobs after others. This way a
    constraint could be not a single but a list jobs, with the detail that among
    those some would have ordering constraints ("only do after finishing those
    guys") and others not ("take these in any order") */
typedef struct Tconstr
{
  TDAG D0;           /*< first DAG in the job */
  TDAG D1;           /*< second DAG in the job */
  bool pol;          /*< polarity of job */
  Tconstr_type type; /*< type of constraint */
  unsigned t_score;  /*< score of constraint type */
  unsigned score;    /*< score of constraint */
} Tconstr;

TSstack(_constr, Tconstr); /* typedefs Tstack_constr */

/** \brief component of constraints sharing variables */
typedef struct Tcomp
{
  Tstack_constr constrs; /*< constrains in component */
  unsigned score;        /*< the smaller the score the sooner the constraints
                           are considered for unification */
} Tcomp;

TSstack(_comp, Tcomp); /* typedefs Tstack_comp */

#define is_predicate(c) !c.D1

/*
  --------------------------------------------------------------
  Creation and classification
  --------------------------------------------------------------
*/

extern Tconstr create_constr_lit(TDAG lit, Tunifier solution);
extern Tconstr create_constr_eq(TDAG D0, TDAG D1, Tunifier solution);
extern Tconstr create_constr(TDAG D0, TDAG D1, Tconstr_type type);
extern void update_constr(Tconstr * constr, Tunifier solution);

/*
  --------------------------------------------------------------
  Ordering
  --------------------------------------------------------------
*/

/* If there is at least a var in D0,D1, it will be in NGDAG */
#define ORDER_CONSTRAINT(NGDAG, UDAG, D0, D1)   \
  do {                                          \
    assert(!ground_mod(D0) || !ground_mod(D1)); \
    if (ground_mod(D0))                         \
      {                                         \
        NGDAG = D1;                             \
        UDAG = D0;                              \
      }                                         \
    else if (ground_mod(D1))                    \
      {                                         \
        NGDAG = D0;                             \
        UDAG = D1;                              \
      }                                         \
    else if (!DAG_arity(D1))                    \
      {                                         \
        NGDAG = D1;                             \
        UDAG = D0;                              \
      }                                         \
    else                                        \
      {                                         \
        NGDAG = D0;                             \
        UDAG = D1;                              \
      }                                         \
    } while (0)

/**
    \author Haniel Barbosa
    \brief sort set of constraints by components (literals sharing variables)
    with less variables
    \remark components themselves are sorted by constraints with less variables
    \remark Destructive */
extern Tstack_comp sort_constraints(Tstack_constr constraints);

extern int comps_cmp_q_score(Tcomp * Pcomp1, Tcomp * Pcomp2);
extern int constrs_cmp_q_score(Tconstr * Pconstr1, Tconstr * Pconstr2);
extern int constrs_cmp_q_t_score(Tconstr * Pconstr1, Tconstr * Pconstr2);

/*
  --------------------------------------------------------------
  Pruning
  --------------------------------------------------------------
*/

extern bool check_ground_apps(Tstack_constr constraints);

#endif
