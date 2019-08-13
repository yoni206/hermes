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

#ifndef VERIT_STATE_H
#define VERIT_STATE_H

#include "stack.h"

#include "bool.h"
#include "DAG.h"

/**
   \brief bool value stating if quantifiers are active
   \remark true for all categories with quantifiers */
extern bool Q_active;

/**
   \brief bool value stating if LA decision procedure is active
   \remark false mainly for QF_UF */
extern bool LA_active;

/**
   \brief bool value stating if NLA decision procedure is active */
extern bool NLA_active;

/**
   \brief stack of literals to compute conflict */
extern Tstack_lit veriT_conflict;

/**
   \brief stack of DAGs that are pairwise equal, to compute conflict */
extern Tstack_DAG veriT_conflict_eqs;

/**
   \brief stack of arbitrary lemmas to add to SAT solver */
extern Tstack_DAG veriT_lemmas;

#if 0
#define XMASK (1u << 31u)

/**
   \brief checks if literal is an information exchange */
#define is_xlit(lit) (lit & XMASK)
#endif

/*
  --------------------------------------------------------------
  Init/done
  --------------------------------------------------------------
*/

/**
   \brief initializes the module
   \remarks must be called before any other function of the module */
extern void
veriT_state_init(void);

/**
   \brief releases the module */
extern void
veriT_state_done(void);

/*
  --------------------------------------------------------------
  Exchange Queue
  --------------------------------------------------------------
*/

typedef unsigned Txtype;

enum {
  XTYPE_CC_EQ = 0,        /*< Equality from CC to LA */
  XTYPE_CC_INEQ = 1,      /*< Disequality from CC to LA */
  XTYPE_LA_MODEL_EQ = 2,  /*< Model equality from LA to CC */
  XTYPE_NLA_MODEL_EQ = 3, /*< Model equality from NLA to CC */
};

/**
   \brief stack of things to exchange between CC and arith */
extern Tstack_unsigned xqueue;

/**
   \brief enqueues an information for DP interchange
   \param type the type of information */
static inline void veriT_xenqueue_type(const Txtype type) 
{
  stack_push(xqueue, type);
}

/**
   \brief enqueues an information for DP interchange
   \param DAG a DAG */
static inline void veriT_xenqueue_DAG(const TDAG DAG)
{
  stack_push(xqueue, (unsigned) DAG);
}

static inline Txtype veriT_xqueue_get_type(const unsigned i)
{
  return (Txtype) stack_get(xqueue, i);
}

static inline TDAG veriT_xqueue_get_DAG(const unsigned i)
{
  return (TDAG) stack_get(xqueue, i);
}

static inline void veriT_xqueue_clear(void) 
{
  stack_reset(xqueue);
}

#endif /* VERIT_STATE_H */
