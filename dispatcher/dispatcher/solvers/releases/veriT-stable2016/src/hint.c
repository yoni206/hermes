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

#include "hint.h"

#include "stack.h"
#include "statistics.h"

#include "literal.h"

#include "congruence.h"
#include "LA.h"

/*
  --------------------------------------------------------------
  Data types
  --------------------------------------------------------------
*/

#define hint_is_CC 1
#define hint_is_LA 2

/** \brief structure to record information on the origin of a hint */
typedef struct TShint_data {
  unsigned char origin; /*< the procedure that produced the hint */
  bool reversed;        /*< helper bit for CC */
  union {
    TDAG DAG; /*< the DAG that produced the hint (in CC) */
    Tlit lit; /*< the lit that produced the hint (in LA) */
  } data;     /*< the reason the hint was produced */
} Thint_data;

TSstack(_hint_data, Thint_data);

/*
  --------------------------------------------------------------
  Local data
  --------------------------------------------------------------
*/

/** This table has Tlit as indices and TDAG or Tlit as values */
static Tstack_hint_data hint_storage = NULL;

/*
  --------------------------------------------------------------
  Module statistics
  --------------------------------------------------------------
*/

static unsigned stats_hint_LA;
static unsigned stats_hint_CC;

/*
  --------------------------------------------------------------
  Local functions
  --------------------------------------------------------------
*/

/** \brief resizes internal storage to accomodate all literals */
static inline void
check_storage(void)
{
  if (2*var_max+1 >= stack_size(hint_storage))
    stack_resize(hint_storage, (2*var_max) + 2);
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

void
hint_CC(Tlit lit, TDAG DAG, bool reversed)
{
  check_storage();
  assert(lit < stack_size(hint_storage));
  hint_storage->data[lit].origin = hint_is_CC;
  hint_storage->data[lit].reversed = reversed;
  hint_storage->data[lit].data.DAG = DAG;
  SAT_hint(lit);
  stats_counter_inc(stats_hint_CC);
}

/*--------------------------------------------------------------*/

void
hint_LA(Tlit lit, Tlit cause)
{
  check_storage();
  assert(lit < stack_size(hint_storage));
  hint_storage->data[lit].origin = hint_is_LA;
  hint_storage->data[lit].data.lit = cause;
  SAT_hint(lit);
  stats_counter_inc(stats_hint_LA);
}

/*--------------------------------------------------------------*/

TDAG
hint_CC_cause(Tlit lit)
{
  assert(lit < stack_size(hint_storage));
  return hint_storage->data[lit].data.DAG;
}

/*--------------------------------------------------------------*/

bool
hint_CC_reversed(Tlit lit)
{
  assert(lit < stack_size(hint_storage));
  return hint_storage->data[lit].reversed;
}

/*--------------------------------------------------------------*/

Tlit
hint_LA_cause(Tlit lit)
{
  assert(lit < stack_size(hint_storage));
  return hint_storage->data[lit].data.lit;
}

/*--------------------------------------------------------------*/

void
hint_explain_dispatch(Tlit lit)
{
  assert(lit < stack_size(hint_storage));
  switch (hint_storage->data[lit].origin) {
  case hint_is_CC:
    CC_hint_explain(lit);
    break;
  case hint_is_LA:
    LA_hint_explain(lit);
    break;
  default:
    my_error("strange literal in hint_explain_dispatch.");
  }
}


/*--------------------------------------------------------------*/

void
hint_init(void)
{
  stack_INIT(hint_storage);
  stats_hint_CC = stats_counter_new("hint/CC", 
				    "Hints produced by congruence closure",
				    "%9d");
  stats_hint_LA = stats_counter_new("hint/LA", 
				    "Hints produced by linear arithmetics",
				    "%9d");
}

/*--------------------------------------------------------------*/

void
hint_done(void)
{
  stack_free(hint_storage);
}
