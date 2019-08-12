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
  distinct operator removing in terms and formulas
  --------------------------------------------------------------
*/

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "general.h"

#include "veriT-DAG.h"
#include "distinct-elim.h"
#include "simp-sym.h"
#include "proof.h"
#include "recursion.h"

/* #define DEBUG_DISTINCT_ELIM */

/*--------------------------------------------------------------*/

static TDAG
distinct_elim_aux(TDAG src)
{
  unsigned i, j, k = 0;
  TDAG dest, *PDAG;
  if (DAG_symb(src) != PREDICATE_DISTINCT)
    return src;
  if (DAG_arity(src) <= 2)
    {
      dest = DAG_dup((DAG_arity(src) == 1)?DAG_TRUE:
                     DAG_neq(DAG_arg0(src), DAG_arg1(src)));
      DAG_free(src);
      return dest;
    }
  if (DAG_sort(DAG_arg(src, 0)) == SORT_BOOLEAN)
    {
      dest = DAG_dup(DAG_arity(src) > 2 ? DAG_FALSE :
                     DAG_not(DAG_equiv(DAG_arg0(src), DAG_arg1(src))));
      DAG_free(src);
      return dest;
    }
  MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
  memcpy(PDAG, DAG_args(src), DAG_arity(src) * sizeof(TDAG));
  simp_sym_notify(DAG_arity(src), PDAG);
  MY_MALLOC(PDAG, DAG_arity(src) * (DAG_arity(src) - 1) * sizeof(TDAG) / 2);
  for (i = 0; i < DAG_arity(src); i++)
    for (j = i + 1; j < DAG_arity(src); j++)
      PDAG[k++] = DAG_neq(DAG_arg(src, i), DAG_arg(src, j));
  dest = DAG_dup(DAG_new(CONNECTOR_AND, DAG_arity(src) * (DAG_arity(src) - 1) / 2,
                         PDAG));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

TDAG
distinct_elim(TDAG src)
{
  TDAG dest;
#ifdef DEBUG_DISTINCT_ELIM
  my_DAG_message("Before distinct elimination\n%D\n", src);
#endif
  dest = structural_recursion(src, distinct_elim_aux);
#ifdef DEBUG_DISTINCT_ELIM
  my_DAG_message("After distinct elimination\n%D\n", dest);
#endif
  return dest;
}

/*
  --------------------------------------------------------------
  Init/Done
  --------------------------------------------------------------
*/

void
distinct_elim_init(void)
{
}

/*--------------------------------------------------------------*/

void
distinct_elim_done(void)
{
}
