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
  let operator removing in terms and formulas
  --------------------------------------------------------------
*/

#include <assert.h>
#include <stdlib.h>

#include "general.h"
#include "stack.h"

#include "veriT-DAG.h"
#include "DAG-tmp.h"
#include "let-elim.h"

/* #define DEBUG_LET_ELIM */

#define bind_new(A, B)				\
  {						\
    if (!DAG_tmp_stack_DAG[A])			\
      stack_INIT(DAG_tmp_stack_DAG[A]);		\
    stack_push(DAG_tmp_stack_DAG[A], B);	\
  }
#define bind_get(A)				\
  stack_top(DAG_tmp_stack_DAG[A])
#define bind_rm(A)				\
  {						\
    stack_dec(DAG_tmp_stack_DAG[A]);		\
    if (!stack_size(DAG_tmp_stack_DAG[A]))	\
      stack_free(DAG_tmp_stack_DAG[A]);		\
  }
#define bind_exists(A)				\
  (DAG_tmp_stack_DAG[A] && bind_get(A))

/*--------------------------------------------------------------*/

static TDAG
let_elim_aux(TDAG src)
{
  unsigned i;
  TDAG dest;
  TDAG * PDAG;
  if (DAG_symb(src) == LET)
    {
      assert(DAG_arity(src) >= 3);
      /* PF this looks like a letrec, but because of binder_rename,
   this should be OK */
      for (i = 0; i < DAG_arity(src) - 1u; i += 2)
  {
    TDAG tmp = let_elim_aux(DAG_arg(src, i + 1));
    bind_new(DAG_arg(src, i), tmp);
  }
      dest = let_elim_aux(DAG_arg_last(src));
      for (i = 0; i < DAG_arity(src) - 1u; i += 2)
  {
    DAG_free(bind_get(DAG_arg(src, i)));
    bind_rm(DAG_arg(src, i));
  }
    }
  else if (binder(DAG_symb(src)) && DAG_arity(src) >= 2)
    {
      for (i = 0; i < DAG_arity(src) - 1u; i++)
  bind_new(DAG_arg(src, i), DAG_NULL);
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src) - 1u; i++)
  PDAG[i] = DAG_arg(src, i);
      PDAG[i] = let_elim_aux(DAG_arg(src, i));
      dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
      DAG_free(DAG_arg(dest,i));
      for (i = 0; i < DAG_arity(src) - 1u; i++)
  {
    assert(!bind_get(DAG_arg(src, i)));
    bind_rm(DAG_arg(src, i));
  }
    }
  else if (DAG_arity(src) == 0)
    dest = DAG_dup(bind_exists(src)?bind_get(src):src);
  else
    {
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); i++)
  PDAG[i] = let_elim_aux(DAG_arg(src, i));
      dest = DAG_dup(DAG_new(DAG_symb(src), DAG_arity(src), PDAG));
      for (i = 0; i < DAG_arity(dest); i++)
  DAG_free(DAG_arg(dest, i));
    }
  return dest;
}

/*--------------------------------------------------------------*/

TDAG
let_elim(TDAG src)
{
  TDAG dest;
#ifdef DEBUG_LET_ELIM
  my_DAG_message("Before let elimination\n%D\n", src);
#endif
  DAG_tmp_reserve();
  dest = let_elim_aux(src);
  DAG_tmp_release();
#ifdef DEBUG_LET_ELIM
  my_DAG_message("After let elimination\n%D\n", dest);
#endif
  return dest;
}

/*--------------------------------------------------------------*/

void
let_elim_array(unsigned n, TDAG * Psrc)
{
  unsigned i;
  DAG_tmp_reserve();
  for (i = 0; i < n; i++)
    {
      TDAG dest = let_elim_aux(Psrc[i]);
      DAG_free(Psrc[i]);
      Psrc[i] = dest;
    }
  DAG_tmp_release();
}
