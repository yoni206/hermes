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

#include "veriT-DAG.h"
#include "DAG.h"
#include "DAG-symb.h"
#include "DAG-tmp.h"
#include "free-vars.h"

Tstack_DAG * DAG_fvars;

void
fvars_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
  unsigned i;
  MY_REALLOC(DAG_fvars, new_alloc * sizeof(Tstack_DAG));
  for (i = old_alloc; i < new_alloc; ++i)
    DAG_fvars[i] = NULL;
}

/*--------------------------------------------------------------*/

void
fvars_hook_free(TDAG DAG)
{
  if (!ground(DAG))
    stack_free(DAG_fvars[DAG]);
}

/*--------------------------------------------------------------*/

/* When this is used with new generated terms, such as instances, there will be
   recomputations for everything that is ground... should combine with the
   ground and quant bit???

   Only goes down if !DAG_ground || DAG_quant?
 */
void
set_fvars_rec(TDAG DAG)
{
  unsigned i, j;
  Tstack_DAG bvars;
  /* Variables already computed */
  if (DAG_tmp_bool[DAG] || DAG_fvars[DAG])
    return;
  DAG_tmp_bool[DAG] = 1;
  /* constants and variables */
  if (!DAG_arity(DAG) && DAG_symb_type(DAG_symb(DAG)) & SYMB_VARIABLE)
    {
      /* HB remember the memory alignment */
      stack_INIT(DAG_fvars[DAG]);
      stack_push(DAG_fvars[DAG], DAG);
    }
  else if (quantifier(DAG_symb(DAG)))
    {
      set_fvars_rec(DAG_arg_last(DAG));
      /* Whether there are free vars in the quantified formula */
      if (stack_size(DAG_fvars[DAG_arg_last(DAG)]) > DAG_arity(DAG) - 1)
        {
          stack_INIT(DAG_fvars[DAG]);
          stack_INIT(bvars);
          for (i = 0; i < DAG_arity(DAG) - 1; ++i)
            stack_push(bvars, DAG_arg(DAG, i));
          stack_sort(bvars, DAG_cmp_q);
          i = j = 0;
          /* Gets the difference of free vars - bound vars */
          while (i < stack_size(DAG_fvars[DAG_arg_last(DAG)]) &&
                 j < stack_size(bvars))
            if (stack_get(DAG_fvars[DAG_arg_last(DAG)], i) <
                stack_get(bvars, j))
              {
                stack_push(DAG_fvars[DAG],
                           stack_get(DAG_fvars[DAG_arg_last(DAG)], i));
                ++i;
              }
            else if (stack_get(DAG_fvars[DAG_arg_last(DAG)], i) >
                     stack_get(bvars, j))
              j++;
            else
              {
                i++;
                j++;
              }
          while (i < stack_size(DAG_fvars[DAG_arg_last(DAG)]))
            stack_push(DAG_fvars[DAG],
                       stack_get(DAG_fvars[DAG_arg_last(DAG)], i++));
          stack_free(bvars);
        }
    }
  else
    {
      for (i = 0; i < DAG_arity(DAG); ++i)
        {
          set_fvars_rec(DAG_arg(DAG, i));
          if (DAG_fvars[DAG_arg(DAG, i)])
            {
              if (!DAG_fvars[DAG])
                stack_INIT(DAG_fvars[DAG]);
              stack_merge(DAG_fvars[DAG], DAG_fvars[DAG_arg(DAG, i)]);
            }
        }
      if (DAG_fvars[DAG])
        {
          stack_sort(DAG_fvars[DAG], DAG_cmp_q);
          stack_uniq(DAG_fvars[DAG]);
        }
    }
  if (!DAG_fvars[DAG])
    return;
}

/*--------------------------------------------------------------*/

void
set_fvars(TDAG DAG)
{
  DAG_tmp_reserve();
  set_fvars_rec(DAG);
  DAG_tmp_reset_bool(DAG);
  DAG_tmp_release();
}

/*--------------------------------------------------------------*/

#ifdef DEBUG
Tstack_DAG get_fvars(TDAG DAG)
{
  assert(!DAG_fvars[DAG] || !stack_is_empty(DAG_fvars[DAG]));
  return DAG_fvars[DAG];
}
#endif
