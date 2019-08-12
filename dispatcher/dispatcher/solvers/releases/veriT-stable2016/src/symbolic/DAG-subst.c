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

#include "DAG.h"
#include "DAG-tmp.h"
#include "DAG-subst.h"

/*
  --------------------------------------------------------------
  Substitution
  --------------------------------------------------------------
*/

bool
DAG_tmp_subst(TDAG src)
{
  unsigned i, res = 0;
  if (DAG_tmp_DAG[src])
    return DAG_tmp_DAG[src] != src;
  for (i = 0; i < DAG_arity(src); i++)
    res |= DAG_tmp_subst(DAG_arg(src, i));
  if (res)
    {
      TDAG *PDAG, tmp;
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); i++)
        PDAG[i] = DAG_tmp_DAG[DAG_arg(src, i)];
      tmp = DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
      /* PF tmp is necessary since DAG_new may change DAG_tmp_DAG */
      DAG_tmp_DAG[src] = tmp;
      return true;
    }
  DAG_tmp_DAG[src] = src;
  return false;
}

/*--------------------------------------------------------------*/

bool
DAG_tmp_subst_cond(TDAG src, bool (*cont)(TDAG DAG))
{
  unsigned i, res = 0;
  if (DAG_tmp_DAG[src])
    return DAG_tmp_DAG[src] != src;
  if (cont(src))
    for (i = 0; i < DAG_arity(src); i++)
      res |= DAG_tmp_subst(DAG_arg(src, i));
  if (res)
    {
      TDAG *PDAG, tmp;
      MY_MALLOC(PDAG, DAG_arity(src) * sizeof(TDAG));
      for (i = 0; i < DAG_arity(src); i++)
        PDAG[i] = DAG_tmp_DAG[DAG_arg(src, i)];
      tmp = DAG_new(DAG_symb(src), DAG_arity(src), PDAG);
      /* PF tmp is necessary since DAG_new may change DAG_tmp_DAG */
      DAG_tmp_DAG[src] = tmp;
      return true;
    }
  DAG_tmp_DAG[src] = src;
  return false;
}

/*--------------------------------------------------------------*/

TDAG
DAG_subst(TDAG src, TDAG origin, TDAG subst)
{
  TDAG dest;
  DAG_tmp_reserve();
  DAG_tmp_DAG[origin] = subst;
  DAG_tmp_DAG[subst] = subst;
  DAG_tmp_subst(src);
  dest = DAG_tmp_DAG[src];
  DAG_tmp_reset_DAG(src);
  DAG_tmp_reset_DAG(origin);
  DAG_tmp_reset_DAG(subst);
  DAG_tmp_release();
  return dest;
}

/*--------------------------------------------------------------*/

TDAG
DAG_subst_multiple(TDAG src, unsigned n, TDAG * origin, TDAG * subst)
{
  TDAG dest;
  unsigned i;
  DAG_tmp_reserve();
  for (i = 0; i < n; ++i)
    {
      DAG_tmp_DAG[origin[i]] = subst[i];
      DAG_tmp_DAG[subst[i]] = subst[i];
    }
  DAG_tmp_subst(src);
  dest = DAG_tmp_DAG[src];
  DAG_tmp_reset_DAG(src);
  for (i = 0; i < n; ++i)
    {
      DAG_tmp_reset_DAG(origin[i]);
      DAG_tmp_reset_DAG(subst[i]);
    }
  DAG_tmp_release();
  return dest;
}

/*--------------------------------------------------------------*/

static bool
DAG_contain_aux(TDAG src)
{
  unsigned i;
  bool res = false;
  if (DAG_tmp_bool[src])
    return (DAG_tmp_bool[src] == 2);
  for (i = 0; i < DAG_arity(src); i++)
    res |= DAG_contain_aux(DAG_arg(src, i));
  DAG_tmp_bool[src] = 1;
  return res;
}

/*--------------------------------------------------------------*/

bool
DAG_contain(TDAG src, TDAG find)
{
  bool res;
  DAG_tmp_reserve();
  DAG_tmp_bool[find] = 2;
  res = DAG_contain_aux(src);
  DAG_tmp_reset_bool(find);
  DAG_tmp_reset_bool(src);
  DAG_tmp_release();
  return res;
}
