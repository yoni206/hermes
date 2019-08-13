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

#include "recursion.h"

#include "LA-pre.h"

#include "totality.h"

#define DAG_LEQ(a, b) DAG_new_binary(PREDICATE_LEQ, a, b)

/*--------------------------------------------------------------*/

extern bool LA_enable_lemmas_totality;

static TDAG
rewrite_eq(TDAG src)
{
  TDAG dest;
  if (DAG_symb(src) != PREDICATE_EQ)
    return src;
  if (LA_enable_lemmas_totality)
    {
      TDAG DAG0 = DAG_LEQ(DAG_arg0(src), DAG_arg1(src));
      TDAG DAG1 = DAG_LEQ(DAG_arg1(src), DAG_arg0(src));
      totality_register(DAG_or2(DAG0, DAG1));
    }
  dest = DAG_dup(DAG_and2(DAG_LEQ(DAG_arg0(src), DAG_arg1(src)),
                          DAG_LEQ(DAG_arg1(src), DAG_arg0(src))));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

void
LA_pre_array(unsigned n, TDAG * Psrc)
{
  structural_recursion_array(n, Psrc, rewrite_eq);
}

/*--------------------------------------------------------------*/
