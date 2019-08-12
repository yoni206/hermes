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

#include "eq-norm.h"
#include "recursion.h"

/* #define DEBUG_EQ_NORM */

/*--------------------------------------------------------------*/

static TDAG
eq_norm_aux(TDAG src)
{
  TDAG dest;
  if (DAG_symb(src) != PREDICATE_EQ || DAG_sort(DAG_arg0(src)) != SORT_BOOLEAN)
    return src;
  dest = DAG_dup(DAG_equiv(DAG_arg0(src), DAG_arg1(src)));
  DAG_free(src);
  return dest;
}

/*--------------------------------------------------------------*/

TDAG
eq_norm(TDAG src)
{
  TDAG dest;
#ifdef DEBUG_EQ_NORM
  my_DAG_message("Before equality normalization\n%D\n", src);
#endif
  dest = structural_recursion(src, eq_norm_aux);
#ifdef DEBUG_EQ_NORM
  my_DAG_message("After equality normalization\n%D\n", dest);
#endif
  return dest;
}

/*--------------------------------------------------------------*/
