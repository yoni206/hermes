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

#include <stdio.h>
#include <string.h>

#include "general.h"

#include "nonce.h"

/*--------------------------------------------------------------*/

void 
nonce_init(Tnonce* P, const char * prefix)
{
  P->prefix = strmake(prefix);
  P->sz = ((unsigned)strlen(P->prefix)) + 2;
  P->n = 0;
  P->resize_n = 10;
  MY_MALLOC(P->buffer, sizeof(char) * P->sz);
}

/*--------------------------------------------------------------*/

void
nonce_free(Tnonce *P)
{
  free(P->prefix);
  free(P->buffer);
}

/*--------------------------------------------------------------*/

void
nonce_next(Tnonce *P)
{
  if (P->n == P->resize_n)
    {
      P->sz += 1;
      P->resize_n *= 10;
      MY_REALLOC(P->buffer, sizeof(char) * P->sz);
    }
  sprintf(P->buffer, "%s%u", P->prefix, P->n);
  ++P->n;
}


