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

#include "config.h"

#include "h-util.h"

/*--------------------------------------------------------------*/

unsigned
hash_one_at_a_time(char * str)
{
  unsigned hash;
  for (hash = 0; *str; str++)
    {
      hash += (unsigned) *str;
      hash += (hash << 10);
      hash ^= (hash >> 6);
    }
  hash += (hash << 3);
  hash ^= (hash >> 11);
  hash += (hash << 15);
  return hash;
}

/*--------------------------------------------------------------*/

unsigned
hash_one_at_a_time_u(unsigned u)
{
  unsigned hash;
  hash = u & 0xFF;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  hash += (u & 0xFF00)>>8;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  hash += (u & 0xFF0000)>>16;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  hash += (u & 0xFF000000)>>24;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  hash += (hash << 3);
  hash ^= (hash >> 11);
  hash += (hash << 15);
  return hash;
}

/*--------------------------------------------------------------*/

unsigned
hash_one_at_a_time_inc(unsigned hash, char * str)
{
  for (; *str; str++)
    {
      hash += (unsigned) *str;
      hash += (hash << 10);
      hash ^= (hash >> 6);
    }
  return hash;
}

/*--------------------------------------------------------------*/

#ifndef HASH_MACRO
unsigned
hash_one_at_a_time_u_inc(unsigned hash, unsigned u)
{
  hash += u & 0xFF;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  hash += (u & 0xFF00)>>8;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  hash += (u & 0xFF0000)>>16;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  hash += (u & 0xFF000000)>>24;
  hash += (hash << 10);
  hash ^= (hash >> 6);
  return hash;
}
#endif

/*--------------------------------------------------------------*/

unsigned
hash_one_at_a_time_inc_end(unsigned hash)
{
  hash += (hash << 3);
  hash ^= (hash >> 11);
  hash += (hash << 15);
  return hash;
}
