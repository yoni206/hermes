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

#ifdef DEBUG
#include <stdio.h>
#endif
#ifdef PEDANTIC
#include <stdio.h>
#endif
#include <strings.h>

#include "general.h"

#include "bitset.h"

#define COORD(i, w, p) ((w) = (i) >> 3, (p) = (i) & 7)

/*--------------------------------------------------------------*/

Tbs
bitset_new(unsigned size)
{
  Tbs result;
  size = (size + 7) >> 3;
  MY_MALLOC(result, sizeof(struct TSbs) + size * sizeof(unsigned char));
  result->size = size;
  bzero(result->v, size * sizeof(unsigned char));
  return result;
}

/*--------------------------------------------------------------*/

void
bitset_free(Tbs s)
{
  free(s);
}

/*--------------------------------------------------------------*/

void
bitset_insert(Tbs s, unsigned val)
{
  unsigned w, p;
  assert(val < (s->size << 3));
  COORD(val, w, p);
  s->v[w] |= (unsigned char) (1u << p);
}

/*--------------------------------------------------------------*/

void
bitset_remove(Tbs s, unsigned val)
{
  unsigned w, p;
  assert(val < (s->size << 3));
  COORD(val, w, p);
  s->v[w] &= (unsigned char) (0xff ^ (1u << p));
}

/*--------------------------------------------------------------*/

void
bitset_union(Tbs res, Tbs set1, Tbs set2)
{
  unsigned w;
  assert(res->size == set1->size && set1->size == set2->size);
  for (w = 0; w < res->size; ++w)
    res->v[w] = set1->v[w] | set2->v[w];
}

/*--------------------------------------------------------------*/

void
bitset_diff(Tbs res, Tbs set1, Tbs set2)
{
  unsigned w;
  assert(res->size == set1->size && set1->size == set2->size);
  for (w = 0; w < res->size; ++w)
    res->v[w] = set1->v[w] & (unsigned char) ~set2->v[w];
}

/*--------------------------------------------------------------*/

bool
bitset_empty(Tbs set)
{
  unsigned w;
  for (w = 0; w < set->size; ++w)
    if (set->v[w])
      return false;
  return true;
}

/*--------------------------------------------------------------*/

bool
bitset_equal(Tbs set1, Tbs set2)
{
  unsigned w;
  assert(set1->size == set2->size);
  for (w = 0; w < set1->size; ++w)
    if (set1->v[w] != set2->v[w])
      return false;
  return true;
}

/*--------------------------------------------------------------*/

bool
bitset_subseteq(Tbs set1, Tbs set2)
{
  unsigned w;
  assert(set1->size == set2->size);
  for (w = 0; w < set1->size; ++w)
    if ((set1->v[w] | set2->v[w]) != set2->v[w])
      return false;
  return true;
}

/*--------------------------------------------------------------*/

bool
bitset_in(Tbs s, unsigned val)
{
  unsigned w, p;
  assert(val < (s->size << 3));
  COORD(val, w, p);
  return s->v[w] & (1 << p);
}

/*--------------------------------------------------------------*/

unsigned
bitset_card(Tbs s)
{
  unsigned w;
  unsigned result = 0;
  for (w = 0; w < s->size; ++w)
    {
      unsigned i = s->v[w];
      while (i)
        {
          result += (i & 1);
          i >>= 1;
        }
    }
  return result;
}

/*--------------------------------------------------------------*/

#ifdef DEBUG
void
bitset_fprint(FILE * file, Tbs set)
{
  unsigned w;
  int first = 1;
  fprintf(file, "{");
  for (w = 0; w < set->size; ++w)
    {
      unsigned i;
      for (i = 0; i < 8; ++i)
        if (set->v[w] & (1 << i))
          {
            if (!first)
              fprintf(stdout, ", ");
            fprintf(stdout, "%i", w*8+i);
            first = 0;
          }
    }
  fprintf(file, "}");
}
#endif

/*--------------------------------------------------------------*/

/*

static void
bitset_print(Tbs set)
{
  bitset_fprint(stdout, set);
}

int main (void)
{
  {
    Tbs s7a = bitset_new(7);
    Tbs s7b = bitset_new(7);
    Tbs s7c = bitset_new(7);
    bitset_insert(s7a, 2);
    bitset_insert(s7a, 5);
    bitset_insert(s7b, 2);
    bitset_insert(s7b, 6);
    bitset_union(s7c, s7a, s7b);
    bitset_print(s7a);
    bitset_print(s7b);
    bitset_print(s7c);
    bitset_free(s7a);
    bitset_free(s7b);
    bitset_free(s7c);
  }
  {
    Tbs s13a = bitset_new(13);
    Tbs s13b = bitset_new(13);
    Tbs s13c = bitset_new(13);
    bitset_insert(s13a, 0);
    bitset_insert(s13a, 1);
    bitset_insert(s13a, 2);
    bitset_insert(s13a, 5);
    bitset_insert(s13b, 2);
    bitset_insert(s13b, 6);
    bitset_diff(s13c, s13a, s13b);
    bitset_print(s13a);
    bitset_print(s13b);
    bitset_print(s13c);
    bitset_free(s13a);
    bitset_free(s13b);
    bitset_free(s13c);
  }
  {
    Tbs s32a = bitset_new(32);
    Tbs s32b = bitset_new(32);
    Tbs s32c = bitset_new(32);
    bitset_insert(s32a, 0);
    bitset_insert(s32a, 1);
    bitset_insert(s32a, 2);
    bitset_insert(s32a, 5);
    bitset_insert(s32b, 2);
    bitset_insert(s32b, 6);
    bitset_diff(s32c, s32a, s32b);
    bitset_print(s32a);
    bitset_print(s32b);
    bitset_print(s32c);
    bitset_free(s32a);
    bitset_free(s32b);
    bitset_free(s32c);
  }
  return 0;
}

*/
