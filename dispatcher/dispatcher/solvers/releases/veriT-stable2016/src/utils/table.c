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
  Table data structure
  --------------------------------------------------------------
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "veriT-qsort.h"

#include "general.h"
#include "types.h"

#include "table.h"

#ifndef TABLE_MACRO
struct TStable
{
  unsigned last;
  unsigned size;
  unsigned increment;
  void **P;
};
#endif

/*--------------------------------------------------------------*/

Ttable
table_new(unsigned size, unsigned increment)
{
  Ttable table;
  MY_MALLOC(table, sizeof(struct TStable));
  table->last = 0;
  table->size = size;
  table->increment = increment;
  MY_MALLOC(table->P, size * sizeof(void *));
  return table;
}

/*--------------------------------------------------------------*/

void
table_free(Ttable * Ptable)
{
  if (!*Ptable)
    return;
  free((*Ptable)->P);
  free(*Ptable);
  (*Ptable) = NULL;
}

/*--------------------------------------------------------------*/

void
table_init(Ttable table, unsigned length)
{
  assert(table);
  if (length > table->size)
    {
      table->size = length;
      MY_REALLOC(table->P, table->size * sizeof(void *));
    }
  table->last = table->size;
  memset(table->P, 0, table->size * sizeof(void *));
}

/*--------------------------------------------------------------*/

void
table_resize(Ttable table, unsigned length)
{
  assert(table);
  if (length > table->size)
    {
      MY_REALLOC(table->P, length * sizeof(void *));
      table->size = length;
    }
  if (length > table->last)
    memset(table->P + table->last, 0,
	   (length - table->last) * sizeof(void *));
  table->last = length;
}

/*--------------------------------------------------------------*/

#ifndef TABLE_MACRO
unsigned
table_length(Ttable table)
{
  assert(table);
  return table->last;
}
#endif

/*--------------------------------------------------------------*/

unsigned
table_increment(Ttable table)
{
  assert(table);
  return table->increment;
}

/*--------------------------------------------------------------*/

void
table_push(Ttable table, void *P)
{
  assert(table);
  if (table->last == table->size)
    {
      table->size = table->size + table->increment;
      MY_REALLOC(table->P, table->size * sizeof(void *));
    }
  table->P[table->last++] = P;
}

/*--------------------------------------------------------------*/

void *
table_pop(Ttable table)
{
  assert(table);
  if (table->last > 0)
    {
      table->last--;
      return table->P[table->last];
    }
  my_error("table_pop: empty table\n");
  return NULL;
}

/*--------------------------------------------------------------*/

void *
table_top(Ttable table)
{
  assert(table);
  if (table->last > 0)
    return table->P[table->last - 1];
  my_error("table_top: empty table\n");
  return NULL;
}

/*--------------------------------------------------------------*/

#ifndef TABLE_MACRO
int
table_empty(Ttable table)
{
  assert (table);
  return table->last == 0;
}
#endif

/*--------------------------------------------------------------*/

#ifndef TABLE_MACRO
void *
table_get(Ttable table, unsigned i)
{
  assert(table);
  if (i >= table->last)
    my_error("table: access out of bounds\n");
  return table->P[i];
}
#endif

/*--------------------------------------------------------------*/

#ifndef TABLE_MACRO
void
table_set(Ttable table, unsigned i, void *P)
{
  assert(table);
  assert(i >= 0);
  assert(i < table->size);
  table->P[i] = P;
}
#endif

/*--------------------------------------------------------------*/

void
table_insert(Ttable table, unsigned i, void *P)
{
  unsigned j;
  assert(table);
  assert(i < table->size);
  if (table->last == table->size)
    {
      table->size = table->size + table->increment;
      MY_REALLOC(table->P, table->size * sizeof(void *));
    }
  for (j = table->last; j > i; j--)
    table->P[j] = table->P[j - 1];
  table->P[i] = P;
  table->last++;
}

/*--------------------------------------------------------------*/

void
table_insert_sort(Ttable table, void *P, TFcmp compare)
{
  unsigned i, j;
  assert(table);
  for (i = 0; i < table->last && compare(P, table->P[i]) < 0; i++);
  if (table->last == table->size)
    {
      table->size += table->increment;
      MY_REALLOC(table->P, table->size * sizeof(void *));
    }
  for (j = table->last; j > i; j--)
    table->P[j] = table->P[j - 1];
  table->P[i] = P;
  table->last++;
}

/*--------------------------------------------------------------*/

void *
table_del(Ttable table, unsigned i)
{
  unsigned j;
  void *P;
  assert(table);
  assert(i < table->size);
  P = table->P[i];
  for (j = i; j < table->last - 1; j++)
    table->P[j] = table->P[j + 1];
  table->P[j] = NULL;
  table->last--;
  return P;
}

/*--------------------------------------------------------------*/

void
table_erase(Ttable table)
{
  assert(table);
  table->last = 0;
}

/*--------------------------------------------------------------*/

void
table_apply(Ttable table, void (*f) (void *))
{
  register unsigned i;
  assert(table);
  for (i = 0; i < table->last; i++)
    f(table->P[i]);
}

/*--------------------------------------------------------------*/

void
table_shrink(Ttable table)
{
  assert(table);
  if (table->last < table->size)
    {
      table->size = table->last;
      MY_REALLOC(table->P, table->size * sizeof(void *));
    }
}

/*--------------------------------------------------------------*/

void
table_sort(Ttable table, TFcmp compare)
{
  assert(table);
  if (table->last > 1)
    veriT_qsort(table->P, table->last, 
		sizeof(void *), (int (*) (const void *, const void*)) compare);
}

/*--------------------------------------------------------------*/

void *
table_lookup(Ttable table, TFcmp lookup, void *criteria)
{
  unsigned i;
  assert(table);
  for (i = 0; i < table->last; i++)
    if (lookup(table->P[i], criteria) == 0)
      return table->P[i];
  return NULL;
}

/*--------------------------------------------------------------*/

void *
table_lookup_sort(Ttable table, TFcmp compare, void *criteria)
{
  Tsigned i, j, m, c;
  assert(table);
  if (table->last == 0)
    return NULL;
  i = 0;
  j = table->last - 1;
  while (i < j)
    {
      m = (i + j) / 2;
      c = compare(table->P[m], criteria);
      if (c == 0)
	return table->P[m];
      if (c > 0)
	i = m + 1;
      else
	j = m - 1;
    }
  if (compare(table->P[i], criteria) == 0)
    return table->P[i];
  return NULL;
}

/*--------------------------------------------------------------*/
