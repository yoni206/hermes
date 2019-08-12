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
  table data structure
  --------------------------------------------------------------
*/

#ifndef __TABLE_H
#define __TABLE_H
#include "types.h"

/* PF A table is basically a growing array */

#define TABLE_MACRO

#ifdef TABLE_MACRO
struct TStable
{
  unsigned       last;
  unsigned       size;
  void    **P;
  unsigned       increment;
#ifdef PEDANTIC
  unsigned       unused;
#endif
};
#endif

typedef struct TStable *Ttable;

/* PF builds a table with initial size, and growing by adding increment */
Ttable    table_new(unsigned size, unsigned increment);
void      table_free(Ttable * Ptable);

/* PF initialize table such that it contains length elements, null initially */
void      table_init(Ttable table, unsigned length);
/* PF resize table such that it contains length elements.
   New elements are set to null initially */
void      table_resize(Ttable table, unsigned length);

/* PF returns number of elements in table */
#ifdef TABLE_MACRO
#define   table_length(T) T->last
#else
int       table_length(Ttable table);
#endif
/* PF returns the increment size of table */
unsigned table_increment(Ttable table);
/* PF adds P on top of table */
void      table_push(Ttable table, void *P);
/* PF returns top of table, and remove element from table */
void     *table_pop(Ttable table);
/* PF returns top of table, and let table unchanged */
void     *table_top(Ttable table);
/* PF returns 1 iff table is empty, 0 else */
#ifdef TABLE_MACRO
#define   table_empty(T) (T->last == 0)
#else
int       table_empty(Ttable table);
#endif
/* PF returns i-th element */
#ifdef TABLE_MACRO
#define   table_get(T, I) T->P[I]
#else
void     *table_get(Ttable table, unsigned i);
#endif
/* PF set i-th element */
#ifdef TABLE_MACRO
#define   table_set(T, I, E) (T)->P[I] = (void *)(E)
#else
void      table_set(Ttable table, unsigned i, void *P);
#endif
/* PF inserts P at position i */
void      table_insert(Ttable table, unsigned i, void *P);
/* PF delete i-th element */
void     *table_del(Ttable table, unsigned i);
/* PF table is set to have 0 elements */
void      table_erase(Ttable table);
/* PF applies f to every element in table */
void      table_apply(Ttable table, void (*f) (void *));
/* PF size of table is set to be exactly the number of elements,
   further adding only one element will imply a realloc */
void      table_shrink(Ttable table);

/* PF inserts P in a sorted table */
void      table_insert_sort(Ttable table, void *P, TFcmp compare);
/* PF sort table so that lookup would be in ln n */
void      table_sort(Ttable table, TFcmp compare);
/* PF return element such that lookup_function(element, criteria) = 0
   DD or NULL if no such element exist.
   Linear */
void     *table_lookup(Ttable table, TFcmp lookup, void *criteria);
/* PF return element such that compare(element, criteria) = 0.
   For sorted tables only! n ln n. */
void     *table_lookup_sort(Ttable table, TFcmp compare, void *criteria);

#endif /* __TABLE_H */
