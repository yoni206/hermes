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
  Hash tables
  --------------------------------------------------------------
*/

#include <stdio.h>

/**
   \brief when set, this macro activates statistics */
/* #define H_STAT */

/* Required definitions
   TYPE the type of elements in the h table
   TYPE_EXT the extension to denote h functions
   TYPE_KEY hash key function for elements (may be inlined)
   TYPE_EQ equality function between elements (may be inlined)
   TYPE_NULL the null element of TYPE

   Optional definitions
   H_STAT to activate statistics
*/

#ifndef TYPE
#error TYPE not defined
#endif
#ifndef TYPE_EXT
#error TYPE_EXT not defined
#endif
#ifndef TYPE_KEY
#error TYPE_KEY not defined
#endif
#ifndef TYPE_EQ
#error TYPE_EQ not defined
#endif
#ifndef TYPE_NULL
#error TYPE_NULL not defined
#endif

#define CC2(A,B) A ## B
/* force prescan */
#define CC(A,B) CC2(A,B)
#define CC3(A,B,C) CC(CC(A,B),C)
#define EXT(A) CC3(A,_,TYPE_EXT)
#define EXTH(A) CC3(h_,TYPE_EXT,A)

typedef unsigned Tbucket;

#define H_FACTOR 2

typedef struct EXT(TSbucket) {
  unsigned k; /*< The key */
  Tbucket b;  /*< The next bucket */
  TYPE e;     /*< The element */
} EXT(TSbucket);

/**
   \brief main data structure for hash
   \remark the allocated size for bucket is size << H_FACTOR 
   \remark the allocated size for Sbucket is size
   \remark bucket 0 is unused, and thus there can be at most size - 1 elements
   in h table
   \remark the size of the arrays storing bucket pointers and bucket 
   structures is a power of 2, indices are taken from hash using bit masks.
*/
struct EXT(TSh)
{
  unsigned nb;             /*< Number of elements in the hash table */
  unsigned mask;           /*< mask to obtain index from hash */
  unsigned size;           /*< number of allocated place in next arrays */
  unsigned first;
  Tbucket * bucket;        /*< array of first bucket pointers */
  EXT(TSbucket) * Sbucket; /*< array of bucket structures */
#ifdef H_STAT
  unsigned insert_collision;
  unsigned insert_total;
  unsigned max_collision;
  unsigned eq_key;
#endif
};
typedef struct EXT(TSh) *EXT(Th);

/*
  --------------------------------------------------------------
  Two private functions
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief double the allocated size for h table */
static inline void
EXTH(_double_size)(EXT(Th) h)
{
  unsigned i;
  assert(h->first == 0);
  assert(h->nb == h->size);
  MY_REALLOC(h->bucket, 2 * (h->size << H_FACTOR) * sizeof(Tbucket));
  memset(h->bucket + (h->size << H_FACTOR), 0,
	 (h->size << H_FACTOR) * sizeof(Tbucket));
  MY_REALLOC(h->Sbucket, 2 * h->size * sizeof(EXT(TSbucket)));
  for (i = 0; i < h->size; i++)
    {
      Tbucket *Pb = &(h->bucket[i]);
      unsigned k;
      for (; *Pb; )
	if ((k = h->Sbucket[*Pb].k & h->mask) != i)
	  {
	    Tbucket b = *Pb;
	    *Pb = h->Sbucket[*Pb].b;
	    h->Sbucket[b].b = h->bucket[k];
	    h->bucket[k] = b;
	  }
	else
	  Pb = &(h->Sbucket[*Pb].b);
    }
  h->size <<= 1;
  h->mask = (h->mask << 1) | 1;
  for (i = h->size >> 1; i < h->size - 1; i++)
    h->Sbucket[i].b = i + 1;
  h->Sbucket[i].b = 0;
  h->first = h->size >> 1;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief create a new container
   \param h the hash table
   \param k the (hash) key
   \param e the element
   \param b the next bucket
   \return the new bucket */
static inline Tbucket
EXTH(_bucket_new)(EXT(Th) h, unsigned k, TYPE e, Tbucket b)
{
  Tbucket nb = h->first;
  /* function being called only in h_push, and h_double_size having being
     called if needed, there should always be a free bucket */
  assert(h->first);
  h->first = h->Sbucket[nb].b;
  h->Sbucket[nb].k = k;
  h->Sbucket[nb].b = b;
  h->Sbucket[nb].e = e;
  return nb;
}

/*
  --------------------------------------------------------------
  Public functions
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief creates a new hash table
   \param power states the initial size which is 1 << power
   \return the h table */
static inline EXT(Th)
EXTH(_new)(unsigned power)
{
  unsigned i;
  EXT(Th) h;
  MY_MALLOC(h, sizeof(struct EXT(TSh)));
  h->nb = 0;
  h->size = 1u << power;
  h->mask = (1u << power) - 1;
  MY_MALLOC(h->bucket, (h->size << H_FACTOR) * sizeof(Tbucket));
  /* PF caution: keep following line even if duplicate in SAFE mode */
  memset(h->bucket, 0, (h->size << H_FACTOR) * sizeof(Tbucket));
  MY_MALLOC(h->Sbucket, h->size * sizeof(EXT(TSbucket)));
  for (i = 1; i < h->size - 1; i++)
    h->Sbucket[i].b = i + 1;
  h->Sbucket[i].b = 0;
  h->first = 1;
#ifdef HASH_STAT
  h->insert_collision = 0;
  h->insert_total = 0;
  h->max_collision = 0;
  h->eq_key = 0;
#endif
  return h;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief release table and set h to NULL
   \param Ph pointer to hash table
   \remark if elements have to be freed, used h_apply before */
static inline void
EXTH(_free)(EXT(Th) * Ph)
{
  free((*Ph)->Sbucket);
  free((*Ph)->bucket);
  free(*Ph);
  *Ph = NULL;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief apply function f on every element in h table
   \param h the hash table
   \param f the function
   \remark conveniently use to free all elements from a hash table */
static inline void
EXTH(_apply)(EXT(Th) h, void (*f) (TYPE))
{
  unsigned i;
  Tbucket b;
  for (i = 0; i < (h->size << H_FACTOR); i++)
    for (b = h->bucket[i]; b; b = h->Sbucket[b].b)
      f(h->Sbucket[b].e);
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief insert element in h table
   \param h the hash table
   \param e the element */
static inline void
EXTH(_push)(EXT(Th) h, TYPE e)
{
  Tbucket b;
  unsigned k = TYPE_KEY(e);
  h->nb++;
  if (h->nb >= h->size)
    EXTH(_double_size)(h);
  /* order of assignment evaluation is unknown: keep variable b */
  b = EXTH(_bucket_new)(h, k, e, h->bucket[k & h->mask]);
  h->bucket[k & h->mask] = b;
#ifdef HASH_STAT
  {
    unsigned i = 0;
    h->insert_total++;
    if (h->Sbucket[b].b)
      h->insert_collision++;
    for ( ; b = h->Sbucket[b].b; i++)
      if (h->Sbucket[b].k == k)
	h->eq_key++;
    if (h->max_collision < i)
      h->max_collision = i;
  }
#endif
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief look for an element in h table
   \param h the hash table
   \param e the element
   \return either the element if found or TYPE_NULL */
static inline TYPE
EXTH(_get)(EXT(Th) h, TYPE e)
{
  Tbucket b;
  unsigned k = TYPE_KEY(e);
  for (b = h->bucket[k & h->mask]; b; b = h->Sbucket[b].b)
    if ((k == h->Sbucket[b].k) && (TYPE_EQ(e, h->Sbucket[b].e)))
      return h->Sbucket[b].e;
  return TYPE_NULL;
}

/*--------------------------------------------------------------*/

#if 0

/**
   \author Pascal Fontaine
   \brief remove an element in h table
   \param h the hash table
   \param e the element */
static inline TYPE
EXTH(_pop)(EXT(Th) h, TYPE e)
{
  Tbucket *Pb;
  unsigned k = TYPE_KEY(e);
  for (Pb = &(h->bucket[k & h->mask]); *Pb; Pb = &(h->Sbucket[*Pb].b))
    if ((k == h->Sbucket[*Pb].k) && (TYPE_EQ(e, h->Sbucket[*Pb].e)))
      {
	Tbucket b = *Pb;
	*Pb = h->Sbucket[*Pb].b;
	h->nb--;
	h->Sbucket[b].b = h->first;
	h->first = b;
	return h->Sbucket[b].e;
      }
  my_error("hash_remove: object not found\n"); 
  return TYPE_NULL;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief print some statistics about hash table use
   \param h the hash table */
static inline void
EXTH(_print_stats)(EXT(Th) h)
{
#ifdef H_STAT
  my_message("Hash stats: %u, %u/%u (%u-%u)\n",
	     h->size,
	     h->insert_total,
	     h->insert_collision,
	     h->max_collision,
	     h->eq_key);
#else
#ifdef PEDANTIC
  /* PF avoid a warning when compiling in pedantic mode */
  printf("%p\n", (void *) h);
#endif
#endif
}

#endif

#undef CC2
#undef CC
#undef CC3
#undef EXT
#undef EXTH
#undef H_FACTOR

