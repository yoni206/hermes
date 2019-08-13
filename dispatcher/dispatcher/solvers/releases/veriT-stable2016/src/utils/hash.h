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

#ifndef __HASH_H
#define __HASH_H

#include <stdio.h>

#include "types.h"

/* PF do the size of hash tables grow? */
#define HASH_ADAPTIVE_SIZE

/* PF print statistics about hash tables  */
/* #define HASH_STAT */

typedef struct TShash *Thash;

/* PF creates a new hash table,
   initially of size given in the first argument,
   hash_function is used to get the hash key from objects
   equal is the equality function between objects
   free function is the function used to free objects when table released */
Thash     hash_new(unsigned size,
		   TFhash hash_function,
		   TFequal equal,
		   TFfree free_function);
/* PF Release table and apply free_function to all objects in table */
void      hash_free(Thash * Phash);

/* PF look for an object that is equal to P */
void     *hash_lookup(Thash hash, void *P);
/* PF insert object P */
void      hash_insert(Thash hash, void *P);
/* PF remove object P */
void      hash_remove(Thash hash, void *P);
/* PF Empty table contents */
void      hash_erase(Thash hash);

/* PF apply function f on every pointer in hash table */
void      hash_apply(Thash hash, TFapply f);
/* PF print some statistics about hash table use */
void      hash_print_stats(Thash hash);

#endif /* __HASH_H */
