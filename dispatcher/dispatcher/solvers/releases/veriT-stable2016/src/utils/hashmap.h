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
  Maps through hashing
  --------------------------------------------------------------
*/
#ifndef __HASHMAP_H
#define __HASHMAP_H

#ifdef HASH_STAT
#include <stdio.h>
#endif

#include "assoc.h"
#include "types.h"

typedef struct TShashmap * Thashmap;

extern Thashmap hashmap_new(Tunsigned size, TFhash, TFequal,
			    TFfree key_free, TFfree value_free);
extern void     hashmap_free(Thashmap * Phashmap);
extern void     hashmap_erase(Thashmap hashmap);

extern void **  hashmap_lookup(Thashmap hashmap, void * key);
extern void     hashmap_insert(Thashmap hashmap, void * key, void * value);
extern void     hashmap_remove(Thashmap hashmap, void * key);
extern void     hashmap_apply(Thashmap hashmap, TFapply2 fun);

#ifdef HASH_STAT
extern void     hashmap_fprint_stats(FILE * file, Thashmap hashmap);
#endif

#endif /* __HASHMAP_H */
