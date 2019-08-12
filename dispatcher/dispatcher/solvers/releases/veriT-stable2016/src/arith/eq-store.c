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


#include <string.h>

#include "general.h"
#include "hash.h"

#include "eq-store.h"

typedef struct Teqvar
{
  bool lemma_generated;
  Tsimplex_var var;
  TDAG DAG[2];
} Teqvar;

static Teqvar **var_to_eq = NULL;
static unsigned var_to_eq_size = 0;
static Thash eq_to_var = NULL;

/*
  --------------------------------------------------------------
  hash helpers
  --------------------------------------------------------------
*/

static int
eqvar_eq(Teqvar *eqvar1, Teqvar *eqvar2)
{
  return eqvar1->DAG[0] == eqvar2->DAG[0] &&
    eqvar1->DAG[1] == eqvar2->DAG[1];
}

/*--------------------------------------------------------------*/

static unsigned
eqvar_hash(Teqvar *eqvar)
{
  return DAG_hash(eqvar->DAG[0]) ^ DAG_hash(eqvar->DAG[1]); 
}

/*--------------------------------------------------------------*/

static void
eqvar_free(Teqvar *eqvar)
{
  free(eqvar);
}

/*
  --------------------------------------------------------------
  Public
  --------------------------------------------------------------
*/

void
eq_store(TDAG DAG0, TDAG DAG1, Tsimplex_var var)
{
  Teqvar eqvar, *Peqvar;
  assert(DAG0 < DAG1);
  eqvar.DAG[0] = DAG0;
  eqvar.DAG[1] = DAG1;
  Peqvar = hash_lookup(eq_to_var, &eqvar);
  if (Peqvar)
    {
      assert(!Peqvar->var);
      Peqvar->var = var;
    }
  else
    {
      MY_MALLOC(Peqvar, sizeof(Teqvar));
      Peqvar->DAG[0] = DAG0;
      Peqvar->DAG[1] = DAG1;
      Peqvar->lemma_generated = false;
      Peqvar->var = var;
      hash_insert(eq_to_var, Peqvar);
    }
  if (var_to_eq_size <= var)
    {
      unsigned old_size = var_to_eq_size;
      while (var_to_eq_size <= var)
	var_to_eq_size *= 2;
      MY_REALLOC(var_to_eq, var_to_eq_size * sizeof(Teqvar *));
      memset(var_to_eq + old_size, 0,
	     (var_to_eq_size - old_size) * sizeof(Teqvar *));
    }
  assert(!var_to_eq[var]);
  var_to_eq[var] = Peqvar;
}

/*--------------------------------------------------------------*/

Tsimplex_var
eq_get_from_DAG(TDAG DAG0, TDAG DAG1)
{
  Teqvar eqvar, *Peqvar;
  assert(DAG0 < DAG1);
  eqvar.DAG[0] = DAG0;
  eqvar.DAG[1] = DAG1;
  Peqvar = hash_lookup(eq_to_var, &eqvar);
  if (!Peqvar)
    return 0;
  return Peqvar->var;
}

/*--------------------------------------------------------------*/

void
eq_get_from_var(Tsimplex_var var, TDAG *PDAG0, TDAG *PDAG1)
{
 if (var_to_eq_size <= var)
   my_error("eq_get_from_var: internal error\n");
 *PDAG0 = var_to_eq[var]->DAG[0];
 *PDAG1 = var_to_eq[var]->DAG[1];
}

/*--------------------------------------------------------------*/

void
eq_remove(Tsimplex_var var)
{
  Teqvar *Peqvar = var_to_eq[var];
  var_to_eq[var] = NULL;
  if (!Peqvar->lemma_generated)
    hash_remove(eq_to_var, Peqvar);
}

/*--------------------------------------------------------------*/

void
eq_set_lemma_generated(TDAG DAG0, TDAG DAG1)
{
  Teqvar eqvar, *Peqvar;
  assert(DAG0 < DAG1);
  eqvar.DAG[0] = DAG0;
  eqvar.DAG[1] = DAG1;
  Peqvar = hash_lookup(eq_to_var, &eqvar);
  if (Peqvar)
    {
      assert(!Peqvar->lemma_generated);
      Peqvar->lemma_generated = true;
    }
  else
    {
      MY_MALLOC(Peqvar, sizeof(Teqvar));
      Peqvar->DAG[0] = DAG0;
      Peqvar->DAG[1] = DAG1;
      Peqvar->var = 0;
      Peqvar->lemma_generated = true;
      hash_insert(eq_to_var, Peqvar);
    }
}

/*--------------------------------------------------------------*/

bool
eq_get_lemma_generated(TDAG DAG0, TDAG DAG1)
{
  Teqvar eqvar, *Peqvar;
  assert(DAG0 < DAG1);
  eqvar.DAG[0] = DAG0;
  eqvar.DAG[1] = DAG1;
  Peqvar = hash_lookup(eq_to_var, &eqvar);
  if (!Peqvar)
    return 0;
  return Peqvar->lemma_generated;
}

/*--------------------------------------------------------------*/

bool
eq_test(Tsimplex_var var)
{
  return var < var_to_eq_size && var_to_eq[var] != NULL;
}

/*--------------------------------------------------------------*/

void
eq_init(void)
{
  eq_to_var = hash_new(32, (TFhash) eqvar_hash,
		       (TFequal) eqvar_eq, (TFfree) eqvar_free);

  MY_MALLOC(var_to_eq, 4 * sizeof(Teqvar *));
  memset(var_to_eq, 0, 4 * sizeof(Teqvar *));
  var_to_eq_size = 4;
  
}

/*--------------------------------------------------------------*/

static void
reset_var(Teqvar *eqvar)
{
  if (!eqvar->var)
    return;
  var_to_eq[eqvar->var] = 0;
  eqvar->var = 0;
}

/*--------------------------------------------------------------*/

void
eq_reset_var(void)
{
  hash_apply(eq_to_var, (TFapply) reset_var);
}

/*--------------------------------------------------------------*/

void
eq_done(void)
{
  hash_free(&eq_to_var);
  free(var_to_eq);
  var_to_eq = NULL;
}
