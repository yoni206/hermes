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
  Module to link one DAG to symbols
  Used for macros, defined functions, and variable handling
  --------------------------------------------------------------
*/

#include <string.h>

#include "DAG.h"
#include "DAG-symb.h"

#include "DAG-symb-DAG.h"

TDAG * DAG_symb_DAG = NULL;

/*--------------------------------------------------------------*/

static void
DAG_symb_DAG_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
#ifdef DMEM
  MY_REALLOC_DMEM(DAG_symb_DAG, new_alloc * sizeof(TDAG),
		  old_alloc * sizeof(TDAG));
#else
  MY_REALLOC(DAG_symb_DAG, new_alloc * sizeof(TDAG));
#endif
  if (new_alloc > old_alloc)
    memset(DAG_symb_DAG + old_alloc, 0, (new_alloc - old_alloc) * sizeof(TDAG));
  /*
  else
    {
      unsigned i;
      for (i = new_alloc; i < old_alloc; i++)
	if ((DAG_symb_type(symb) | SYMB_INTERPRETED) && DAG_symb_DAG[symb])
	  DAG_free(DAG_symb_DAG[symb]);
    }
  */
}

/*--------------------------------------------------------------*/

static Tstack_symb macro_symb = NULL;

void
DAG_symb_macro(Tsymb symb, TDAG DAG)
{
  DAG_symb_type(symb) |= SYMB_INTERPRETED;
  DAG_symb_DAG[symb] = DAG;
  stack_push(macro_symb, symb);
}

/*
  --------------------------------------------------------------
  Initialization-release functions
  --------------------------------------------------------------
*/

void
DAG_symb_DAG_init(void)
{
  DAG_symb_set_hook_resize(DAG_symb_DAG_hook_resize);
  stack_INIT(macro_symb);
}

/*--------------------------------------------------------------*/

void
DAG_symb_DAG_done(void)
{
  unsigned i;
  for (i = 0; i < stack_size(macro_symb); i++)
    DAG_free(DAG_symb_DAG[stack_get(macro_symb, i)]);
  stack_free(macro_symb);
}
