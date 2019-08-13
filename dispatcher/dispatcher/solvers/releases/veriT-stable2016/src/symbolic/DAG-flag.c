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
  Obsolete functions about DAG and symbols
  --------------------------------------------------------------
*/

#include <string.h>

#include "general.h"

#include "DAG.h"
#include "DAG-ptr.h"

#include "DAG-flag.h"

int *obsolete_DAG_flag = NULL;
void **obsolete_DAG_Pflag = NULL;

static unsigned size = 0;

/*--------------------------------------------------------------*/

void
DAG_free_Pflag(TDAG src)
{
  unsigned i;
  if (!DAG_Pflag(src))
    return;
  for (i = 0; i < DAG_arity(src); i++)
    DAG_free_Pflag(DAG_arg(src, i));
  DAG_free(DAG_of_ptr(DAG_Pflag(src)));
  DAG_Pflag_set(src, NULL);
}

/*--------------------------------------------------------------*/

void
DAG_reset_flag(TDAG src)
{
  unsigned i;
  if (!DAG_flag(src))
    return;
  for (i = 0; i < DAG_arity(src); i++)
    DAG_reset_flag(DAG_arg(src, i));
  DAG_flag_set(src, 0);
}

/*--------------------------------------------------------------*/

void
DAG_reset_Pflag(TDAG src)
{
  unsigned i;
  if (!DAG_Pflag(src))
    return;
  for (i = 0; i < DAG_arity(src); i++)
    DAG_reset_Pflag(DAG_arg(src, i));
  DAG_Pflag_set(src, NULL);
}

/*--------------------------------------------------------------*/

void
DAG_check_Pflag(void)
{
  unsigned i;
  for (i = 0; i < size; i++)
    assert(!DAG_Pflag(i));
}

/*--------------------------------------------------------------*/

static void
DAG_flag_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
  assert(size == old_alloc);
#ifndef DMEM
  MY_REALLOC(obsolete_DAG_flag, new_alloc * sizeof(int));
  MY_REALLOC(obsolete_DAG_Pflag, new_alloc * sizeof(void *));
#else
  MY_REALLOC_DMEM(obsolete_DAG_flag, new_alloc * sizeof(int),
		  old_alloc * sizeof(int));
  MY_REALLOC_DMEM(obsolete_DAG_Pflag, new_alloc * sizeof(void *),
		  old_alloc * sizeof(void *));
#endif
  if (new_alloc > old_alloc)
    {
      memset(obsolete_DAG_flag + old_alloc, 0,
	     (new_alloc - old_alloc) * sizeof(int));
      memset(obsolete_DAG_Pflag + old_alloc, 0,
	     (new_alloc - old_alloc) * sizeof(void *));
    }
  size = new_alloc;
}

/*--------------------------------------------------------------*/

void
DAG_flag_init(void)
{
  DAG_set_hook_resize(DAG_flag_hook_resize);
}

/*--------------------------------------------------------------*/

void
DAG_flag_done(void)
{
}


