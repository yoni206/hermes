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

#include "DAG.h"
#ifdef DEBUG
#include "DAG-print.h"
#endif

#include "DAG-tmp.h"

char * DAG_tmp = NULL;

#define SIZE1 (sizeof(void *))
#define SIZE2 (sizeof(TDAG) + sizeof(unsigned))
#define DAG_MAX_SIZE (SIZE1<=SIZE2?SIZE2:SIZE1)

/*--------------------------------------------------------------*/
#ifdef DEBUG

static unsigned DAG_size = 0;
static unsigned reserved = 0;

void
DAG_tmp_reserve(void)
{
  assert(!reserved);
  reserved = 1;
  MY_MALLOC(DAG_tmp, DAG_size * DAG_MAX_SIZE);
  memset(DAG_tmp, 0, DAG_size * DAG_MAX_SIZE);
}

/*--------------------------------------------------------------*/

void
DAG_tmp_release(void)
{
  unsigned i;
  assert(reserved);
  for (i = 0; i < DAG_size * DAG_MAX_SIZE; i++)
    assert(!DAG_tmp[i]);
  reserved = 0;
  free(DAG_tmp);
  DAG_tmp = NULL;
}

#endif
/*--------------------------------------------------------------*/

static void
DAG_tmp_hook_resize(unsigned old_alloc, unsigned new_alloc)
{
#ifdef DEBUG
  DAG_size = new_alloc;
  if (!reserved) return;
#endif
#ifdef DMEM
  MY_REALLOC_DMEM(DAG_tmp, new_alloc * DAG_MAX_SIZE, old_alloc * DAG_MAX_SIZE);
#else
  MY_REALLOC(DAG_tmp, new_alloc * DAG_MAX_SIZE);
#endif
  if (new_alloc > old_alloc)
    memset(DAG_tmp + old_alloc * DAG_MAX_SIZE, 0,
           (new_alloc - old_alloc) * DAG_MAX_SIZE);
}

/*--------------------------------------------------------------*/

void
DAG_tmp_reset_bool(TDAG DAG)
{
  unsigned i;
  if (!DAG_tmp_bool[DAG])
    return;
  DAG_tmp_bool[DAG] = 0;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_reset_bool(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

void
DAG_tmp_reset_DAG(TDAG DAG)
{
  unsigned i;
  if (!DAG_tmp_DAG[DAG])
    return;
  DAG_tmp_DAG[DAG] = DAG_NULL;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_reset_DAG(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

void
DAG_tmp_free_DAG(TDAG DAG)
{
  unsigned i;
  if (!DAG_tmp_DAG[DAG])
    return;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_free_DAG(DAG_arg(DAG, i));
  DAG_free(DAG_tmp_DAG[DAG]);
  DAG_tmp_DAG[DAG] = DAG_NULL;
}

/*--------------------------------------------------------------*/

void
DAG_tmp_reset_unsigned(TDAG DAG)
{
  unsigned i;
  if (!DAG_tmp_unsigned[DAG])
    return;
  DAG_tmp_unsigned[DAG] = 0;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_reset_unsigned(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

void
DAG_tmp_reset_int(TDAG DAG)
{
  unsigned i;
  if (!DAG_tmp_int[DAG])
    return;
  DAG_tmp_int[DAG] = 0;
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_reset_int(DAG_arg(DAG, i));
}

/*--------------------------------------------------------------*/

void
DAG_tmp_reset_stack_DAG(TDAG DAG)
{
  unsigned i;
  if (!DAG_tmp_stack_DAG[DAG])
    return;
  stack_free(DAG_tmp_stack_DAG[DAG]);
  for (i = 0; i < DAG_arity(DAG); i++)
    DAG_tmp_reset_stack_DAG(DAG_arg(DAG, i));
}

/*
  --------------------------------------------------------------
  Initialization-release functions
  --------------------------------------------------------------
*/

void
DAG_tmp_init(void)
{
  DAG_set_hook_resize(DAG_tmp_hook_resize);
}

/*--------------------------------------------------------------*/

void
DAG_tmp_done(void)
{
}

/*--------------------------------------------------------------*/

#ifdef DEBUG
void
DAG_tmp_debug(void)
{
  unsigned i;
  for (i = 0; i < DAG_size; i++)
    if (DAG_tmp_bool[i])
      my_DAG_message("1: %D\n", i);
  for (i = 0; i < DAG_size; i++)
    if (!DAG_tmp_bool[i])
      my_DAG_message("0: %D\n", i);
}
#endif
