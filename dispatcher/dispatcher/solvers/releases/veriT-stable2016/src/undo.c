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

#include "general.h"

#include "undo.h"

unsigned undo_level = 0;
Tstack_unsigned undo = NULL;

unsigned undo_top_level = 0;
Tstack_unsigned undo_top = NULL;

Tundo_hook undo_hook[UNDO_NB] = { NULL };
unsigned undo_hook_arg_size[UNDO_NB] = { 0 };

/*--------------------------------------------------------------*/

#ifdef DEBUG
void
undo_debug(void)
{
  unsigned i = stack_size(undo) - 1;
  my_message("undo stack begin\n");
  while (i)
    {
      my_message("stack : %u %u\n", stack_get(undo, i), i);
      /* if (stack_get(undo, i) == 3) */
      /*   my_message("  SIG_ADD %d\n", stack_get(undo, i - 1)); */
      /* if (stack_get(undo, i) == 4) */
      /*   my_message("  SIG_DEL %d\n", stack_get(undo, i - 1)); */
      i -= undo_hook_arg_size[stack_get(undo, i)] + 1;
    }
  my_message("undo stack end\n");
  i = stack_size(undo_top) - 1;
  my_message("undo_top stack begin\n");
  while (i)
    {
      my_message("stack : %u %u\n", stack_get(undo_top, i), i);
      i -= undo_hook_arg_size[stack_get(undo_top, i)] + 1;
    }
  my_message("undo_top stack end\n");
}
#endif

/*--------------------------------------------------------------*/

void
undo_set_hook(Tundo_type type, Tundo_hook f, unsigned size)
{
  assert(type < UNDO_NB);
  assert(!undo_hook[type]);
  undo_hook[type] = f;
  undo_hook_arg_size[type] = (size + (((unsigned) sizeof(unsigned)) - 1u)) /
    ((unsigned) sizeof(unsigned));
}

/*--------------------------------------------------------------*/

void
undo_unset_hook(Tundo_type type)
{
  assert(type < UNDO_NB);
  assert(undo_hook[type]);
  undo_hook[type] = NULL;
}

/*--------------------------------------------------------------*/


void
undo_init(void)
{
  stack_INIT(undo);
  stack_INIT(undo_top);
}

/*--------------------------------------------------------------*/

void
undo_done(void)
{
  assert(!undo_level);
  assert(!stack_size(undo));
  stack_free(undo);
  assert(!undo_top_level);
  assert(!stack_size(undo_top));
  stack_free(undo_top);
}

/*--------------------------------------------------------------*/
