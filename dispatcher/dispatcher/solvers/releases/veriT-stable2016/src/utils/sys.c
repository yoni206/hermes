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

#define _BSD_SOURCE /* for mkdtemp */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "general.h"
#include "sys.h"

FILE * 
sys_open_file(const char * name, const char * mode)
{
  FILE * result;
  result = fopen(name, mode);
  if (result == 0)
  {
    my_error("cannot open file \"%s\".\n", name);
    exit(SYS_EXIT_ERROR_IO);
  }
  return result;
}

/*--------------------------------------------------------------*/

void
sys_close_file(FILE * file)
{
  if (fclose(file) == -1)
    {
      my_error("cannot close file.\n");
      exit(SYS_EXIT_ERROR_IO);
    }
}

/*--------------------------------------------------------------*/

char * 
sys_create_directory(void)
{
  /** TEMPLATE is a string that specifies how directory and files 
   * created by veriT shall be named. See mkdtemp (3). */

  static const char TEMPLATE [] = "veriT-XXXXXX";

  char * template;
  MY_MALLOC(template, sizeof(char) * (strlen(TEMPLATE) + 1));
  strcpy(template, TEMPLATE);
#ifndef WIN32
  return mkdtemp(template);
#else
  /* This is insecure, but mkdtemp is not available on Windows. */
  mktemp(template);
  mkdir(template);
  return template;
#endif
}
