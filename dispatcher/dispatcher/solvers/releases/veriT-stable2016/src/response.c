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

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#include "response.h"

/*
  --------------------------------------------------------------
  response helpers
  --------------------------------------------------------------
*/

FILE * veriT_out_file;
FILE * veriT_err_file;

void
veriT_out(char *format, ...)
{
  va_list params;
  va_start(params, format);
  vfprintf(veriT_out_file, format, params);
  va_end(params);
  fprintf(veriT_out_file, "\n");
}

/*--------------------------------------------------------------*/

void
veriT_out_no_newline(char *format, ...)
{
  va_list params;
  va_start(params, format);
  vfprintf(veriT_out_file, format, params);
  va_end(params);
}

/*--------------------------------------------------------------*/

void
veriT_err(char *format, ...)
{
  va_list params;
  fprintf(veriT_err_file, "error \"");
  va_start(params, format);
  vfprintf(veriT_err_file, format, params);
  va_end(params);
  fprintf(veriT_err_file, "\"\n");
}

/*--------------------------------------------------------------*/

void
veriT_error(char *format, ...)
{
#ifdef NLA
  NLA_done();  /* TODO FIX THIS IS DIRTY */
#endif
  va_list params;
  fprintf(veriT_err_file, "(error \"");
  va_start(params, format);
  vfprintf(veriT_err_file, format, params);
  va_end(params);
  fprintf(veriT_err_file, "\")\n");
  exit(-1);
}

/*--------------------------------------------------------------*/

void
veriT_set_err_file(char * str)
{
  if (veriT_err_file != stderr && veriT_err_file != stdout)
    fclose(veriT_err_file);
  if (!strcmp(str, "stderr") || !strcmp(str, ""))
    veriT_err_file = stderr;
  else if (!strcmp(str, "stdout"))
    veriT_err_file = stdout;
  else
    veriT_err_file = fopen(str, "a");
}

/*--------------------------------------------------------------*/

void
veriT_set_out_file(char * str)
{
  if (veriT_out_file != stderr && veriT_out_file != stdout)
    fclose(veriT_out_file);
  if (!strcmp(str, "stderr"))
    veriT_out_file = stderr;
  else if (!strcmp(str, "stdout") || !strcmp(str, ""))
    veriT_out_file = stdout;
  else
    veriT_out_file = fopen(str, "a");
}

/*--------------------------------------------------------------*/

void
response_init(void)
{
  veriT_out_file = stdout;
  veriT_err_file = stderr;
}

/*--------------------------------------------------------------*/

void
response_done(void)
{
  veriT_set_out_file("stdout");
  veriT_set_err_file("stderr");
}
