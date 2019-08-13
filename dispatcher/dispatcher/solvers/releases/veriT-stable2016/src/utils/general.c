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
  Glibc-like general functions
  --------------------------------------------------------------
*/

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "general.h"

/*--------------------------------------------------------------*/

void
breakpoint(void)
{
  static unsigned n = 0;
  fprintf(stderr, "breakpoint %d\n", n++);
}

/*--------------------------------------------------------------*/

void
my_error(char *format, ...)
{
#ifdef NLA
  NLA_done();  /* TODO FIX!!!! */
#endif
  va_list params;
  va_start(params, format);
  fprintf(stderr, "error : ");
  vfprintf(stderr, format, params);
  va_end(params);
  exit(1);
}

/*--------------------------------------------------------------*/

void
my_warning(char *format, ...)
{
  va_list params;
  va_start(params, format);
  fprintf(stderr, "warning : ");
  vfprintf(stderr, format, params);
  va_end(params);
}

/*--------------------------------------------------------------*/

int SILENT = 0;

void
my_message(char *format, ...)
{
  va_list params;
  if (SILENT)
    return;
  va_start (params, format);
  fprintf (stderr, "MSG : ");
  vfprintf (stderr, format, params);
  va_end (params);
}

/*--------------------------------------------------------------*/

void
my_message_return(void)
{
  if (SILENT)
    return;
  fprintf(stderr, "\n");
}

/*--------------------------------------------------------------*/

char *
strmake(const char* const astr)
{
  char *ptr;
  if (astr == NULL)
    return NULL;
  MY_MALLOC(ptr, strlen(astr) + 1);
  strcpy(ptr, astr);
  return ptr;
}

/*--------------------------------------------------------------*/

char *
strapp(char *dest, size_t *destlen, const char *src)
{
  size_t srclen;
  if (!src)
    return dest;
  srclen = strlen(src);
  MY_REALLOC(dest, *destlen + srclen + 1);
  strcpy(dest + *destlen, src);
  *destlen += srclen;
  return dest;
}

/*--------------------------------------------------------------*/

char *
strmake_printf(char *format, ...)
{
  char str[255];
  va_list params;
  va_start(params, format);
  /*  vsnprintf (str, 255, format, params); */
  vsprintf(str, format, params);
  va_end(params);
  return strmake(str);
}

/*--------------------------------------------------------------*/

unsigned
ul_str_size(unsigned long val)
{
  unsigned result;
  result = 1;
  while (val > 9)
    {
      val /= 10;
      result++;
    }
  return result;
}

/*--------------------------------------------------------------*/

unsigned
l_str_size(long val)
{
  unsigned result;
  result = 1;
  while (val > 9)
    {
      val /= 10;
      result++;
    }
  return result;
}

/*--------------------------------------------------------------*/

int
str_nb_words(char *str)
{
  int result = 0;
  while (*str == ' ') str++;
  while (*str != 0)
    {
      result++;
      while (*str != ' ' && *str != 0) str++;
      while (*str == ' ') str++;
    }
  return result;
}

/*--------------------------------------------------------------*/

char**
str_split(char* a_str, const char a_delim)
{
    char** result    = 0;
    size_t count     = 0;
    char* tmp        = a_str;
    char* last_comma = 0;
    char delim[2];
    delim[0] = a_delim;
    delim[1] = 0;

    /* Count how many elements will be extracted. */
    while (*tmp)
      {
        if (a_delim == *tmp)
	  {
            count++;
            last_comma = tmp;
	  }
        tmp++;
      }

    /* Add space for trailing token. */
    count += last_comma < (a_str + strlen(a_str) - 1);

    /* Add space for terminating null string so caller
       knows where the list of returned strings ends. */
    count++;

    result = malloc(sizeof(char*) * count);

    if (result)
      {
        size_t idx  = 0;
        char* token = strtok(a_str, delim);

        while (token)
	  {
            assert(idx < count);
            *(result + idx++) = strdup(token);
            token = strtok(0, delim);
	  }
        assert(idx == count - 1);
        *(result + idx) = 0;
      }

    return result;
}

/*--------------------------------------------------------------*/
