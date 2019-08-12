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

#ifndef __GENERAL_H
#define __GENERAL_H

#ifdef DEBUG
#define SAFE_MALLOC
#endif

#include <stdlib.h>
#ifdef SAFE_MALLOC
#include <string.h>
#endif

/* PF use MY_MALLOC and MY_REALLOC with caution
   In particular, make sure it is not cut (if ( ) then MY_MALLOC; */

#ifdef DMEM
#define MY_MALLOC(v,s)                                                  \
  {                                                                     \
    v = malloc(s);                                                      \
    if (s && !v)                                                        \
      my_error ("malloc error on line %d in file " __FILE__ "\n", __LINE__); \
    memset(v,0xFF,s);                                                   \
  }
#define MY_REALLOC_DMEM(v,s,os)                                         \
  {                                                                     \
    void * P;                                                           \
    P = malloc(s);                                                      \
    memset(P, 0xFF, s);                                                 \
    memcpy(P, v, os);                                                   \
    free(v);                                                            \
    v = P;                                                              \
    if (s && !v)                                                        \
      my_error ("realloc error on line %d in file " __FILE__ "\n", __LINE__); \
  }
#else
#define MY_MALLOC(v,s)                                                  \
  {                                                                     \
    v = malloc(s);                                                      \
    if (s && !v)                                                        \
      my_error ("malloc error on line %d in file " __FILE__ "\n", __LINE__); \
  }
#endif
#define MY_REALLOC(v,s)                                                 \
  {                                                                     \
    v = realloc(v,s);                                                   \
    if (s && !v)                                                        \
      my_error ("realloc error on line %d in file " __FILE__ "\n", __LINE__); \
  }

#undef assert
#ifdef DEBUG
#define assert(expr) {if (expr) ; else my_error("Assert "__STRING(expr)" failed (" __FILE__":%d)\n", __LINE__); }
#else
#define assert(A) {};
#endif

#define MAC_BREAK_MALLOC_DEBUG (msg)                \
  { char c; printf("%s\n", msg); scanf("%c", &c); }

/* PF do-nothing function for breakpoints in debugging */
void      breakpoint(void);

/* PF if SILENT set, message functions do nothing */
extern int SILENT;
/* PF error messages functions */
void      my_error(char *format, ...);
void      my_warning(char *format, ...);
void      my_message(char *format, ...);
void      my_message_return(void);

/* PF takes a null terminated string.  Returns a new allocated copy */
char     *strmake(const char* const astr);
/* PF returns a new allocated copy, using sprintf function (255 char at most)*/
char     *strmake_printf(char *format, ...);
/* DD dest is NULL or a null-terminated string, s.t. (strlen(dest) == *destlen)
   appends null-terminated src at the end of dest, updates *destlen */
char     *strapp(char *dest, size_t *destlen, const char *src);

/* DD computes the number of digits to represent an unsigned long */
unsigned  ul_str_size(unsigned long val);
/* DD computes the number of digits to represent an long */
unsigned  l_str_size(long val);
/* DD computes the number of tokens in a space-separated string */
int       str_nb_words(char *str);

/* HB From literature, string split */
char** str_split(char* a_str, const char a_delim);


#define SWAP(V1, V2)                            \
  do                                            \
    {                                           \
      typeof(V1) __tmp = V1;                    \
      V1 = V2;                                  \
      V2 = __tmp;                               \
    }                                           \
  while (0)

#define MIN(v1, v2) ((v1) <= (v2)) ? (v1) : (v2)

#endif /* __GENERAL_H */
