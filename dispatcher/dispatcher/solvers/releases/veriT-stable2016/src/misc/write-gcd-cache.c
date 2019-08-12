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

/**
 \file write-gcd-cache.c
 
 \note This file contains a program that prints a table filled with
 the GCDs of small positive numbers.
 
 The produced table is C code and the output can be redirected to
 C-source files. To this, and assuming the program is called wcc:
 
 wcc 2> gcd-cache.h 1> gcd-cache.c
 
 i.e. the output on stdout is a definition of the table, and the
 output on stderr is a declaration formatted as a C header file
 suitable for inclusion elsewhere.
 
 The cache is a square matrix of unsigned char values and can be
 looked up to speed up calculation of GCD in a general purpose
 routine. The size of the matrix is 256 (UCHAR_MAX), and the values 
 in the table are unsigned char.
 There is a total of 256^2 = 65536 entries, which is roughly the size
 of the object file in bytes.
 
 \author David Deharbe
 */
#include <assert.h>
#include <limits.h>
#include <stdio.h>

/** \brief GCD_CACHE_SZ defines the number of lines/columns of the cache */
#define GCD_CACHE_SZ UCHAR_MAX

int main (void)
{
  unsigned char gcd[GCD_CACHE_SZ][GCD_CACHE_SZ];
  int i, j;
  assert(GCD_CACHE_SZ <= UCHAR_MAX);
  /* fill the table line by line */
  for (i = 0; i < GCD_CACHE_SZ; ++i)
    gcd[0][i] = i;
  for (i = 1; i < GCD_CACHE_SZ; ++i) {
    for (j = 0; j < i; ++j)
      gcd[i][j] = gcd[j][i];
    gcd[i][i] = i;
    for (j = i+1; j < GCD_CACHE_SZ; ++j)
      gcd[i][j] = gcd[i][j-i];
  }
  fputs("/* File produced automatically - do note edit (see write-gcd-cache.c instead) */\n"
	"#ifndef GCD_CACHE_H__\n"
	"#define GCD_CACHE_H__\n"
	"extern unsigned char GCD_CACHE[][];\n"
	"#endif\n", stderr);
  fprintf(stdout, "#define GCD_CACHE_SZ %u\n", GCD_CACHE_SZ);
  fprintf(stdout, "unsigned char GCD_CACHE [GCD_CACHE_SZ][GCD_CACHE_SZ] = {");
  for (i = 0; i < GCD_CACHE_SZ; ++i) {
    for (j = 0; j < GCD_CACHE_SZ; ++j) {
      fprintf(stdout, "%c%3hhu", j == 0 ? '{' : ',', gcd[i][j]);
    }
    if (i < GCD_CACHE_SZ - 1)
      fputs("},\n", stdout);
    else
      fputs("}\n", stdout);
  }
  fputs("};\n", stdout);
  return 0;
}
