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
   Module for representing arithmetic formulas and terms
*/

#include <gmp.h>

#include "DAG-arith.h"

#include "DAG-symb.h"

/*--------------------------------------------------------------*/

TDAG
DAG_new_integer(long value)
{
  return DAG_new_nullary(DAG_symb_integer(value));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_integer_mpz(mpz_t mpz)
{
  return DAG_new_nullary(DAG_symb_integer_mpz(mpz));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_integer_str(char * value)
{
  return DAG_new_nullary(DAG_symb_integer_str(value));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_binary_str(char * value)
{
  return DAG_new_nullary(DAG_symb_binary_str(value));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_hex_str (char * value)
{
  return DAG_new_nullary(DAG_symb_hex_str(value));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_rational_mpq(mpq_t mpq)
{
  return DAG_new_nullary(DAG_symb_rational_mpq(mpq));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_rational_str(char * value)
{
  return DAG_new_nullary(DAG_symb_rational_str(value));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_decimal_str(char * value)
{
  return DAG_new_nullary(DAG_symb_decimal_str(value));
}

/*--------------------------------------------------------------*/

TDAG
DAG_new_str(char * value)
{
  return DAG_new_nullary(DAG_symb_str(value));
}

/*--------------------------------------------------------------*/

bool
DAG_is_rational(TDAG DAG)
{
  return DAG_symb_type(DAG_symb(DAG)) & SYMB_NUMBER;
}

/*--------------------------------------------------------------*/

bool
DAG_is_integer(TDAG DAG)
{
  return DAG_symb_type(DAG_symb(DAG)) & SYMB_INTEGER;
}

/*--------------------------------------------------------------*/

bool
DAG_is_number(TDAG DAG)
{
  return DAG_is_integer(DAG) || DAG_is_rational(DAG);
}

/*--------------------------------------------------------------*/

void
DAG_mpz_set(mpz_t mpz, TDAG DAG)
{
  assert(DAG_is_integer(DAG));
  mpz_set(mpz, DAG_symb_mpz(DAG_symb(DAG)));
}

/*--------------------------------------------------------------*/

void
DAG_mpq_set(mpq_t mpq, TDAG DAG)
{
  if (DAG_is_integer(DAG))
    {
      mpq_set_z(mpq, DAG_symb_mpz(DAG_symb(DAG)));
      return;
    }
  assert(DAG_is_rational(DAG));
  mpq_set(mpq, DAG_symb_mpq(DAG_symb(DAG)));
}

/*--------------------------------------------------------------*/

char *
DAG_number_str(TDAG DAG)
{
  char * str = NULL, * tmp;
  size_t str_len = 0;
  bool neg;
  if (DAG_is_integer(DAG))
    {
      neg = (mpz_sgn(DAG_symb_mpz(DAG_symb(DAG))) < 0);
      if (neg)
        str = strapp(str, &str_len, "(- ");
      tmp = mpz_get_str(NULL, 10, DAG_symb_mpz(DAG_symb(DAG)));
      str = strapp(str, &str_len, tmp + (neg?1:0));
      free(tmp);
      if (neg)
        str = strapp(str, &str_len, ")");
      return str;
    }
  assert(DAG_is_rational(DAG));
  neg = (mpz_sgn(mpq_numref(DAG_symb_mpq(DAG_symb(DAG)))) < 0);
  if (neg)
    str = strapp(str, &str_len, "(- ");
  str = strapp(str, &str_len, "(/ ");
  tmp = mpz_get_str(NULL, 10, mpq_numref(DAG_symb_mpq(DAG_symb(DAG))));
  str = strapp(str, &str_len, tmp + (neg?1:0));
  free(tmp);
  str = strapp(str, &str_len, " ");
  tmp = mpz_get_str(NULL, 10, mpq_denref(DAG_symb_mpq(DAG_symb(DAG))));
  str = strapp(str, &str_len, tmp);
  free(tmp);
  str = strapp(str, &str_len, neg?"))":")");
  return str;
}
