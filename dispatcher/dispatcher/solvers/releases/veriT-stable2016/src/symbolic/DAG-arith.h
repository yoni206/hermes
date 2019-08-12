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
   \file DAG-arith.h
   \author Pascal Fontaine

   \brief Module for arith terms and formulas */

#ifndef __DAG_ARITH_H
#define __DAG_ARITH_H

#include <gmp.h>

#include "DAG.h"

/*
  --------------------------------------------------------------
  Specific constructors
  --------------------------------------------------------------
*/

/**
   \brief DAG constructor
   \param value an integer
   \return DAG representing integer value */
extern TDAG      DAG_new_integer(long value);

/**
   \brief DAG constructor
   \param value an integer
   \return DAG representing integer value */
extern TDAG      DAG_new_integer_mpz(mpz_t value);

/**
   \brief DAG constructor
   \param value an integer
   \return DAG representing integer value */
extern TDAG      DAG_new_integer_str(char * value);

/**
   \brief DAG constructor
   \param num an integer interpreted as numerator
   \param den an integer interpreted as denominator
   \return DAG representing rational num/den.
   \remark User is responsible for overflow, if using version with
   hardware data types */
extern TDAG      DAG_new_rational(long num, long den);

/**
   \brief DAG constructor
   \param value a multiprecision rational
   \return DAG representing rational
   \remark if value happens to be an integer, returns an integer */
extern TDAG      DAG_new_rational_mpq(mpq_t value);

/**
   \brief DAG constructor
   \param value textual representation of a numeral \c 0|[1-9][0-9]* \c
   \return DAG representing integer value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_numeral_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a decimal \c (0|[1-9][0-9]*)\.[0-9]+ \c
   \return DAG representing decimal value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_decimal_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a binary \c #b[01]+ \c
   \return Creates (if new) and returns DAG representing binary value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_binary_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of an hexadecimal \c #x[0-9A-Fa-f]+ \c
   \return DAG representing hexadecimal value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_hex_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a floating point \c 0.[0-9]+ | [1-9][0-9]*.[0-9]+ \c
   \return DAG representing floating point value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_decimal_str(char * value);
extern TDAG      DAG_new_float_str(char * value);

/**
   \brief DAG constructor
   \param value textual representation of a rational \c [1-9][0-9]* / [0-9]+[1-9] or [1-9][0-9]* \c
   \return DAG representing rational value
   \remark The given string is checked for conformance */
extern TDAG      DAG_new_rational_str(char * value);

/**
   \brief DAG constructor
   \param value string
   \return DAG representing string value */
extern TDAG      DAG_new_str(char * value);

/*
  --------------------------------------------------------------
  Specific recognizers
  --------------------------------------------------------------
*/

/**
   \brief Tests if DAG is an integer literal */
extern bool      DAG_is_integer(TDAG DAG);

/**
   \brief Tests if DAG is a rational literal */
extern bool      DAG_is_rational(TDAG DAG);

/**
   \brief Tests if DAG is a numeric literal */
extern bool      DAG_is_number(TDAG DAG);

/*
  --------------------------------------------------------------
  Accessors
  --------------------------------------------------------------
*/

/**
   \brief Get mpz out of integer DAG */
extern void      DAG_mpz_set(mpz_t mpz, TDAG DAG);

/**
   \brief Set mpq to the value of number DAG */
extern void      DAG_mpq_set(mpq_t mpq, TDAG DAG);

/**
   \brief return a string representing DAG in smt-lib2 format
   \remark this string has to be freed by the caller */
extern char *    DAG_number_str(TDAG DAG);

#endif /* __DAG_ARITH_H */
