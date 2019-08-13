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
  Computing hash keys from datastructures
  --------------------------------------------------------------
*/

#ifndef _HK_H
#define _HK_H

/**
   \author Pascal Fontaine
   \brief finalize hash key computation
   \param k original hash key
   \return the hash key */
#define h_inc_end(k)					\
  (k += (k << 3), k ^= (k >> 11), k += (k << 15), k)

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief incrementally add hash key for unsigned
   \param k original hash key
   \param u unsigned
   \return the hash key
   \remark Use with k = 0 at first, and finalise with h_inc_end function */
#define h_unsigned_inc(k, u)			\
  ((((k) + (u)) << 10) ^ (((k) + (u)) >> 6))

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief incrementally add h key for string
   \param k original h key
   \param str a string
   \return the hash key
   \remark Use with k = 0 at first, and finalise with h_inc_end function */
static __inline__ unsigned
h_string_inc(unsigned k, char * str)
{
  for (; *str; str++)
    {
      k += (unsigned) *str;
      k += (k << 10);
      k ^= (k >> 6);
    }
  return k;
}

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief computes hash key for unsigned
   \param u an unsigned
   \return the hash key */
static __inline__ unsigned
h_unsigned(unsigned u)
{
  unsigned k = h_unsigned_inc(0, u);
  return h_inc_end(k);
}

/**
   \author Pascal Fontaine
   \brief computes h key for string
   \param str a string
   \return the hash key */
static __inline__ unsigned
h_string(char * str)
{
  unsigned k = h_string_inc(0, str);
  return h_inc_end(k);
}

#endif /* _HK_H */
