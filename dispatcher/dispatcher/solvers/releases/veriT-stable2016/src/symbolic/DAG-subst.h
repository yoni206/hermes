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

#ifndef DAG_SUBST_H
#define DAG_SUBST_H

#include "DAG.h"

/**
   \author David Deharbe, Pascal Fontaine
   \brief substitutes every node by DAG_tmp_DAG[node] in a term
   \param src the term
   \return true iff the term is modified (false otherwise)
   \attention the user should restore the DAG_tmp (see DAG_tmp.h),
   for instance using DAG_tmp_reset_DAG */
extern bool      DAG_tmp_subst(TDAG src);

/**
   \author David Deharbe, Pascal Fontaine
   \brief conditionally substitutes every node by DAG_tmp_DAG[node] in a term
   \param src the term
   \return true iff the term is modified (false otherwise)
   \remark like the above, but only get inside term if cont(term)
   \attention the user should restore the DAG_tmp (see DAG_tmp.h),
   for instance using DAG_tmp_reset_DAG */
extern bool      DAG_tmp_subst_cond(TDAG src, bool (*cont)(TDAG DAG));

/**
   \brief Simple substitution
   \param src Term where the substitution is realized
   \param origin Term that will be substituted
   \param subst Term that will replace origin
   \sa DAG_subst_multiple */
extern TDAG      DAG_subst(TDAG src, TDAG origin, TDAG subst);

/**
   \brief Multiple substitution
   \param src Term where the substitution is realized
   \param n The number of terms that will be substituted
   \param origin Array of n terms that will be substituted
   \param subst Array of n term that will replace substituted terms */
extern TDAG      DAG_subst_multiple(TDAG src, unsigned n,
				    TDAG * origin, TDAG * subst);

/**
   \brief Tests DAG inclusion
   \param src
   \param find
   \return true if find is a subterm of src, false otherwise */
extern bool      DAG_contain(TDAG src, TDAG find);

#endif
