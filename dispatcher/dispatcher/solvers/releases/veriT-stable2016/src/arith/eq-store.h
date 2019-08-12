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

#ifndef EQ_STORE_H
#define EQ_STORE_H

#include "simplex.h"
#include "DAG.h"

/**
   \brief adds an association between two DAGs and a variable
   \pre DAG0 < DAG1
   \remark we assume that var = DAG0 - DAG1 */
void        eq_store(TDAG DAG0, TDAG DAG1, Tsimplex_var var);

/**
   \brief retrieves var associated with two DAGs
   \return the variable associated with the two DAGs, 0 if none
   \pre DAG0 < DAG1
   \remark we assume that var = DAG0 - DAG1 */
Tsimplex_var eq_get_from_DAG(TDAG DAG0, TDAG DAG1);

/**
   \brief retrieves DAGs associated with vars
   \remark fails if none
   \post DAG0 < DAG1
   \remark we assume that var = DAG0 - DAG1 */
void        eq_get_from_var(Tsimplex_var var, TDAG *PDAG0, TDAG *PDAG1);

/**
   \brief removes an association */
void        eq_remove(Tsimplex_var var);

/**
   \brief records that a lemma has been generated for DAG0!=DAG1
   \pre DAG0 < DAG1 */
void        eq_set_lemma_generated(TDAG DAG0, TDAG DAG1);

/**
   \brief query if a lemma has been generated for DAG0!=DAG1
   \pre DAG0 < DAG1 */
bool        eq_get_lemma_generated(TDAG DAG0, TDAG DAG1);

/**
   \brief tests if a variable corresponds to an equality */
bool        eq_test(Tsimplex_var var);

void        eq_init(void);
void        eq_done(void);

/**
   \brief resets all stored variables
   \remark keeps information about lemmas
   \remark use when simplex is restart */
void        eq_reset_var(void);

#endif /* EQ_STORE_H */
