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
  Module for moving trigger attributes at the root of 
  quantified formulas
  --------------------------------------------------------------
*/

#ifndef FIX_TRIGGER_H
#define FIX_TRIGGER_H

#include "DAG.h"

/**
   \author David Deharbe and Pascal Fontaine
   \brief For each quantification occurring in Psrc[i], puts
   quantification patterns in the property list of the DAG for the
   quantification, some benchmarks have it in the DAG of the
   quantified term.  Result is stored in the input 
   \param n the number of terms
   \param Psrc the array of terms to fix
   \remarks Destructive for DAGs and destructive for prop-list of
   quantified DAGs.
   \remarks DAG-linear 
   \remarks Fix discrepancy between AUFLIA benchmarks in SMT-LIB 1.2
   and SMT-LIB 2.0
   \pre none
   \post all triggers are on the quantifier application, not on the body */
void      fix_trigger_array(unsigned n, TDAG * Psrc);

#endif
