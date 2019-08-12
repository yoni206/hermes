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
  Module for hints, i.e., theory propagation

  Maintains information used to build conflict clauses 
  including hints.

  Some hints have no such information, and have to be
  notified directly with SAT_lit.

  Other hints are notified with the routines of this module
  (hint_CC and hint_LA).

  IMPROVE: The software architecture for handling hints is not
  satisfactory. It is an adaptation of a version where only
  CC produced hints to include hints from linear arithmetics.
  --------------------------------------------------------------
*/

#ifndef __HINT_H
#define __HINT_H
#include "DAG.h"
#include "literal.h"

/** \brief initializes module, must be called first */
void hint_init(void);
/** \brief frees used resources, must be called last */
void hint_done(void);

/** \brief propagates hint and stores DAG as explanation */
void hint_CC(Tlit lit, TDAG DAG, bool reversed);
/** \brief gets DAG associated with lit by CC */
TDAG hint_CC_cause(Tlit lit);
/** \brief helper bit for CC */
bool hint_CC_reversed(Tlit lit);

/** \brief propagates hint and stores literal as explanation */
void hint_LA(Tlit lit, Tlit cause);
/** \brief gets lit associated with lit by LA */
Tlit hint_LA_cause(Tlit lit);

/** \brief stores in veriT_conflict all literals implying lit
    \param lit the literal set as hint by the decision procedure
    \remark calls CC_hint_explain or LA_hint_explain */
void hint_explain_dispatch(Tlit lit);

#endif
