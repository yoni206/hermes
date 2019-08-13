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
   \file ujobs.h
   \author Haniel Barbosa
   \brief Module for handling unification jobs

   A unification job is a triple <D0, pol, D1> in which D0, D1 are DAGs and pol
   is a boolean.  At least D0 is nonground. There are two kinds of unification
   jobs, determined by the polarity:
   - if pol = true, find unifiers u such that D0u = D1u
   - if pol = false, find unifiers u such that D0u != D1u

   All found unifiers, if any, are associated with <D0, pol, D1>, therefore
   avoiding the recomputation of these unifiers whenever the same job occurs
   again.

   Such jobs are indexed primarily by D0, then by pol and finally by D1. */
#ifndef __UJOBS_H
#define __UJOBS_H

#include "unify.h"

/*
  --------------------------------------------------------------
  Initialization / Release
  --------------------------------------------------------------
*/

/**
   \author Hanel Barbosa
   \brief initializes module */
extern void ujobs_init(void);

/**
   \author Hanel Barbosa
   \brief releases module */
extern void ujobs_done(void);

/* PF2HB: What is an instantiation cycle ? */
/**
   \author Hanel Barbosa
   \brief releases context dependent information at the end of each
   instantiation cycle */
extern void ujobs_done_cycle(void);

/*
  --------------------------------------------------------------
  Handling ujobs
  --------------------------------------------------------------
*/

/**
   \author Hanel Barbosa
   \brief adds result of ujob to index
   \param NGDAG a nonground DAG part of ujob
   \param UDAG a DAG part of ujob
   \param pol polarity of ujob
   \param result resulting unifiers of ujob */
extern void set_ujob(TDAG NGDAG, TDAG UDAG, bool pol, Tstack_Tunifier result);

/**
   \author Hanel Barbosa
   \brief retrieves result of ujob from index
   \param result set accumulating resulting unifiers
   \param NGDAG a non-ground DAG part of ujob
   \param UDAG a DAG part of ujob
   \param pol polarity of ujob
   \param new_vars variables in the context of ujob
   \return true if ujob has already been computed, false otherwise
   \remark the result of a ujob is stored with unifiers based on the variables
   of that context. The same ujob may appear in a different context, however, so
   although the same DAGs compose the job the resulting unifiers must be reset
   to the current variables.

   E.g. in the context of a clause with free variables {x1, x2} the ujob <fx1,
   T, ft> will be indexed with the resulting unifier {x1/t, x2/x2}. If this same
   ujob appear in a context with free variables {x1, x3} the retrieved unifier
   will be {x1/t, x3/x3} */
extern bool retrieve_ujob(Tstack_Tunifier * result, TDAG NGDAG, TDAG UDAG,
                          bool pol, Tstack_DAG new_vars);

#endif
