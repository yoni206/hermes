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
  Simplex variable
  --------------------------------------------------------------
*/

#ifndef SIMPLEX_H
#define SIMPLEX_H

#include "stack.h"

#include "veriT-status.h"

/**
   \author Pascal Fontaine
   \typedef Tsimplex_var
   \brief Linear Arithmetic variable
   \remark variables are unsigned
   \remark variable 0 is used for the independant term, i.e. v_0 = 1 */
typedef unsigned Tsimplex_var;

TSstack(_simplex_var, Tsimplex_var);

extern Tstatus simplex_status;

/*
  --------------------------------------------------------------
  Access to integer variables: each integer variable has a 
  unique index (starting from 0 upwards).

  To implement branch-and-bound, we need to iterate through 
  all integer variables, and access to the current assignment
  (that may not be an integer value).
  --------------------------------------------------------------
*/  

/**
   \author David Deharbe
   \brief Number of integer variables in simplex
   \remark 
*/
extern unsigned
simplex_integer_var_begin(void);

/**
   \author David Deharbe
   \brief Number of integer variables in simplex
   \remark 
*/
extern unsigned
simplex_integer_var_end(void);

/**
   \author David Deharbe
   \brief Number of integer variables in simplex
   \remark 
*/
extern Tsimplex_var
simplex_integer_var_get(unsigned);

/**
   \author David Deharbe
   \var integer_stack
   \brief array with integer-valued variables
*/
extern Tstack_simplex_var integer_stack;

#endif
