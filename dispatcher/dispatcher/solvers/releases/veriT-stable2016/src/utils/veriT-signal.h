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
  \file veriT-signal.h

  \author David Deharbe

  \brief API for signal handling functionality.

  \note This module provides an API to centralize the signal handling
  necessities from different components. Once initialized, through
  call to veriT_signal_init, client modules may register a signal
  handler procedure and an address. The signal handler procedure
  sig_handler shall have one argument P, a pointer.

  When the program is signaled, all registered signal handling
  procedures are called with the signal and the corresponding address
  as argument.
  
  Routine veriT_signal_done shall be called to free the resources
  allocated by the module. After it has been called, the program will
  no longer react to signals with the registered signal handlers.
*/

#ifndef __VERIT_SIGNAL_H
#define __VERIT_SIGNAL_H

#include <signal.h>

/**
   \brief Type for signal handling functions. It is a routine that
   takes as argument the signal caught and an address.
*/

typedef void (* Tsigfun) (void); 

/**
   \brief Module initialization.
   \note Must be called before veriT_signal_register.
*/
extern void veriT_signal_init(void);
extern void veriT_signal_done(void);

extern void veriT_signal_register(Tsigfun sigfun);
#endif /* __VERIT_SIGNAL_H */
