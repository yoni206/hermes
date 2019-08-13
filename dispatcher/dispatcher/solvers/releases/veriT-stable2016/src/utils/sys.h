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
  \file sys.h
  \author David Deharbe

  \brief Provides functions to access some system resources.
*/

#ifndef __SYS_H
#define __SYS_H

#include <stdio.h>

/**
   \brief exit status codes */
typedef enum Tsys_exit_code
  {
    SYS_EXIT_VALID = 0,
    SYS_EXIT_COUNTERSATISFIABLE,
    SYS_EXIT_DONT_KNOW,
    SYS_EXIT_CONFLICTING_AXIOMS,
    SYS_EXIT_TIMEOUT,
    SYS_EXIT_RESOURCES_EXHAUSTED,
    SYS_EXIT_ERROR_USAGE,
    SYS_EXIT_ERROR_IO,
    SYS_EXIT_ERROR_UNKNOWN
  } Tsys_exit_code;

/**
   \brief Creates a new directory in the current directory
   \remark assumes this is possible
   \author David Deharbe */
extern char * sys_create_directory(void);

/**
   \brief opens a file
   \param name the file name
   \param mode access mode (as defined in C)
   \return a pointer to this file
   \author David Deharbe */
extern FILE * sys_open_file(const char * name, const char * mode);

/**
   \brief Closes a file
   \param file the file to close
   \author David Deharbe */
extern void   sys_close_file(FILE * file);

#endif /* __SYS_H */
