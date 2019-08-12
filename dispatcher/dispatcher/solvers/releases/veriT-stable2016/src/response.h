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

#ifndef RESPONSE_H
#define RESPONSE_H

/**
  \file response.h
  \author Pascal Fontaine

  \brief Function implementing the output of veriT
*/

#include <stdarg.h>
#include <stdio.h>

/*
  --------------------------------------------------------------
  response helpers
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_out_file
   \param format printf-like format
*/
void veriT_out(char *format, ...);

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_out_file
   \param format printf-like format
*/
void veriT_out_no_newline(char *format, ...);

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_err_file
   \param format printf-like format
*/
void veriT_err(char *format, ...);

/**
   \author Pascal Fontaine
   \brief outputs anything on the output chosen by veriT_set_err_file and exit
   \param format printf-like format
*/
void veriT_error(char *format, ...);

/**
   \author Pascal Fontaine
   \brief set a file for the error flow
   \param str path to the file
*/
void veriT_set_err_file(char * str);

/**
   \author Pascal Fontaine
   \brief set a file for the error flow
   \param str path to the file
*/
void veriT_set_out_file(char * str);

/**
   \author Pascal Fontaine
   \brief module initialisation
*/
void response_init(void);

/**
   \author Pascal Fontaine
   \brief module disposal
*/
void response_done(void);

/**
   \author David Deharbe
   \brief output communication channel for normal output
*/
extern FILE * veriT_out_file;

/**
   \author David Deharbe
   \brief output communication channel for diagnostic output
*/
extern FILE * veriT_err_file;

#endif
