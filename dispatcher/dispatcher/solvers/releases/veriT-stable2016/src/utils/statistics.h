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
  Generic module for handling statistics
  --------------------------------------------------------------
*/

#ifndef __STATISTICS_H
#define __STATISTICS_H

#include <stdio.h>

#define STATS_TIMER_SELF 1
#define STATS_TIMER_CHILDREN 2
#define STATS_TIMER_ALL 3

void      stats_init(void);
void      stats_done(void);

/*--------------------------------------------------------------*/

/**
   \author David Déharbe, Pascal Fontaine
   \brief creates a new counter (integer) stat, with name and description
   \param name the name of the statistic
   \param desc a description
   \param form a format string
   \return the id of the stat */
unsigned  stats_counter_new(char *name, char *desc, char *form);

/**
   \author David Déharbe, Pascal Fontaine
   \brief sets the value of counter
   \param stat_id id of statistic
   \param value the value to set */
void      stats_counter_set(unsigned stat_id, int value);

/**
   \author David Déharbe, Pascal Fontaine
   \brief gets the value of counter
   \param stat_id id of statistic
   \return the value of the counter */
int       stats_counter_get(unsigned stat_id);

/**
   \author David Déharbe, Pascal Fontaine
   \brief adds a value to counter
   \param stat_id id of statistic
   \param value the value to add */
void      stats_counter_add(unsigned stat_id, int value);

/**
   \author David Déharbe, Pascal Fontaine
   \brief decrement counter
   \param stat_id id of statistic */
void      stats_counter_inc(unsigned stat_id);

/**
   \author David Déharbe, Pascal Fontaine
   \brief decrement counter
   \param stat_id id of statistic */
void      stats_counter_dec(unsigned stat_id);

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief increment counter associated to desc
   \param name the name of the statistic
   \param desc textual description.  Be careful of conflicts
   \param form a format string
   \remark automatically create counter at first call */
void      stats_easy_inc(char *name, char *desc, char *form);

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief set statistic associated to desc
   \param name the name of the statistic
   \param desc textual description.  Be careful of conflicts
   \param form a format string
   \param v the value
   \remark automatically create counter at first call */
void      stats_easy_set(char *name, char *desc, char *form, int v);

/*--------------------------------------------------------------*/

/**
   \author Pascal Fontaine
   \brief set statistic associated to desc to max
   \param name the name of the statistic
   \param desc textual description.  Be careful of conflicts
   \param form a format string
   \param v the value
   \remark automatically create counter at first call */
void      stats_easy_max(char *name, char *desc, char *form, int v);

/*--------------------------------------------------------------*/

/**
   \author David Déharbe, Pascal Fontaine
   \brief creates a new timer stat, with name and description
   \param name the name of the statistic
   \param desc a description
   \param form a format string
   \param which flags to select process and children to take time into
   account
   \return the id of the timer */
unsigned  stats_timer_new(char *name, char *desc, char *form, int which);

/**
   \author David Déharbe, Pascal Fontaine
   \brief starts timer
   \param stat_timer_id id of timer */
void      stats_timer_start(unsigned stat_timer_id);

/**
   \author David Déharbe, Pascal Fontaine
   \brief stop timer
   \param stat_timer_id id of timer */
void      stats_timer_stop(unsigned stat_timer_id);

/**
   \author David Déharbe, Pascal Fontaine
   \brief get timer (in seconds)
   \param stat_timer_id id of timer */
double    stats_timer_get(unsigned stat_timer_id);

/*--------------------------------------------------------------*/

/**
   \author David Déharbe, Pascal Fontaine
   \brief sets an integer statistic, with name and description
   \param name the name of the statistic
   \param desc a description
   \param form a format string
   \param value the value to set
   \remark sort of contraction of stats_counter_new and stats_counter_set */
void      stats_int(char *name, char *desc, char *form, int value);

/**
   \author David Déharbe, Pascal Fontaine
   \brief sets an unsigned integer statistic, with name and description
   \param name the name of the statistic
   \param desc a description
   \param form a format string
   \param value the value to set
   \remark like stats_int but for unsigned */
void      stats_unsigned(char *name, char *desc, char *form, unsigned value);

/**
   \author Hanile Barbosa
   \brief sets a float statistic, with name and description
   \param name the name of the statistic
   \param desc a description
   \param form a format string
   \param value the value to set
   \remark like stats_int but for float */
void      stats_float(char *name, char *desc, char *form, float value);

/*--------------------------------------------------------------*/

/**
   \author David Déharbe, Pascal Fontaine
   \brief prints statistics to file
   \param file */
void      stats_fprint(FILE * file);

/**
   \author Haniel Barbosa
   \brief prints list of statistics to file
   \param file
   \param list */
void
stats_fprint_list(FILE * file, char ** list);

/**
   \author David Déharbe, Pascal Fontaine
   \brief prints formats of statistics to file
   \param file */
void      stats_fprint_formats(FILE * file);

/**
   \author David Déharbe, Pascal Fontaine
   \brief prints short-form statistics to file
   \param file */
void      stats_fprint_short(FILE * file);

#endif /* __STATISTICS */
