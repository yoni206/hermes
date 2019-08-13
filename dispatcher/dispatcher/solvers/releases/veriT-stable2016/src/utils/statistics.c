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
  Generic module for handling options
  --------------------------------------------------------------
*/

#include <sys/time.h>
#ifndef WIN32
#include <sys/resource.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "general.h"
#include "statistics.h"
#include "stack.h"

/*
  --------------------------------------------------------------
  timeval help functions
  --------------------------------------------------------------
*/

static void
timeval_init(struct timeval *x)
{
  x->tv_sec = 0;
  x->tv_usec = 0;
}

/*--------------------------------------------------------------*/

static void
timeval_diff(struct timeval *x, struct timeval *y)
{
  x->tv_sec -= y->tv_sec;
  x->tv_usec -= y->tv_usec;

  if (x->tv_usec < 0)
    {
      long int nsec = x->tv_usec / 1000000;
      x->tv_usec -= 1000000 * nsec;
      x->tv_sec += nsec;
    }
}

/*--------------------------------------------------------------*/

static void
timeval_add(struct timeval *x, struct timeval *y)
{
  x->tv_sec += y->tv_sec;
  x->tv_usec += y->tv_usec;

  if (x->tv_usec > 1000000)
    {
      long int nsec = x->tv_usec / 1000000;
      x->tv_usec -= 1000000 * nsec;
      x->tv_sec += nsec;
    }
}

/*
  --------------------------------------------------------------
  time_adder
  --------------------------------------------------------------
*/

struct TStime_adder
{
  int who;
  struct timeval last_time;
  struct timeval total_time;
};
typedef struct TStime_adder *Ttime_adder;

static Ttime_adder
time_adder_new(int who)
{
  Ttime_adder result;
  MY_MALLOC(result, sizeof(struct TStime_adder));
  timeval_init(&result->total_time);
  result->who = who;
  return result;
}

/*--------------------------------------------------------------*/
static void
time_adder_free(Ttime_adder * Ptime_adder)
{
  free(*Ptime_adder);
  *Ptime_adder = NULL;
}

/*--------------------------------------------------------------*/

static void
time_adder_start(Ttime_adder time_adder)
{
#ifndef WIN32
  struct rusage usage;
  if (!time_adder)
    my_error("time_adder_start: NULL pointer\n");
  timeval_init(&time_adder->last_time);
  if (time_adder->who & STATS_TIMER_CHILDREN)
    {
      getrusage(RUSAGE_CHILDREN, &usage);
      timeval_add(&time_adder->last_time, &usage.ru_utime);
      timeval_add(&time_adder->last_time, &usage.ru_stime);
    }
  if (time_adder->who & STATS_TIMER_SELF)
    {
      getrusage(RUSAGE_SELF, &usage);
      timeval_add(&time_adder->last_time, &usage.ru_utime);
      timeval_add(&time_adder->last_time, &usage.ru_stime);
    }
#endif
}

/*--------------------------------------------------------------*/

static void
time_adder_stop(Ttime_adder time_adder)
{
#ifndef WIN32
  struct rusage usage;
  struct timeval actual_time;
  if (!time_adder)
    my_error("time_adder_stop: NULL pointer\n");
  timeval_init(&actual_time);
  if (time_adder->who & STATS_TIMER_CHILDREN)
    {
      getrusage(RUSAGE_CHILDREN, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  if (time_adder->who & STATS_TIMER_SELF)
    {
      getrusage(RUSAGE_SELF, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  timeval_diff(&actual_time, &time_adder->last_time);
  timeval_add(&time_adder->total_time, &actual_time);
#endif
}

/*--------------------------------------------------------------*/

static double
time_adder_get(Ttime_adder time_adder)
{
  double result;
  if (!time_adder)
    my_error("time_adder_get: NULL pointer\n");
  result = (double) time_adder->total_time.tv_sec;
  result += (double) time_adder->total_time.tv_usec / 1000000.0;
  return result;
}


/*--------------------------------------------------------------*/

static double
time_adder_intermediate_get(Ttime_adder time_adder)
{
#ifndef WIN32
  double result;
  struct rusage usage;
  struct timeval actual_time;
  if (!time_adder)
    my_error("time_adder_intermediate_get: NULL pointer\n");
  result = (double) time_adder->total_time.tv_sec;
  result += (double) time_adder->total_time.tv_usec / 1000000.0;
  timeval_init(&actual_time);
  if (time_adder->who & STATS_TIMER_CHILDREN)
    {
      getrusage(RUSAGE_CHILDREN, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  if (time_adder->who & STATS_TIMER_SELF)
    {
      getrusage(RUSAGE_SELF, &usage);
      timeval_add(&actual_time, &usage.ru_utime);
      timeval_add(&actual_time, &usage.ru_stime);
    }
  timeval_diff(&actual_time, &time_adder->last_time);
  result += (double) actual_time.tv_sec;
  result += (double) actual_time.tv_usec / 1000000.0;
  return result;
#else
  return 1.0;           /* fake value for Windows */
#endif
}

/*
  --------------------------------------------------------------
  Statistics
  --------------------------------------------------------------
*/

#define STAT_NONE 0
#define STAT_INT 1
#define STAT_UNSIGNED 1
#define STAT_TIMER 2
#define STAT_FLOAT 3

struct Tstat
{
  char *name, *desc, *form;
  unsigned type;
  union {
    Ttime_adder time_adder;
    int a_int;
    unsigned a_unsigned;
    float a_float;
  } value;
};
typedef struct Tstat Tstat;

TSstack(_stat, Tstat);
Tstack_stat stats;

/*--------------------------------------------------------------*/

unsigned
stats_counter_new(char *name, char *desc, char *form)
{
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_INT;
  stack_top(stats).value.a_int = 0;
  return stack_size(stats) - 1;
}

/*--------------------------------------------------------------*/

void
stats_easy_inc(char *name, char *desc, char *form)
{
  unsigned i;
  /* IMPROVE: use hash table to associate stat_id to name */
  for (i = 0; i < stack_size(stats); i++)
    if (!strcmp(name, stack_get(stats, i).name))
      {
        assert(stack_get(stats, i).type == STAT_INT);
        stack_get(stats, i).value.a_int++;
        return;
      }
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_INT;
  stack_top(stats).value.a_int = 1;
}

/*--------------------------------------------------------------*/

void
stats_easy_set(char *name, char *desc, char *form, int v)
{
  unsigned i;
  /* IMPROVE: use hash table to associate stat_id to name */
  for (i = 0; i < stack_size(stats); i++)
    if (!strcmp(name, stack_get(stats, i).name))
      {
        assert(stack_get(stats, i).type == STAT_INT);
        stack_get(stats, i).value.a_int = v;
        return;
      }
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_INT;
  stack_top(stats).value.a_int = v;
}

/*--------------------------------------------------------------*/

void
stats_easy_max(char *name, char *desc, char *form, int v)
{
  unsigned i;
  /* IMPROVE: use hash table to associate stat_id to name */
  for (i = 0; i < stack_size(stats); i++)
    if (!strcmp(name, stack_get(stats, i).name))
      {
        assert(stack_get(stats, i).type == STAT_INT);
        if (stack_get(stats, i).value.a_int < v)
          stack_get(stats, i).value.a_int = v;
        return;
      }
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_INT;
  stack_top(stats).value.a_int = v;
}

/*--------------------------------------------------------------*/

void
stats_counter_set(unsigned stat_id, int value)
{
  assert(stat_id < stack_size(stats));
  assert(stack_get(stats, stat_id).type == STAT_INT);
  stack_get(stats, stat_id).value.a_int = value;
}

/*--------------------------------------------------------------*/

int
stats_counter_get(unsigned stat_id)
{
  assert(stat_id < stack_size(stats));
  assert(stack_get(stats, stat_id).type == STAT_INT);
  return stack_get(stats, stat_id).value.a_int;
}

/*--------------------------------------------------------------*/

void
stats_counter_add(unsigned stat_id, int value)
{
  assert(stat_id < stack_size(stats));
  assert(stack_get(stats, stat_id).type == STAT_INT);
  stack_get(stats, stat_id).value.a_int += value;
}

/*--------------------------------------------------------------*/

void
stats_counter_inc(unsigned stat_id)
{
  assert(stat_id < stack_size(stats));
  assert(stack_get(stats, stat_id).type == STAT_INT);
  stack_get(stats, stat_id).value.a_int++;
}

/*--------------------------------------------------------------*/

void
stats_counter_dec(unsigned stat_id)
{
  assert(stat_id < stack_size(stats));
  assert(stack_get(stats, stat_id).type == STAT_INT);
  stack_get(stats, stat_id).value.a_int--;
}

/*--------------------------------------------------------------*/

unsigned
stats_timer_new(char *name, char *desc, char *form, int which)
{
  if ((which & STATS_TIMER_SELF) == 0 && (which & STATS_TIMER_CHILDREN) == 0)
    my_error("stats_timer_new: no process specified");
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_TIMER;
  stack_top(stats).value.time_adder = time_adder_new(which);
  return stack_size(stats) - 1;
}

/*--------------------------------------------------------------*/

void
stats_timer_start(unsigned stat_timer_id)
{
  assert(stat_timer_id < stack_size(stats));
  assert(stack_get(stats, stat_timer_id).type == STAT_TIMER);
  time_adder_start(stack_get(stats, stat_timer_id).value.time_adder);
}

/*--------------------------------------------------------------*/

void
stats_timer_stop(unsigned stat_timer_id)
{
  assert(stat_timer_id < stack_size(stats));
  assert(stack_get(stats, stat_timer_id).type == STAT_TIMER);
  time_adder_stop(stack_get(stats, stat_timer_id).value.time_adder);
}

/*--------------------------------------------------------------*/

double
stats_timer_get(unsigned stat_timer_id)
{
  assert(stat_timer_id < stack_size(stats));
  assert(stack_get(stats, stat_timer_id).type == STAT_TIMER);
  return time_adder_intermediate_get(stack_get(stats, stat_timer_id).
                                     value.time_adder);
}

/*--------------------------------------------------------------*/

void
stats_int(char *name, char *desc, char *form, int value)
{
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_INT;
  stack_top(stats).value.a_int = value;
}

/*--------------------------------------------------------------*/

void
stats_unsigned(char *name, char *desc, char *form, unsigned value)
{
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_UNSIGNED;
  stack_top(stats).value.a_unsigned = value;
}

/*--------------------------------------------------------------*/

void
stats_float(char *name, char *desc, char *form, float value)
{
  stack_inc(stats);
  stack_top(stats).name = name;
  stack_top(stats).desc = desc;
  stack_top(stats).form = form;
  stack_top(stats).type = STAT_FLOAT;
  stack_top(stats).value.a_float = value;
}

/*--------------------------------------------------------------*/

void
stats_fprint_formats(FILE * file)
{
  unsigned i;
  /* DD print the glossary */
  for (i = 0; i < stack_size(stats); i++)
    {
      Tstat *Pstat = &stack_get(stats, i);
      if (Pstat->name)
        fprintf(file, "STAT_FORM: %s: %s\n", Pstat->name, Pstat->form);
      else
        fprintf(file, "STAT_FORM: %s%.2u: %s\n",
                (Pstat->type == STAT_TIMER)?"ST":"SC", i + 1, Pstat->form);
    }
}

/*--------------------------------------------------------------*/

void
stats_fprint_short(FILE * file)
{
  unsigned i;
  for (i = 0; i < stack_size(stats); ++i)
    {
      Tstat *Pstat = &stack_get(stats, i);
      if (Pstat->type == STAT_INT)
        {
          if (Pstat->name)
            fprintf(file, "%s=%d\n", Pstat->name, Pstat->value.a_int);
          else
            fprintf(file, "SC%.2u=%d\n", i + 1, Pstat->value.a_int);
        }
      else if (Pstat->type == STAT_UNSIGNED)
        {
          if (Pstat->name)
            fprintf(file, "%s=%d\n", Pstat->name, Pstat->value.a_unsigned);
          else
            fprintf(file, "SC%.2u=%d\n", i + 1, Pstat->value.a_unsigned);
        }
      else
        {
          if (Pstat->name)
            fprintf(file, "%s=%.3f\n", Pstat->name,
                    time_adder_get(Pstat->value.time_adder));
          else
            fprintf(file, "ST%.2u=%.3f\n", i + 1,
                    time_adder_get(Pstat->value.time_adder));
        }
    }
}

/*--------------------------------------------------------------*/

void
stats_fprint_list(FILE * file, char ** list)
{
  unsigned i, j;
  /* DD print value of each counter / timer */
  for (i = 0; i < stack_size(stats); i++)
    {
      Tstat *Pstat = &stack_get(stats, i);
      /* HB Avoid non-listed counters */
      if ((Pstat->type == STAT_INT || Pstat->type == STAT_UNSIGNED ||
           Pstat->type == STAT_FLOAT) && Pstat->name)
        {
          for (j = 0; *(list + j); ++j)
            if (!strcmp(*(list + j), Pstat->name))
              break;
          if (!*(list+j))
            continue;
        }
      if (Pstat->type == STAT_INT)
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%d\n", Pstat->name, Pstat->value.a_int);
          else
            fprintf(file, "STAT: SC%.2u=%d\n", i + 1, Pstat->value.a_int);
        }
      else if (Pstat->type == STAT_UNSIGNED)
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%d\n", Pstat->name, Pstat->value.a_unsigned);
          else
            fprintf(file, "STAT: SC%.2u=%d\n", i + 1, Pstat->value.a_unsigned);
        }
      else if (Pstat->type == STAT_FLOAT)
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%.3f\n", Pstat->name, Pstat->value.a_float);
          else
            fprintf(file, "STAT: SC%.2u=%.3f\n", i + 1, Pstat->value.a_float);
        }
      else
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%.3f\n", Pstat->name,
                    time_adder_get(Pstat->value.time_adder));
          else
            fprintf(file, "STAT: ST%.2u=%.3f\n ", i + 1,
                    time_adder_get(Pstat->value.time_adder));
        }
    }
  for (i = 0; *(list + i); ++i)
    free(*(list + i));
  free(list);
}

/*--------------------------------------------------------------*/

void
stats_fprint(FILE * file)
{
  unsigned i;
  /* DD print the glossary */
  for (i = 0; i < stack_size(stats); i++)
    {
      Tstat *Pstat = &stack_get(stats, i);
      if (Pstat->name)
        fprintf(file, "STAT_DESC: %s: %s\n", Pstat->name, Pstat->desc);
      else
        fprintf(file, "STAT_DESC: %s%.2u: %s\n",
                (Pstat->type == STAT_TIMER)?"ST":"SC", i + 1, Pstat->desc);
    }
  /* DD print value of each counter / timer */
  for (i = 0; i < stack_size(stats); i++)
    {
      Tstat *Pstat = &stack_get(stats, i);
      if (Pstat->type == STAT_INT)
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%d\n", Pstat->name, Pstat->value.a_int);
          else
            fprintf(file, "STAT: SC%.2u=%d\n", i + 1, Pstat->value.a_int);
        }
      else if (Pstat->type == STAT_UNSIGNED)
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%d\n", Pstat->name, Pstat->value.a_unsigned);
          else
            fprintf(file, "STAT: SC%.2u=%d\n", i + 1, Pstat->value.a_unsigned);
        }
      else if (Pstat->type == STAT_FLOAT)
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%.3f\n", Pstat->name, Pstat->value.a_float);
          else
            fprintf(file, "STAT: SC%.2u=%.3f\n", i + 1, Pstat->value.a_float);
        }
      else
        {
          if (Pstat->name)
            fprintf(file, "STAT: %s=%.3f\n", Pstat->name,
                    time_adder_get(Pstat->value.time_adder));
          else
            fprintf(file, "STAT: ST%.2u=%.3f\n ", i + 1,
                    time_adder_get(Pstat->value.time_adder));
        }
    }
}

/*--------------------------------------------------------------*/

void
stats_init(void)
{
  stack_INIT(stats);
}

/*--------------------------------------------------------------*/

void
stats_done(void)
{
  unsigned i;
  for (i = 0; i < stack_size(stats); i++)
    if (stack_get(stats, i).type == STAT_TIMER)
      time_adder_free(&(stack_get(stats, i).value.time_adder));
  stack_free(stats);
}
