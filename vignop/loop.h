#ifndef _LOOP_H_INCLUDED_
#define _LOOP_H_INCLUDED_
#include "libvig/verified/double-chain.h"
#include "libvig/verified/map.h"
#include "libvig/verified/vector.h"
#include "libvig/verified/cht.h"
#include "libvig/verified/lpm-dir-24-8.h"
#include "libvig/proof/coherence.h"
#include "libvig/verified/vigor-time.h"
/*@
@*/
/*@
@*/
/*@ predicate evproc_loop_invariant(unsigned int lcore_id,
                                    vigor_time_t time) = 
              lcore_id == 0 &*&
              last_time(time);
@*/
void loop_invariant_consume(unsigned int lcore_id,
                            vigor_time_t time);
/*@ requires 
             evproc_loop_invariant(lcore_id, time); @*/
/*@ ensures true; @*/
void loop_invariant_produce(unsigned int* lcore_id,
                            vigor_time_t* time);
/*@ requires *lcore_id |-> _ &*& *time |-> _;@*/
/*@ ensures *lcore_id |-> ?lcid &*& *time |-> ?t &*&
             evproc_loop_invariant(lcid, t); @*/

void loop_iteration_border(unsigned int lcore_id,
                           vigor_time_t time);

#endif//_LOOP_H_INCLUDED_
