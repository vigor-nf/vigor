#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "nat_flow.h"
#include "lib/coherence.h"
#include "lib/nf_time.h"

/*@
fixpoint bool nat_int_fp(flow_id ik, int index) {
    return true;
}

fixpoint bool nat_ext_fp(int start_port, flow_id ek, int index) {
    switch(ek) { case flid(sp,dp,sip,dip,prot):
        return dp == start_port + index;
    }
}


predicate evproc_loop_invariant(struct DoubleMap* mp, struct DoubleChain *chp,
                                unsigned int lcore_id,
                                time_t time, int max_flows, int start_port) =
          dmappingp<flow_id,flow_id,flow>(?m, flow_idp, flow_idp, _flow_id_hash, _flow_id_hash,
                                          flowp, flowp_bare, flow_ids_offsets_fp,
                                          sizeof(struct Flow), flow_get_internal_id, flow_get_external_id,
                                          nat_int_fp, (nat_ext_fp)(start_port), mp) &*&
          double_chainp(?ch, chp) &*&
          dmap_dchain_coherent(m, ch) &*&
          lcore_id == 0 &*& //<-- We are verifying for a single core.
          last_time(time) &*&
          dchain_high_fp(ch) <= time &*&
          dmap_cap_fp(m) == max_flows &*&
          max_flows < INT_MAX;
@*/

void loop_iteration_assumptions(struct DoubleMap** m, struct DoubleChain** ch,
                                unsigned int lcore_id,
                                time_t time, int max_flows, int start_port);

void loop_iteration_assertions(struct DoubleMap** m, struct DoubleChain** ch,
                               unsigned int lcore_id,
                               time_t time, int max_flows, int start_port);

void loop_invariant_consume(struct DoubleMap** m, struct DoubleChain** ch,
                            unsigned int lcore_id,
                            time_t time, int max_flows, int start_port);
/*@ requires *m |-> ?mp &*& *ch |-> ?chp &*&
             evproc_loop_invariant(mp, chp, lcore_id,
                                   time, max_flows, start_port); @*/
/*@ ensures *m |-> mp &*& *ch |-> chp; @*/

void loop_invariant_produce(struct DoubleMap** m, struct DoubleChain** ch,
                            unsigned int* lcore_id,
                            time_t *time, int max_flows, int start_port);
/*@ requires *m |-> ?mp &*& *ch |-> ?chp &*&
             *lcore_id |-> _ &*&
             *time |-> _; @*/
/*@ ensures *m |-> mp &*& *ch |-> chp &*&
            *lcore_id |-> ?lcid &*&
            *time |-> ?t &*&
            evproc_loop_invariant(mp, chp, lcid,
                                  t, max_flows, start_port); @*/

void loop_iteration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                          unsigned int lcore_id,
                          time_t time, int max_flows, int start_port);

void loop_iteration_end(struct DoubleMap** m, struct DoubleChain** ch,
                        unsigned int lcore_id,
                        time_t time, int max_flows, int start_port);

void loop_enumeration_begin(struct DoubleMap** m, struct DoubleChain** ch,
                            unsigned int lcore_id,
                            time_t time, int max_flows, int start_port,
                            int cnt);
//@ requires true;
//@ ensures true;

void loop_enumeration_end(struct DoubleMap** m, struct DoubleChain** ch,
                          unsigned int lcore_id,
                          time_t time, int max_flows, int start_port);
//@ requires true;
//@ ensures true;

#endif//LOOP_H_INCLUDED
