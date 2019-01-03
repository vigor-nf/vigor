#ifndef LOOP_H_INCLUDED
#define LOOP_H_INCLUDED

#include "lib/containers/double-chain.h"
#include "lib/containers/double-map.h"
#include "nat_flow.h"
#include "lib/coherence.h"
#include "lib/nf_time.h"

/*@
fixpoint bool nat_flow_fp(int start_port, dchain filter, int index, pair<flow, real> flw_cell) {
  switch(flw_cell) { case pair(flw, presence):
    return switch(flw) { case flw(iid, eid, dev):
      return switch(eid) { case flid(sp, dp, sip, dip, prot):
        return dchain_allocated_fp(filter, index) ? dp == start_port + index : true;
      };
    };
  }
}


predicate evproc_loop_invariant(struct Map* mp,
                                struct Vector* in_keys,
                                struct DoubleChain *chp,
                                struct Vector* in_values,
                                unsigned int lcore_id,
                                time_t time, int max_flows, int start_port) =
          mapp<flow_id>(mp, flow_idp, _flow_id_hash, nop_true, mapc(max_flows, ?m, ?maddr)) &*&
          vectorp<flow_id>(in_keys, flow_idp, ?iks, ?ikaddrs) &*&
          double_chainp(?ch, chp) &*&
          vectorp<flow>(in_values, flowp, ?ivs, ?ivaddrs) &*&
          map_vec_chain_coherent<flow_id>(m, iks, ch) &*&
          true == forall2(iks, ikaddrs, (kkeeper)(maddr)) &*&
          true == forall_idx(ivs, 0, (nat_flow_fp)(start_port, ch)) &*&
          lcore_id == 0 &*& //<-- We are verifying for a single core.
          last_time(time) &*&
          dchain_high_fp(ch) <= time &*&
          max_flows < INT_MAX;
@*/

void loop_iteration_assumptions(struct Map** m,
                                struct Vector** v_keys,
                                struct DoubleChain** ch,
                                struct Vector** v_vals,
                                unsigned int lcore_id,
                                time_t time, int max_flows, int start_port);

void loop_iteration_assertions(struct Map** m,
                               struct Vector** v_keys,
                               struct DoubleChain** ch,
                               struct Vector** v_vals,
                               unsigned int lcore_id,
                               time_t time, int max_flows, int start_port);

void loop_invariant_consume(struct Map** m,
                            struct Vector** v_keys,
                            struct DoubleChain** ch,
                            struct Vector** v_vals,
                            unsigned int lcore_id,
                            time_t time, int max_flows, int start_port);
/*@ requires *m |-> ?mp &*& *v_keys |-> ?vkp &*& *ch |-> ?chp &*&
             *v_vals |-> ?vvp &*&
             evproc_loop_invariant(mp, vkp, chp, vvp, lcore_id,
                                   time, max_flows, start_port); @*/
/*@ ensures *m |-> mp &*& *ch |-> chp; @*/

void loop_invariant_produce(struct Map** m,
                            struct Vector** v_keys,
                            struct DoubleChain** ch,
                            struct Vector** v_vals,
                            unsigned int* lcore_id,
                            time_t *time, int max_flows, int start_port);
/*@ requires *m |-> ?mp &*& *v_keys |-> ?vkp &*& *ch |-> ?chp &*&
             *v_vals |-> ?vvp &*&
             *lcore_id |-> _ &*&
             *time |-> _; @*/
/*@ ensures *m |-> mp &*& *v_keys |-> vkp &*& *ch |-> chp &*&
            *v_vals |-> vvp &*&
            *lcore_id |-> ?lcid &*&
            *time |-> ?t &*&
            evproc_loop_invariant(mp, vkp, chp, vvp, lcid,
                                  t, max_flows, start_port); @*/

void loop_iteration_begin(struct Map** m,
                          struct Vector** v_keys,
                          struct DoubleChain** ch,
                          struct Vector** v_vals,
                          unsigned int lcore_id,
                          time_t time, int max_flows, int start_port);

void loop_iteration_end(struct Map** m,
                        struct Vector** v_keys,
                        struct DoubleChain** ch,
                        struct Vector** v_vals,
                        unsigned int lcore_id,
                        time_t time, int max_flows, int start_port);

void loop_enumeration_begin(struct Map** m,
                            struct Vector** v_keys,
                            struct DoubleChain** ch,
                            struct Vector** v_vals,
                            unsigned int lcore_id,
                            time_t time, int max_flows, int start_port,
                            int cnt);
//@ requires true;
//@ ensures true;

void loop_enumeration_end(struct Map** m,
                          struct Vector** v_keys,
                          struct DoubleChain** ch,
                          struct Vector** v_vals,
                          unsigned int lcore_id,
                          time_t time, int max_flows, int start_port);
//@ requires true;
//@ ensures true;

#endif//LOOP_H_INCLUDED
