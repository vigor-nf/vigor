#include "libvig/stubs/core_stub.h"
#include "libvig/stubs/containers/str-descr.h"
#include "libvig/packet-io.h"

#include <stdlib.h>
#include <string.h>

#include <rte_byteorder.h>
#include <rte_mbuf.h>
#include <rte_mbuf_ptype.h>
#include <rte_memory.h>
#include <rte_ethdev.h>

#include "libvig/stubs/mbuf_content.h"

#ifdef KLEE_VERIFICATION
#include <klee/klee.h>
#else
#include <dsos-klee.h>
#endif

bool
stub_core_mbuf_create(uint16_t device, struct rte_mempool* pool, struct rte_mbuf** mbufp)
{
	uint16_t priv_size = rte_pktmbuf_priv_size(pool);
	uint16_t mbuf_size = sizeof(struct rte_mbuf) + priv_size;
	uint16_t buf_len = rte_pktmbuf_data_room_size(pool);

	*mbufp = rte_mbuf_raw_alloc(pool);
	if (*mbufp == NULL) {
		return false;
	}

	struct rte_mbuf* buf_symbol = (struct rte_mbuf*) malloc(pool->elt_size);
	if (buf_symbol == NULL) {
		rte_pktmbuf_free(*mbufp);
		return false;
	}

	// Make the packet symbolic
	klee_make_symbolic(buf_symbol, pool->elt_size, "buf_value");
	memcpy(*mbufp, buf_symbol, pool->elt_size);
	free(buf_symbol);

	// Explicitly make the content symbolic - validator depends on an user_buf symbol for the proof
        klee_assert(sizeof(struct stub_mbuf_content) <= pool->elt_size);
	struct stub_mbuf_content* buf_content_symbol = (struct stub_mbuf_content*) malloc(pool->elt_size);
	if (buf_content_symbol == NULL) {
		rte_pktmbuf_free(*mbufp);
		return false;
	}
	klee_make_symbolic(buf_content_symbol, pool->elt_size, "user_buf");
	memcpy((char*) *mbufp + mbuf_size, buf_content_symbol, sizeof(struct stub_mbuf_content));
	free(buf_content_symbol);

	// We do not support chained mbufs for now, make sure the NF doesn't touch them
	struct rte_mbuf* buf_next = (struct rte_mbuf*) malloc(pool->elt_size);
	if (buf_next == NULL) {
		rte_pktmbuf_free(*mbufp);
		return false;
	}
	klee_forbid_access(buf_next, pool->elt_size, "buf_next");

  uint16_t packet_length = klee_int("pkt_len");
  uint16_t data_length = klee_int("data_len");

  klee_assume(data_length <= packet_length);
  klee_assume(sizeof(struct ether_hdr) <= data_length);

	// Keep concrete values for what a driver guarantees
	// (assignments are in the same order as the rte_mbuf declaration)
	(*mbufp)->buf_addr = (char*) (*mbufp) + mbuf_size;
	(*mbufp)->buf_iova = (rte_iova_t) (*mbufp)->buf_addr; // we assume VA = PA
	// TODO: make data_off symbolic (but then we get symbolic pointer addition...)
	// Alternative: Somehow prove that the code never touches anything outside of the [data_off, data_off+data_len] range...
	(*mbufp)->data_off = 0; // klee_range(0, pool->elt_size - sizeof(struct stub_mbuf_content), "data_off");
	(*mbufp)->refcnt = 1;
	(*mbufp)->nb_segs = 1; // TODO do we want to make a possibility of multiple packets? Or we could just prove the NF never touches this...
	(*mbufp)->port = device;
	(*mbufp)->ol_flags = 0;
	// packet_type is symbolic
	(*mbufp)->pkt_len =  packet_length;
	(*mbufp)->data_len = data_length;
	// vlan_tci is symbolic
	// hash is symbolic
	// vlan_tci_outer is symbolic
	(*mbufp)->buf_len = (uint16_t) buf_len;
	// timestamp is symbolic
	(*mbufp)->udata64 = 0;
	(*mbufp)->pool = pool;
	(*mbufp)->next = buf_next;
	// tx_offload is symbolic
	(*mbufp)->priv_size = priv_size;
	// timesync is symbolic
	// seqn is symbolic

	rte_mbuf_sanity_check(*mbufp, 1 /* is head mbuf */);

	return true;
}

void
stub_core_mbuf_free(struct rte_mbuf* mbuf)
{
	// Undo our pseudo-chain trickery (see stub_core_mbuf_create)
	klee_allow_access(mbuf->next, mbuf->pool->elt_size);
	free(mbuf->next);
	mbuf->next = NULL;

	rte_mbuf_raw_free(mbuf);
}

