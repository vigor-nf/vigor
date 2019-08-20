// used with VeriFast, cannot use #pragma
#ifndef CORE_STUB_H
#define CORE_STUB_H

#include <stdbool.h>
#include <stdint.h>

#include <rte_mempool.h>

struct rte_mbuf;

bool stub_core_mbuf_create(uint16_t device, struct rte_mempool *pool,
                           struct rte_mbuf **mbufp);
void stub_core_mbuf_free(struct rte_mbuf *mbuf);

#endif
