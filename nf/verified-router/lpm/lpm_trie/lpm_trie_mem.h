#include "lib/double-chain.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>
#include <limits.h>

//@ #include <list.gh>
//@ #include "arith.gh"
//@ #include <nat.gh>
//@ #include <bitops.gh>

#define TRIE_SIZE_MAX 65535
#define MAX_NODE_SIZE 500
#define LPM_TREE_NODE_FLAG_IM	1
#define LPM_DATA_SIZE 		4
#define LPM_PLEN_MAX		32
#define INVALID_NODE_ID -1
#define INVALID_VAL -1
#define CHAR_BIT 8 //In limits.h, verifast does not see it

#define min(a, b) ((a<b) ? (a) : (b))

struct lpm_trie_node;

struct lpm_trie_node {
	int l_child;
	int r_child;
	//int mem_index;
	int has_l_child;
	int has_r_child;
	uint32_t prefixlen;
	uint32_t flags;
	int value;
	uint8_t data[LPM_DATA_SIZE];
};

struct lpm_trie {
	int root;
	size_t n_entries;
	size_t max_entries;
	struct DoubleChain *dchain;
	struct lpm_trie_node *node_mem_blocks;
};

struct lpm_trie_key {
	uint32_t prefixlen;
	uint8_t data[LPM_DATA_SIZE];
};

//@ inductive node_t = node(node_t, list<int>, option<int>, node_t) | empty;
//@ inductive node_mem_t = node_mem(option<int>, list<int>, option<int>, option<int>);
//@ inductive trie_t = trie(node_t, int, int);

/*@
	predicate trie_p(struct lpm_trie *trie, int n, int max, trie_t t) =
		//switch(t) {
		//	case trie(r, tn, m): return
			malloc_block_lpm_trie(trie) &*&
			trie->root |-> ?root &*&
			trie->n_entries |-> n &*&
			trie->max_entries |-> max &*&
			trie->dchain |-> ?dchain &*&
			trie->node_mem_blocks |-> ?mem_blocks &*&
			malloc_block_chars((void*)mem_blocks,
			(sizeof(struct lpm_trie_node) * max)) &*&
			n >= 0 &*&
			(n == 0 ? true : root >= 0 &*& root < max) &*&
			max > 0 &*& //max == m &*&
			IRANG_LIMIT >= max &*&
			double_chainp(?ch, dchain) &*&
			dchain_index_range_fp(ch) == max &*&
			dchain_high_fp(ch) <= 1 &*&
			(void*)0 < ((void*)(mem_blocks)) &*&
			(void*)(mem_blocks + max) <= (char*)UINTPTR_MAX &*&
			nodes_p(mem_blocks, max, max, ?ns); // &*&
			// (root == INVALID_NODE_ID ? trie_in_list(r, none, ns) == true :
			//                            trie_in_list(r, some(root), ns) == true) &*&
			// (root == INVALID_NODE_ID ? distinct(indexes(trie_nodes(r, none, ns))) == true :
			//                            distinct(indexes(trie_nodes(r, some(root), ns))) == true);

		//};

	predicate node_im_p(struct lpm_trie_node *node) =
		node->l_child |-> _ &*&
		node->r_child |-> _ &*&
		node->has_l_child |-> _ &*&
		node->has_r_child |-> _ &*&
		node->prefixlen |-> _ &*&
		node->flags |-> _ &*&
		node->value |-> _ &*&
		node->data[0..LPM_DATA_SIZE] |-> _;

	predicate node_p(struct lpm_trie_node* node, int max_i, node_mem_t n) =
		switch(n) {
			case node_mem(lc, p, v, rc): return
				node->l_child |-> ?l_child &*&
				node->r_child |-> ?r_child &*&
				node->has_l_child |-> ?has_l &*&
				node->has_r_child |-> ?has_r &*&
				node->prefixlen |-> ?prefixlen &*&
				node->flags |-> ?flags &*&
				node->value |-> ?value &*&
				uchars((void*) node->data, LPM_DATA_SIZE, ?chs) &*&
				l_child >= 0 &*& l_child < max_i &*&
				r_child >= 0 &*& r_child < max_i &*&
				valid_child(l_child, has_l, lc) == true &*&
				valid_child(r_child, has_r, rc) == true;
				// prefixlen == length(p) &*&
				// valid_data(chs, p, p) == true &*&
				// valid_value(value, v) == true &*&
				// (value == INVALID_VAL ? (flags & LPM_TREE_NODE_FLAG_IM) :
				//                         (flags & LPM_TREE_NODE_FLAG_IM)) == true;
		};

	predicate key_p(struct lpm_trie_key *key, list<int> p) =
		malloc_block_lpm_trie_key(key) &*&
		key->prefixlen |-> ?prefixlen &*&
		uchars((void*) key->data, LPM_DATA_SIZE, ?chs); // &*&
		// prefixlen == length(p) &*&
		// valid_data(chs, p, p) == true;

	predicate nodes_im_p(struct lpm_trie_node *node, int count) =
		count == 0 ?
			true
		:
			node_im_p(node) &*& nodes_im_p(node + 1, count - 1);

	predicate nodes_p(struct lpm_trie_node* node, int count, int max_i, list<node_mem_t> ns) =
		count == 0 ?
			ns == nil
		:
			node_p(node, max_i, ?n) &*& nodes_p(node+1, count-1, max_i, ?ns0) &*&
			ns == cons(n, ns0);

@*/

/*@
	lemma void node_layout_assumptions(struct lpm_trie_node *node);
	requires true;
	ensures sizeof(struct lpm_trie_node) == 4*sizeof(int) +
	                                        2*sizeof(uint32_t) +
											sizeof(int) +
	                                        LPM_DATA_SIZE*sizeof(uint8_t) &*&
	        (void*) &(node->l_child) + sizeof(int) ==
	        (void*) &(node->r_child) &*&
	        (void*) &(node->r_child) + sizeof(int) ==
	        (void*) &(node->has_l_child) &*&
	        (void*) &(node->has_l_child) + sizeof(int) ==
	        (void*) &(node->has_r_child) &*&
	        (void*) &(node->has_r_child) + sizeof(int) ==
	        (void*) &(node->prefixlen) &*&
	        (void*) &(node->prefixlen) + sizeof(uint32_t) ==
	        (void*) &(node->flags) &*&
	        (void*) &(node->flags) + sizeof(uint32_t) ==
	        (void*) &(node->value) &*&
	        (void*) &(node->value) + sizeof(int) ==
	        (void*) node->data;
@*/

/*@
	lemma void dchain_allocate_range_time(struct DoubleChain *dchain, int max, int ni);
	requires double_chainp(?ch, dchain) &*&
	         dchain_index_range_fp(ch) == max &*&
	         dchain_high_fp(ch) <= 1;
	ensures double_chainp(dchain_allocate_fp(ch, ni, 1), dchain) &*&
	        dchain_index_range_fp(dchain_allocate_fp(ch, ni, 1)) == max &*&
	        dchain_high_fp(dchain_allocate_fp(ch, ni, 1)) <= 1;

	fixpoint bool char_equals(int i, char c){
		return i == c;
	}

	lemma void bytes_to_node_im(void* node);
	requires chars((void*)node, sizeof(struct lpm_trie_node), ?chs);
	ensures node_im_p(node);

	lemma void bytes_to_nodes_im(void* node, nat len);
	requires chars((void*)node, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);
	ensures nodes_im_p(node, int_of_nat(len));

	lemma void node_im_to_bytes(struct lpm_trie_node *node);
	requires node_im_p(node);
	ensures chars((void*) node, sizeof(struct lpm_trie_node), ?chs);

	lemma void nodes_im_to_bytes(struct lpm_trie_node *first, nat len);
	requires nodes_im_p(first, int_of_nat(len));
	ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);

	lemma void node_to_bytes(struct lpm_trie_node *node);
	requires node_p(node, ?max_i, ?n);
	ensures chars((void*) node, sizeof(struct lpm_trie_node), ?cs);

	lemma void nodes_to_bytes(struct lpm_trie_node *first, nat len);
	requires nodes_p(first, int_of_nat(len), ?max_i, ?ns);
	ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?cs);

	lemma void extract_node(struct lpm_trie_node *node, int i);
	requires nodes_p(node, ?size, ?max_i, ?ns) &*& 0 <= i &*& i < size;
  	ensures nodes_p(node, i, max_i, take(i, ns)) &*&
	        node_p(node+i, max_i, nth(i, ns)) &*&
	        nodes_p(node+i+1, size-i-1, max_i, drop(i+1, ns));

	lemma void extract_im_node(struct lpm_trie_node *node, int i);
	requires nodes_im_p(node, ?size) &*& 0 <= i &*& i < size;
  	ensures nodes_im_p(node, i) &*&
	        node_im_p(node+i) &*&
	        nodes_im_p(node+i+1, size-i-1);

	lemma void nodes_join(struct lpm_trie_node *node, list<node_mem_t> ns);
	requires nodes_p(node, ?n, ?max_i, take(n, ns)) &*& nodes_p(node+n, ?n0, max_i, drop(n, ns));
	ensures nodes_p(node, n+n0, max_i, ns);

	lemma void close_nodes(struct lpm_trie_node *first, int i, int size, list<node_mem_t> ns);
	requires size > i &*& i >= 0 &*&
	         nodes_p(first, i, ?max_i, take(i, ns)) &*&
	         node_p(first+i, max_i, nth(i, ns)) &*&
	         nodes_p(first+i+1, size-i-1, max_i, drop(i+1, ns));
	ensures nodes_p(first, size, max_i, ns);

	lemma void close_nodes_update(struct lpm_trie_node *first, int i, int size,
	                              list<node_mem_t> ns, node_mem_t new);
	requires size > i &*& i >= 0 &*&
	         nodes_p(first, i, ?max_i, take(i, ns)) &*&
	         node_p(first+i, max_i, new) &*&
	         nodes_p(first+i+1, size-i-1, max_i, drop(i+1, ns));
	ensures nodes_p(first, size, max_i, update(i, new, ns));
@*/

/*@
	fixpoint bool is_bit(int i) {
		return i == 0 || i == 1;
	}

	fixpoint bool trie_in_list(node_t node, option<int> opt_i, list<node_mem_t> node_mems) {
		switch(node) {
			case empty: return switch(opt_i) {
				case none: return true;
				case some(i): return false;
			};
			case node(lc, p, v, rc): return switch(opt_i) {
				case none: return false;
				case some(i): return switch((node_mem_t) nth(i, node_mems)) {
					case node_mem(l_child, prefix, value, r_child):
						//Establish equivalence between node and node_mem here
						return p == prefix && v == value &&
						       trie_in_list(lc, l_child, node_mems) &&
						       trie_in_list(rc, r_child, node_mems);
				};
			};
		}
	}

	fixpoint list<node_mem_t> trie_nodes(node_t n, option<int> opt_i, list<node_mem_t> node_mems) {
		switch(n) {
			case empty: return nil;
			case node(lc, p, v, rc): return switch(opt_i) {
				case none: return nil;
				case some(i): return switch((node_mem_t) nth(i, node_mems)) {
					case node_mem(l_child, prefix, value, r_child):
						return append(trie_nodes(lc, l_child, node_mems),
						              cons(nth(i, node_mems), trie_nodes(rc, r_child, node_mems)));
				};
			};
		}
	}

	fixpoint int node_l_child_int_fp(node_mem_t node) {
		switch(node) {
			case node_mem(lc, p, v, rc): return switch(lc) {
				case none: return INVALID_NODE_ID;
				case some(l): return l;
			};
		}
	}

	fixpoint option<int> node_l_child_fp(node_mem_t node) {
		switch(node) {
			case node_mem(lc, p, v, rc): return lc;
		}
	}

	fixpoint option<int> node_r_child_fp(node_mem_t node) {
		switch(node) {
			case node_mem(lc, p, v, rc): return rc;
		}
	}

	fixpoint int node_r_child_int_fp(node_mem_t node) {
		switch(node) {
			case node_mem(lc, p, v, rc): return switch(rc) {
				case none: return INVALID_NODE_ID;
				case some(r): return r;
			};
		}
	}

	fixpoint list<int> indexes(list<node_mem_t> nodes) {
		return append(map(node_l_child_int_fp, nodes), map(node_r_child_int_fp, nodes));
	}

	fixpoint bool unique_indexes(list<int> ids) {
		return distinct(ids) == true;
	}

	fixpoint bool valid_value(int value, option<int> val) {
		switch(val) {
			case none: return value == INVALID_VAL;
			case some(v): return value == v;
		}
	}

	fixpoint bool valid_children(int l_child, int r_child, int has_l, int has_r,
	                             option<int> lc, option<int> rc)
	{
		switch(lc) {
			case none: return switch(rc) {
				case none:
					return has_l == 0 && has_r == 0;
				case some(rm):
					return has_l == 0 && has_r == 1 &&
					       r_child == rm;
			};
			case some(lm): return switch(rc) {
				case none:
					return has_l == 1 && has_r == 0 &&
					       l_child == lm;
				case some(rm):
					return has_l == 1 && has_r == 1 &&
					       l_child != r_child && l_child == lm &&
					       r_child == rm;
			};
		}
	}

	fixpoint bool valid_child(int child, int has, option<int> c) {
		switch(c) {
			case none: return has == 0;
			case some(cc): return has != 0 && child == cc;
		}
	}

	fixpoint int extract_bit_single(unsigned char c, int index) {
		return (c & (1 << (7 - index)));
	}

	fixpoint int extract_bit(list<unsigned char> data, int index) {
		return extract_bit_single(nth(index/8, data), index % 8);
	}

	fixpoint bool valid_data_single(unsigned char c, list<int> ps, list<int> old_ps)
	{
		switch(ps) {
			case nil: return true;
			case cons(p, p0s):
				return extract_bit_single(c, index_of(p, old_ps)) == p &&
				       valid_data_single(c, p0s, old_ps);
		}
	}

	fixpoint bool valid_data(list<unsigned char> data, list<int> ps, list<int> old_ps)
	{
		switch(ps) {
			case nil: return true;
			case cons(p, p0s):
				return extract_bit(data, index_of(p, old_ps)) == p &&
				       valid_data(data, p0s, old_ps);
		}
	}

	fixpoint trie_t empty_trie(int max_i) {
		return trie(empty, 0, max_i);
	}

	fixpoint node_mem_t unalloced_node() {
		return node_mem(none, nil, none, none);
	}

	fixpoint node_mem_t node_no_l_child(node_mem_t node) {
		switch(node) {
			case node_mem(lc, p, v, rc): return node_mem(none, p, v, rc);
		}
	}

	fixpoint node_mem_t node_no_r_child(node_mem_t node) {
		switch(node) {
			case node_mem(lc, p, v, rc): return node_mem(lc, p, v, none);
		}
	}

	fixpoint node_mem_t node_set_l_child(node_mem_t node, int l_child) {
		switch(node) {
			case node_mem(lc, p, v, rc):
				return node_mem(some(l_child), p, v, rc);
		}
	}

	fixpoint node_mem_t node_set_r_child(node_mem_t node, int r_child) {
		switch(node) {
			case node_mem(lc, p, v, rc):
				return node_mem(lc, p, v, some(r_child));
		}
	}

	fixpoint list<int> bits_from_char(char c, nat len) {
		switch(len) {
			case zero: return nil;
			case succ(n):
				return cons(extract_bit_single(c, int_of_nat(n)-1),
				            bits_from_char(c, n));
		}
	}

	fixpoint list<int> bits_from_chars(list<char> cs) {
		switch(cs) {
			case nil: return nil;
			case cons(c, cs0): return
				append(bits_from_char(c, nat_of_int(CHAR_BIT)), bits_from_chars(cs0));
		}
	}

	fixpoint node_mem_t node_set_prefix(node_mem_t node, list<int> prefix) {
		switch(node) {
			case node_mem(lc, p, v, rc):
				return node_mem(lc, prefix, v, rc);
		}
	}
@*/

/*@
	fixpoint int match_length_aux(list<int> p1, list<int> p2, int acc){
		switch(p1) {
			case nil: return acc;
			case cons(h1, t1): return switch(p2) {
				case nil: return acc;
				case cons(h2, t2):
					return (h1 == h2 ? match_length_aux(t1, t2, acc + 1) : acc);
			};
		}
	}

	fixpoint int match_length(node_t node, list<int> p){
		switch(node) {
			case empty: return 0;
			case node(lc, np, v, rc):
				return match_length_aux(np, p, 0);
		}
	}

	fixpoint list<int> make_im_prefix_aux(list<int> p, nat ml){
		switch(ml) {
			case zero: return nil;
			case succ(n): return switch(p) {
				case nil: return nil;
				case cons(h, t): return cons(h, make_im_prefix_aux(t, n));
			};
		}
	}

	fixpoint list<int> make_im_prefix(list<int> p1, list<int> p2){
		return make_im_prefix_aux(p1, nat_of_int(match_length_aux(p1, p2, 0)));
	}

	fixpoint option<int> trie_lookup_nodes(node_t par, node_t cur, list<int> p){
		switch(cur) {
			case empty: return
				switch(par) {
					case empty: return none;
					case node(p_lc, pp, pv, p_rc): return pv;
				};
			case node(c_lc, cp, cv, c_rc): return
				(match_length(cur, p) < length(cp) ?
					switch(par) {
						case empty: return none;
						case node(p_lc, pp, pv, p_rc): return pv;
					} :
					(length(cp) == length(p) ? cv :
						(nth(length(cp), p) == 0 ?
							trie_lookup_nodes(cur, c_lc, p) :
							trie_lookup_nodes(cur, c_rc, p))
					)
				);
		}
	}

	fixpoint bool node_search(node_t root, node_t node, fixpoint (node_t, node_t, bool) fp) {
		switch(root) {
			case empty: return false;
			case node(r_lc, rp, rv, r_rc): return
				(fp(root, node) ? true :
					switch(node) {
						case empty: return false;
						case node(n_lc, np, nv, n_rc): return
							(match_length(root, np) < length(rp) ? false :
								(nth(length(rp), np) == 0 ?
									node_search(r_lc, node, fp) :
									node_search(r_rc, node, fp)
								)
							);
					}
				);
		}
	}

	fixpoint bool same_prefix(node_t n1, node_t n2){
		switch(n1) {
			case empty: return false;
			case node(n1_lc, n1_p, n1_v, n1_rc): return
				switch(n2) {
					case empty: return false;
					case node(n2_lc, n2_p, n2_v, n2_rc):
						return n1_p == n2_p;
				};
		}
	}

	fixpoint bool contains_prefix(trie_t trie, list<int> p){
		switch(trie) {
			case trie(root, n, m): return
				node_search(root, node(empty, p, none, empty), same_prefix);
		}
	}

	fixpoint int lpm_trie_update_size(trie_t trie, list<int> p){
		switch(trie){
			case trie(root, n, m): return
			(contains_prefix(trie, p) ? n : n+1);
		}
	}

	fixpoint node_t lpm_trie_update_nodes(trie_t trie, node_t root, node_t new){
		switch(root) {
			case empty: return new;
			case node(r_lc, rp, rv, r_rc): return
				switch(new) {
					case empty: return root;
					case node(n_lc, np, nv, n_rc): return
						(match_length(root, np) == length(rp) ?
							(length(rp) == length(np) ?
							 	node(r_lc, rp, nv, r_rc) :
								(nth(length(rp), np) == 0 ?
									node(lpm_trie_update_nodes(trie, r_lc, new), rp, rv, r_rc) :
									node(r_lc, rp, rv, lpm_trie_update_nodes(trie, r_rc, new))
								)
							) :
							(length(rp) == length(np) ?
								(nth(length(np)-1, np) == 0 ?
									node(new, make_im_prefix(np, rp), none, root) :
									node(root, make_im_prefix(np, rp), none, new)
								) :
								(nth(length(np), rp) == 0 ?
									node(root, np, nv, n_rc) :
									node(n_lc, np, nv, root)
								)
							)
						);
				};
		}
	}

	fixpoint option<int> make_value(int v) {
		return v == INVALID_VAL ? none : some(v);
	}

	fixpoint trie_t lpm_trie_update(trie_t trie, list<int> p, int v){
		switch(trie){
			case trie(root, n, m): return
				trie(lpm_trie_update_nodes(trie, root, node(empty, p, make_value(v), empty)),
				     lpm_trie_update_size(trie, p), m);
		}
	}

	fixpoint bool is_im_node(node_t node) {
		switch(node) {
			case empty: return false;
			case node(lc, p, v, rc): return
				switch(v) {
					case none: return true;
					case some(x): return false;
				};
		}
	}

	fixpoint bool is_left_child(node_t par, node_t node) {
		switch(par) {
			case empty: return false;
			case node(p_lc, pp, pv, p_rc): return p_lc == node;
		}
	}

	fixpoint node_t remove_node(node_t par, node_t rem) {
		switch(rem) {
			case empty: return par;
			case node(rem_lc, remp, remv, rem_rc): return
				switch(rem_lc){
					case empty: return
						switch(rem_rc) {
							case empty: return
								//no children
								(is_im_node(par) ?
									//check for sibling, return it if it exists
									switch(par) {
										case empty: return empty;
										case node(p_lc, pp, pv, p_rc): return
											(is_left_child(par, rem) ? p_rc : p_lc);
									} :
									//remove rem
									switch(par) {
										case empty: return empty;
										case node(p_lc, pp, pv, p_rc): return
											(is_left_child(par, rem) ?
												node(empty, pp, pv, p_rc) :
												node(p_lc, pp, pv, empty)
											);
									}
								);

							case node(rem_rlc, rem_rp, rem_rv, rem_rrc): return
								//one child, to the right
								switch(par) {
									case empty: return empty;
									case node(p_lc, pp, pv, p_rc): return
										//replace rem with rem_rc
										(is_left_child(par, rem) ?
											node(rem_rc, pp, pv, p_rc) :
											node(p_lc, pp, pv, rem_rc)
										);
								};
						};

					case node(rem_llc, rem_lp, rem_lv, rem_lrc): return
						switch(rem_rc) {
							case empty: return
								//one child, to the left
								switch(par) {
									case empty: return empty;
									case node(p_lc, pp, pv, p_rc): return
										//replace rem with rem_lc
										(is_left_child(par, rem) ?
											node(rem_lc, pp, pv, p_rc) :
											node(p_lc, pp, pv, rem_lc)
										);
								};
							case node(rem_rlc, rem_rp, rem_rv, rem_rrc): return
								//two children -> mark rem as intermediary node
								switch(par) {
									case empty: return empty;
									case node(p_lc, pp, pv, p_rc): return
									(is_left_child(par, rem) ?
										node(node(rem_lc, remp, none, rem_rc), pp, pv, p_rc) :
										node(p_lc, pp, pv, node(rem_lc, remp, none, rem_rc))

									);
								};
						};
				};
		}
	}

	fixpoint node_t lpm_trie_delete_nodes(node_t par, list<int> p) {
		switch(par) {
			case empty: return empty;
			case node(p_lc, pp, pv, p_rc): return
				(nth(length(pp), p) == 0 ?
					//check prefix match with left child
					switch(p_lc) {
						case empty: return par;
						case node(l_lc, lp, lv, l_rc): return
							(match_length(p_lc, p) < length(p) ?
								node(lpm_trie_delete_nodes(p_lc, p), pp, pv, p_rc) :
								//remove left child
								remove_node(par, p_lc)
							);
					} :
					//check prefix match with right child;
					switch(p_rc) {
						case empty: return par;
						case node(r_lc, rp, rv, r_rc): return
							(match_length(p_rc, p) < length(p) ?
								node(p_lc, pp, pv, lpm_trie_delete_nodes(p_rc, p)) :
								//remove right child
								remove_node(par, p_rc)
							);
					}
				);
		}
	}

	fixpoint trie_t lpm_trie_delete(trie_t trie, list<int> p){
		switch(trie) {
			case trie(root, n, m):
				return trie(lpm_trie_delete_nodes(node(root, nil, none, empty), p), n-1, m);
		}
	}
@*/

int lpm_trie_node_alloc(struct lpm_trie *trie, int value);
/*@ requires trie_p(trie, ?n, ?max_i, ?t); @*/
/*@ ensures trie_p(trie, n, max_i, t) &*&
            (result == INVALID_NODE_ID ? true : result >= 0 &*& result < max_i); @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires max_entries > 0 &*& max_entries <= IRANG_LIMIT &*&
             sizeof(struct lpm_trie_node) < MAX_NODE_SIZE; @*/
/*@ ensures result == NULL ? true : trie_p(result, 0, max_entries, empty_trie(max_entries)); @*/

bool extract_bit(const uint8_t *data, size_t index);
/*@ requires data[0..LPM_DATA_SIZE] |-> _ &*&
             index >= 0 &*& LPM_DATA_SIZE > index / 8; @*/
/*@ ensures data[0..LPM_DATA_SIZE] |-> _;@*/

size_t longest_prefix_match(const struct lpm_trie_node *node,
                            const struct lpm_trie_key *key);
/*@ requires node_p(node, ?max_i, ?n) &*& key_p(key, ?p); @*/
/*@ ensures node_p(node, max_i, n) &*& key_p(key, p); @*/

int trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires trie_p(trie, ?n, ?max_i, ?t) &*& key_p(key, ?p) &*& n > 0; @*/
/*@ ensures trie_p(trie, n, max_i, t) &*& key_p(key, p); @*/

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int value);
/*@ requires trie_p(trie, ?n1, ?max_i, ?t) &*& n1 < max_i &*&
             key_p(key, ?p); @*/
/*@ ensures (result == -1 ?
             trie_p(trie, _, max_i, t) :
             trie_p(trie, _, max_i, lpm_trie_update(t, p, value)) ) &*&
            key_p(key, p); @*/

int trie_delete_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires trie_p(trie, ?n, ?max_i, ?t) &*& n > 0 &*& key_p(key, ?p); @*/
/*@ ensures (result == -1 ?
             trie_p(trie, _, max_i, t) :
             trie_p(trie, _, max_i, lpm_trie_delete(t, p))) &*& key_p(key, p); @*/

/**
 * fls - find last (most-significant) bit set
 * @x: the word to search
 *
 * This is defined the same way as ffs.
 * Note fls(0) = 0, fls(1) = 1, fls(0x80000000) = 32.
 */
static unsigned int fls(unsigned int x)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	unsigned int r = 32;

	if (!x)
		return 0;
	if (!(x & 0xffff0000u)) {
		//@ bitand_limits(0x0000ffffu, x, nat_of_int(16));
		//@ shiftleft_limits(0x0000ffffu & x, nat_of_int(16), nat_of_int(16));
		x = (x & 0x0000ffffu) << 16;
		r -= 16;
	}
	if (!(x & 0xff000000u)) {
		//@ bitand_limits(0x00ffffffu, x, nat_of_int(24));
		//@ shiftleft_limits(0x00ffffffu & x, nat_of_int(24), nat_of_int(8));
		x = (x & 0x00ffffffu) << 8;
		r -= 8;
	}
	if (!(x & 0xf0000000u)) {
		//@ bitand_limits(0x0fffffffu, x, nat_of_int(28));
		//@ shiftleft_limits(0x0fffffffu & x, nat_of_int(28), nat_of_int(4));
		x = (x & 0x0fffffffu) << 4;
		r -= 4;
	}
	if (!(x & 0xc0000000u)) {
		//@ bitand_limits(0x1fffffffu, x, nat_of_int(30));
		//@ shiftleft_limits(0x1fffffffu & x, nat_of_int(30), nat_of_int(2));
		x = (x & 0x1fffffffu) << 2;
		r -= 2;
	}
	if (!(x & 0x80000000u)) {
		//@ bitand_limits(0x3fffffffu, x, nat_of_int(31));
		//@ shiftleft_limits(0x3fffffffu & x, nat_of_int(31), nat_of_int(1));
		x = (x & 0x3fffffffu) << 1;
		r -= 1;
	}
	return r;
}
