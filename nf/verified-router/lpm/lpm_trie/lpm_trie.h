#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

//FIXME: Unify with lpm_trie_mem.h
#define TRIE_SIZE_MAX 65535
#define LPM_TREE_NODE_FLAG_IM	1
#define LPM_DATA_SIZE 		4
#define LPM_PLEN_MAX		32

#define min(a, b) ((a<b) ? (a) : (b))

struct lpm_trie_node;

struct lpm_trie_node {
	//struct lpm_trie_node *child[2];
	struct lpm_trie_node l_child;
	struct lpm_trie_node r_child;
	uint32_t prefixlen;
	uint32_t flags;
	uint8_t data[LPM_DATA_SIZE];
	int *value;
};

struct lpm_trie {
	struct lpm_trie_node *root;
	size_t n_entries;
    size_t max_entries;
	void *node_mem_blocks;
	uintptr_t *node_ptr_stack;
	size_t next_ptr_index;
};

struct lpm_trie_key {
    uint32_t prefixlen;
    uint8_t data[LPM_DATA_SIZE];
};

//@ #include <listex.gh>

/*@
	inductive lpm_node = node(lpm_node, list<int>, option<int>, lpm_node) | empty;
	inductive lpm_trie = trie(lpm_node, int, int);

	predicate lpm_trie_p(struct lpm_trie *trie, lpm_trie t);
	predicate lpm_node_p(struct lpm_node *node, lpm_node n);
	predicate lpm_prefix_p(struct lpm_trie_key *key, list<int>);

	fixpoint bool is_empty(option<t> opt){
		switch(opt) {
			case none: return true;
			case some(v): return false;
		}
	}

	fixpoint int trie_size(lpm_trie t){
		switch(t){
			case trie(r, n, m): return n;
		}
	}

	fixpoint int trie_max(lpm_trie t){
		switch(t){
			case trie(r, n, m): return m;
		}
	}

	fixpoint lpm_trie empty_trie(int max){
		return trie(empty, 0, max);
	}

	fixpoint int match_length(lpm_node node, list<int> p){
		switch(node) {
			case empty: return 0;
			case node(lc, np, v, rc):
				return match_length_aux(np, p, 0);
			case im_node(lc, np, rc):
				return match_length_aux(np, p, 0);
		}
    }

    fixpoint int match_length_aux(list<int> p1, list<int> p2, int acc){
        switch(p1) {
            case nil: return acc;
            case cons(h1, t1):
                switch(p2) {
                    case nil: return acc;
                    case cons(h2, t2):
                        if(h1 == h2){
                            return match_length_aux(t1, t2, acc+1);
                        } else {
                            return acc;
                        }
                }
        }
    }

	fixpoint bool node_search(lpm_node root, lpm_node node,
                              fixpoint (lpm_node, lpm_node, bool) fp){
		if(fp(root)(node)){
			return true;
		} else {
			switch(node) {
				case empty: return false;
				case node(n_lc, np, nv, n_rc):
					switch(root) {
						case empty: return false;
						case node(r_lc, rp, rv, r_rc):
							if(match_length(root, np) < length(rp)){
								return false;
							} else {
								if(nth(length(rp), np) == 0){
									return node_search(r_lc, node);
								} else if(nth(length(rp), np) == 1){
									return node_search(r_rc, node);
								}
							}
					}
			}
		}
	}

	fixpoint bool node_equals(lpm_node n1, lpm_node n2){
		return n1 == n2;
	}

	fixpoint bool is_im_node(lpm_node node){
		switch(node) {
			case empty: return false;
			case node(lc, p, v, rc): return is_empty(v);
		}
	}

	fixpoint bool is_right_child(lpm_node par, lpm_node node){
		switch(par) {
			case empty: return false;
			case node(p_lc, pp, pv, p_rc):
				return node_equals(node, p_rc);
		}
	}

	fixpoint bool is_left_child(lpm_node par, lpm_node node){
		switch(par) {
			case empty: return false;
			case node(p_lc, pp, pv, p_rc):
				return node_equals(node, p_lc);
		}
	}

	fixpoint bool contains(lpm_trie trie, lpm_node node){
		switch(trie) {
			case trie(root, n, m):
				return node_search(root, node, node_equals);
		}
	}

	fixpoint bool same_prefix(lpm_node n1, lpm_node n2){
		switch(n1) {
			case empty: return false;
			case node(n1_lc, n1_p, n1_v, n1_rc):
				switch(n2) {
					case empty: return false;
					case node(n2_lc, n2_p, n2_v, n2_rc):
						return n1_p == n2_p;
				}
		}
	}

	fixpoint bool contains_prefix(lpm_trie trie, list<int> p){
		switch(trie) {
			case trie(root, n, m):
				lpm_node p_node = node(empty, p, none, empty);
				return node_search(root, p_node, same_prefix);
		}
	}

	fixpoint bool trie_condition(lpm_trie trie){
		switch(trie) {
			case trie(r, n, m):
				if(n == 0){
					return node_equals(r, empty);
				} else {
					return trie_cond_nodes(r) && node_count(trie) == n;
				}
		}
	}

	fixpoint bool has_two_children(lpm_node node){
		swicth(node) {
			case empty: return false;
			case node(lc, p, v, rc):
				switch(lc) {
					case empty: return false;
					case node(llc, lp, lv, lrc):
						switch(rc) {
							case empty: return false;
							case node(rlc, rp, rv, rrc):
								return true;
						}
				}
		}
	}

	fixpoint bool trie_cond_nodes(lpm_node node){
		switch(node) {
			case empty: return true;
			case node(lc, p, v, rc):
				if(is_im_node(node)){
					return has_two_children(node) && valid_child(lc, p, 0) &&
					       valid_child(rc, p, 1) && trie_cond_nodes(lc) &&
					       trie_cond_nodes(rc);
				} else {
					return valid_child(lc, p, 0) && valid_child(rc, p, 1) &&
						   trie_cond_nodes(lc) && trie_cond_nodes(rc);
				}
		}
	}

	fixpoint bool valid_child(lpm_node child, list<int> p_pref, int diff){
		switch(child) {
			case empty: return true;
			case node(c_lc, cp, cv, c_rc):
				if(match_length(child, p_pref) < length(p_pref)){
					return false;
				}
				if(nth(length(p_pref), cp) != diff){
					return false;
				}
				return true;
		}
	}

	fixpoint int node_count(lpm_trie trie){
		switch(trie) {
			case trie(r, n, m):
				return node_count_aux(r, 0);
		}
	}

	fixpoint int node_count_aux(lpm_node root, int acc){
		switch(root) {
			case empty:
			case node(lc, p, v, rc):
				switch(lc) {
					case empty:
						switch(rc) {
							case empty: return acc;
							case node(r_lc, rp, rv, r_rc):
								return node_count_aux(rc, acc+1);
						}
					case node(l_lc, lp, lv, l_lc):
						switch(rc) {
							case empty: return node_count_aux(lc, acc+1);
							case node(l_lc, lp, lv, l_rc):
								return node_count_aux(rc, acc + node_count_aux(lc, acc+1));
						}
				}
		}
	}

	fixpoint lpm_trie lpm_trie_update(lpm_trie trie, list<int> p, option<int> v){
		switch(trie){
			case trie(root, n, m):
				lpm_node new_node = node(empty, p, v, empty);
				return trie(lpm_trie_update_nodes(root, new_node),
			                lpm_trie_update_size(trie, p), m);
		}
	}

	fixpoint int lpm_trie_update_size(lpm_trie trie, lis<int> p){
		switch(trie){
			case trie(root, n, m):
			if(contains_prefix(trie, p)){
				return n;
			} else {
				return n+1;
			}
		}
	}

	fixpoint lpm_node lpm_trie_update_nodes(lpm_node root, lpm_node new){
		switch(root) {
			case empty: return new;
			case node(r_lc, rp, rv, r_rc):
				switch(new) {
					case empty:
					case node(n_lc, np, nv, n_rc):
						if(match_length(root, np) == length(rp)
						   && length(rp) == length(np)){
							return node(r_lc, rp, nv, l_lc);
						} else if(ml == length(rp) && length(rp) < length(np)){
							if(nth(length(rp), np) == 0){
								return node(lpm_trie_update_nodes(r_lc, new),
							                    rp, rv, r_rc);
							} else if(nth(length(rp), np) == 1){
								return node(r_lc, rp, rn,
								                lpm_trie_update_nodes(r_rc, new));
							}

						} else if(match_length(root, np) < length(rp) &&
						          length(np) < length(rp)){
							if(nth(length(np), rp) == 0){
								return node(root, np, nv, n_rc);
							} else if(nth(length(np), rp) == 1){
								return node(n_lc, np, nv, root);
							}

						} else if(match_length(root, np) < length(rp) &&
						          length(rp) == length(np)){
							if(nth(length(np)-1, np) == 0){
								return node(new, make_im_prefix(np, rp), none, root);
							} else if(nth(length(np)-1, np) == 1){
								return node(root, make_im_prefix(np, rp), none, new);
							}
						}

				}
		}
	}

	fixpoint list<int> make_im_prefix(list<int> p1, list<int> p2){
		int ml = match_length(p1, p2);
		return make_im_prefix_aux(p1, ml);
	}

	fixpoint list<int> make_im_prefix_aux(list<int> p, int ml){
		if(ml == 0){
			return nil;
		} else {
			switch(p) {
				case nil: return nil;
				case cons(h, t): return cons(h, make_im_prefix_aux(t, ml-1));
			}
		}
	}

	fixpoint lpm_trie lpm_trie_delete(lpm_trie trie, list<int> p){
		switch(trie) {
			case lpm_trie(root, n, m):
				return trie(lpm_trie_delete_nodes(node(root, nil, none, empty), p),
				            n-1, m);
		}
	}

	fixpoint lpm_node remove_node(lpm_node par, lpm_node rem){
		switch(rem) {
			case empty:
			case node(rem_lc, remp, remv, rem_rc){
				switch(rem_lc){
					case empty:
						switch(rem_rc) {
							case empty:
								//no children
								if(is_im_node(par)){
									//check for sibling, return it if it exists
									switch(par) {
										case empty:
										case node(p_lc, pp, pv, p_rc):
											if(is_left_child(par, rem)){
												return p_rc;
											} else if(is_right_child){
												return p_lc;
											}
									}
								} else {
									//remove rem
									switch(par) {
										case empty:
										case node(p_lc, pp, pv, p_rc):
											if(is_left_child(par, rem)){
												return node(empty, pp, pv, p_rc);
											} else if(is_right_child(par, rem)){
												return node(p_lc, pp, pv, empty);
											}
									}
								}

							case node(rem_rlc, rem_rp, rem_rv, rem_rrc):
								//one child, to the right
								switch(par) {
									case empty:
									case node(p_lc, pp, pv, p_rc):
										//replace rem with rem_rc
										if(is_left_child(par, rem)){
											return node(rem_rc, pp, pv, p_rc);
										} else if(is_right_child(par, rem)){
											return node(p_lc, pp, pv, rem_rc);
										}
								}
						}

					case node(rem_llc, rem_lp, rem_lv, rem_lrc):
						switch(rem_rc) {
							case empty:
								//one child, to the left
								switch(par) {
									case empty:
									case node(p_lc, pp, pv, p_rc):
										//replace rem with rem_lc
										if(is_left_child(par, rem)){
											return node(rem_lc, pp, pv, p_rc);
										} else if(is_right_child(par, rem)){
											return node(p_lc, pp, pv, rem_lc);
										}
								}
							case node(rem_rlc, rem_rp, rem_rv, rem_rrc):
								//two children -> mark rem as intermediary node
								if(is_left_child(par, rem)){
									return node(node(rem_lc, remp, none, rem_rc), pp, pv, p_rc);
								} else if(is_right_child(par, rem)){
									return node(p_lc, pp, pv, node(rem_lc, remp, none, rem_rc));
								}
						}
				}
			}
		}
	}

	fixpoint lpm_node lpm_trie_delete_nodes(lpm_node par, list<int> p){
		swicth(par) {
			case empty: return empty;
			case node(p_lc, pp, pv, p_rc):
				if(match_length(par, p) < length(p) && length(pp) < length(p)){

					if(nth(length(pp), p) == 0){
						//check prefix match with left child;
						switch(p_lc) {
							case empty: return par;
							case node(l_lc, lp, lv, l_rc):
								if(match_length(p_lc, p) < length(p) && length(lp) < length(p)){
									return node(lpm_trie_dele_nodes(p_lc, p), pp, pv, p_rc);
								} else if(match_length(p_lc, p) == length(p) && length(lp) == length(p)){
									//remove left child
									return remove_node(par, p_lc);
								}
						}

					} else if(nth(length(pp), p) == 1){
						//check prefix match with right child;
						switch(p_rc) {
							case empty: return par;
							case node(r_lc, rp, rv, r_rc):
								if(match_length(p_rc, p) < length(p) && length(rp) < length(p)){
									return node(p_lc, pp, pv, lpm_trie_dele_nodes(p_rc, p));
								} else if(match_length(p_rc, p) == length(p) && length(rp) == length(p)){
									//remove right child
									return remove_node(par, p_rc);
								}
						}
					}
				}
		}
	}

	fixpoint option<int> trie_lookup(lpm_trie trie, list<int> p){
		switch(trie) {
			case trie(root, n, m):
				return trie_lookup_nodes(root, p);
		}
	}

	fixpoint option<int> trie_lookup_nodes(lpm_node par, lpm_node cur, list<int> p){
		switch(cur) {
			case empty:
				switch(par) {
					case empty: return none;
					case node(p_lc, pp, pv, p_rc): return pv;
				}
			case node(c_lc, cp, cv, c_rc):
				if(match_length(cur, p) < length(cp)){
					switch(par) {
						case empty: return none;
						case node(p_lc, pp, pv, p_rc): return pv;
					}
				}

				else if(match_length(cur, p) == length(cp)){
					if(length(cp) == length(p)){
						return cv;
					} else if(length(cp) < length(p)){
						if(nth(length(cp), p) == 0){
							return trie_lookup_nodes(cur, c_lc, p);
						} else if(nth(length(cp), p) == 1){
							return trie_lookup_nodes(cur, c_rc, p);
						}
					}
				}
		}
	}

@*/

struct lpm_trie_node *lpm_trie_node_alloc(struct lpm_trie *trie, int *value);
/*@ requires value == NULL || *value >= 0; @*/
/*@ ensures lpm_node_p(result, node(empty, nil,
                                    value == NULL ? none : some(*value),
                                    empty)); @*/

struct lpm_trie *lpm_trie_alloc(size_t max_entries);
/*@ requires max_entries > 0; @*/
/*@ ensures lpm_trie_p(result, trie(empty, 0, max_entries)); @*/

void trie_free(struct lpm_trie *trie);
/*@ requires lpm_trie_p(trie, ?t); @*/
/*@ ensures true; @*/

int extract_bit(const uint8_t *data, size_t index);
/*@ requires true; @*/
/*@ ensures true; @*/

size_t longest_prefix_match(const struct lpm_trie_node *node,
                            const struct lpm_trie_key *key);
/*@ requires true; @*/
/*@ ensures true; @*/

int *trie_lookup_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires lpm_trie_p(trie, ?t) &*&
             lpm_prefix_p(_key, ?p) &*&
             trie_condition(t); @*/
/*@ ensures is_empty(trie_lookup(t, p)) ?
				result == -1 :
				result == the(trie_lookup(t, p)) &*&
            trie_condition(t); @*/

int trie_update_elem(struct lpm_trie *trie, struct lpm_trie_key *key, int *value);
/*@ requires lpm_trie_p(trie, ?t1) &*&
             lpm_prefix_p(_key, ?p) &*& //TODO: find way to generate list<int>
             trie_size(t1) < trie_max(t1) &*&
             trie_condition(t1) == true; @*/
/*@ ensures lpm_trie_p(trie, lpm_trie_update(t1, p, v)) &*&
            trie_condition(lpm_trie_update(t1, p, v)); @*/

int trie_delete_elem(struct lpm_trie *trie, struct lpm_trie_key *key);
/*@ requires lpm_trie_p(trie, ?t1) &*&
             lpm_prefix_p(_key, ?p) &*&
             contains_prefix(t1, p) &*&
			 trie_condition(t1); @*/
/*@ ensures lpm_trie_p(trie, lpm_trie_delete(t1, p)) &*&
            trie_condition(lpm_trie_delete(t1, p)); @*/

/**
 * fls - find last (most-significant) bit set
 * @x: the word to search
 *
 * This is defined the same way as ffs.
 * Note fls(0) = 0, fls(1) = 1, fls(0x80000000) = 32.
 */
static int fls(unsigned int x)
/*@ requires true; @*/
/*@ ensures true; @*/
{
	int r = 32;

	if (!x)
		return 0;
	if (!(x & 0xffff0000u)) {
		x <<= 16;
		r -= 16;
	}
	if (!(x & 0xff000000u)) {
		x <<= 8;
		r -= 8;
	}
	if (!(x & 0xf0000000u)) {
		x <<= 4;
		r -= 4;
	}
	if (!(x & 0xc0000000u)) {
		x <<= 2;
		r -= 2;
	}
	if (!(x & 0x80000000u)) {
		x <<= 1;
		r -= 1;
	}
	return r;
}
