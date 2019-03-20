#include "lpm_trie_mem.h"

/*@
lemma void bytes_to_node_im(void* node)
requires chars((void*)node, sizeof(struct lpm_trie_node), ?chs);
ensures node_im_p(node);
{
    struct lpm_trie_node* node_s = node;
    node_layout_assumptions(node_s);
    chars_split((void*) node, sizeof(int));
    chars_to_integer((void*) &(node_s->l_child));
    chars_split((void*) node + sizeof(int), sizeof(int));
    chars_to_integer((void*) &(node_s->r_child));
    chars_split((void*) node + 2*sizeof(int), sizeof(int));
    chars_to_integer((void*) &(node_s->has_l_child));
    chars_split((void*) node + 3*sizeof(int), sizeof(int));
    chars_to_integer((void*) &(node_s->has_r_child));
    chars_split((void*) node + 4*sizeof(int), sizeof(uint32_t));
    chars_to_u_integer((void*) &(node_s->prefixlen));
    chars_split((void*) node + 4*sizeof(int) + sizeof(uint32_t),
                sizeof(uint32_t));
    chars_to_u_integer((void*) &(node_s->flags));
    chars_split((void*) node + 4*sizeof(int) + 2*sizeof(uint32_t),
                sizeof(int));
    chars_to_integer((void*) &(node_s->value));
    chars_split((void*) node + 4*sizeof(int) + 2*sizeof(uint32_t) +
                sizeof(int), LPM_DATA_SIZE*sizeof(uint8_t));
    close lpm_trie_node_l_child(node, _);
    close lpm_trie_node_r_child(node, _);
    close lpm_trie_node_has_l_child(node, _);
    close lpm_trie_node_has_r_child(node, _);
    close lpm_trie_node_mem_index(node, _);
    close lpm_trie_node_prefixlen(node, _);
    close lpm_trie_node_flags(node, _);
    close lpm_trie_node_value(node, _);
    close node_im_p(node);
}

lemma void bytes_to_nodes_im(void* node, nat len)
requires chars((void*)node, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);
ensures nodes_im_p(node, int_of_nat(len));
{
    switch(len) {
        case zero:
            close nodes_im_p(node, 0);
            break;
        case succ(n):
            assert 1 <= int_of_nat(len);
            mul_mono(1, int_of_nat(len), sizeof(struct lpm_trie_node));
            assert sizeof(struct lpm_trie_node) <= int_of_nat(len)*sizeof(struct lpm_trie_node);
            chars_split(node, sizeof(struct lpm_trie_node));
            assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
                   (int_of_nat(len)-1)*sizeof(struct lpm_trie_node);
            assert int_of_nat(len)-1 == int_of_nat(n);
            mul_subst(int_of_nat(len)-1, int_of_nat(n), sizeof(struct lpm_trie_node));
            assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
                   int_of_nat(n)*sizeof(struct lpm_trie_node);
            bytes_to_nodes_im(node+sizeof(struct lpm_trie_node), n);
            bytes_to_node_im(node);
            close nodes_im_p(node, int_of_nat(len));
    }
}

lemma void node_im_to_bytes(struct lpm_trie_node *node)
requires node_im_p(node);
ensures chars((void*) node, sizeof(struct lpm_trie_node), ?chs);
{
	void *_node = node;
	node_layout_assumptions(node);
	open node_im_p(node);
	open lpm_trie_node_l_child(node, _);
	integer_to_chars((void*) &node->l_child);
	open lpm_trie_node_r_child(node, _);
	integer_to_chars((void*) &node->r_child);
	chars_join(_node);
	open lpm_trie_node_has_l_child(node, _);
	integer_to_chars((void*) &node->has_l_child);
	chars_join(_node);
	open lpm_trie_node_has_r_child(node, _);
	integer_to_chars((void*) &node->has_r_child);
	chars_join(_node);
	open lpm_trie_node_prefixlen(node, _);
	u_integer_to_chars((void*) &node->prefixlen);
	chars_join(_node);
	open lpm_trie_node_flags(node, _);
	u_integer_to_chars((void*) &node->flags);
	chars_join(_node);
	open lpm_trie_node_value(node, _);
	integer_to_chars((void*) &node->value);
	chars_join(_node);
	uchars_to_chars((void*) node->data);
	chars_join(_node);
}

lemma void nodes_im_to_bytes(struct lpm_trie_node *first, nat len)
requires nodes_im_p(first, int_of_nat(len));
ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?chs);
{
	switch(len) {
		case zero:
			open nodes_im_p(first, int_of_nat(len));
			close chars((void*) first, 0, _);
			break;
		case succ(n):
			assert 1 <= int_of_nat(len);
			mul_mono(1, int_of_nat(len), sizeof(struct lpm_trie_node));
			assert sizeof(struct lpm_trie_node) <= int_of_nat(len)*sizeof(struct lpm_trie_node);
			open nodes_im_p(first, int_of_nat(len));
			assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
			       (int_of_nat(len)-1)*sizeof(struct lpm_trie_node);
			assert int_of_nat(len)-1 == int_of_nat(n);
			mul_subst(int_of_nat(len)-1, int_of_nat(n), sizeof(struct lpm_trie_node));
			assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
			       int_of_nat(n)*sizeof(struct lpm_trie_node);
			nodes_im_to_bytes(first + 1, n);
			node_im_to_bytes(first);
			chars_join((void*) first);
	}
}

lemma void node_to_bytes(struct lpm_trie_node *node)
requires node_p(node, ?max_i, ?n);
ensures chars((void*) node, sizeof(struct lpm_trie_node), ?cs);
{
    void *_node = node;
    node_layout_assumptions(node);
    open node_p(node, max_i);
    open lpm_trie_node_l_child(node, _);
    integer_to_chars((void*) &node->l_child);
    open lpm_trie_node_r_child(node, _);
    integer_to_chars((void*) &node->r_child);
    chars_join(_node);
    open lpm_trie_node_has_l_child(node, _);
    integer_to_chars((void*) &node->has_l_child);
    chars_join(_node);
    open lpm_trie_node_has_r_child(node, _);
    integer_to_chars((void*) &node->has_r_child);
    chars_join(_node);
    open lpm_trie_node_prefixlen(node, _);
    u_integer_to_chars((void*) &node->prefixlen);
    chars_join(_node);
    open lpm_trie_node_flags(node, _);
    u_integer_to_chars((void*) &node->flags);
    chars_join(_node);
    open lpm_trie_node_value(node, _);
    integer_to_chars((void*) &node->value);
    chars_join(_node);
    uchars_to_chars((void*) node->data);
    chars_join(_node);
}

lemma void nodes_to_bytes(struct lpm_trie_node *first, nat len)
requires nodes_p(first, int_of_nat(len), ?max_i, ?ns);
ensures chars((void*) first, int_of_nat(len)*sizeof(struct lpm_trie_node), ?cs);
{
    switch(len) {
        case zero:
            open nodes_p(first, int_of_nat(len), max_i, ns);
            close chars((void*) first, 0, _);
            break;
        case succ(n):
            assert 1 <= int_of_nat(len);
            mul_mono(1, int_of_nat(len), sizeof(struct lpm_trie_node));
            assert sizeof(struct lpm_trie_node) <= int_of_nat(len)*sizeof(struct lpm_trie_node);
            open nodes_p(first, int_of_nat(len), max_i, ns);
            assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
                   (int_of_nat(len)-1)*sizeof(struct lpm_trie_node);
            assert int_of_nat(len)-1 == int_of_nat(n);
            mul_subst(int_of_nat(len)-1, int_of_nat(n), sizeof(struct lpm_trie_node));
            assert int_of_nat(len)*sizeof(struct lpm_trie_node) - sizeof(struct lpm_trie_node) ==
                   int_of_nat(n)*sizeof(struct lpm_trie_node);
            nodes_to_bytes(first + 1, n);
            node_to_bytes(first);
            chars_join((void*) first);

    }
}

lemma void extract_node(struct lpm_trie_node *node, int i)
requires nodes_p(node, ?size, ?max_i, ?ns) &*& 0 <= i &*& i < size;
ensures nodes_p(node, i, max_i, take(i, ns)) &*&
        node_p(node+i, max_i, nth(i, ns)) &*&
        nodes_p(node+i+1, size-i-1, max_i, drop(i+1, ns));
{
    open nodes_p(node, size, max_i, ns);
    if(i == 0){
    } else {
        extract_node(node+1, i-1);
    }
    close nodes_p(node, i, max_i, ns);
}

lemma void extract_im_node(struct lpm_trie_node *node, int i)
requires nodes_im_p(node, ?size) &*& 0 <= i &*& i < size;
ensures nodes_im_p(node, i) &*&
        node_im_p(node+i) &*&
        nodes_im_p(node+i+1, size-i-1);
{
    open nodes_im_p(node, size);
    if(i == 0){
    } else {
        extract_im_node(node+1, i-1);
    }
    close nodes_im_p(node, i);
}

lemma void nodes_join(struct lpm_trie_node *node, list<node_mem_t> ns);
requires nodes_p(node, ?n, ?max_i, take(n, ns)) &*& nodes_p(node+n, ?n0, max_i, drop(n, ns));
ensures nodes_p(node, n+n0, max_i, ns);
{
    assume(false); //TODO
}

lemma void close_nodes(struct lpm_trie_node *first, int i, int size, list<node_mem_t> ns)
requires size > i &*& i >= 0 &*&
         nodes_p(first, i, ?max_i, take(i, ns)) &*&
         node_p(first+i, max_i, nth(i, ns)) &*&
         nodes_p(first+i+1, size-i-1, max_i, drop(i+1, ns));
ensures nodes_p(first, size, max_i, ns);
{
    if(i == 0){
        open nodes_p(first, i, max_i, take(i, ns));
        close nodes_p(first, size, max_i, take(i, ns));
    } else {
        close nodes_p(first+i, size-i, max_i, drop(i, ns));
        nodes_join(first);
    }
}

lemma void close_nodes_update(struct lpm_trie_node *first, int i, int size,
                              list<node_mem_t> ns, node_mem_t new)
requires size > i &*& i >= 0 &*&
         nodes_p(first, i, ?max_i, take(i, ns)) &*&
         node_p(first+i, max_i, new) &*&
         nodes_p(first+i+1, size-i-1, max_i, drop(i+1, ns));
ensures nodes_p(first, size, max_i, update(i, new, ns));
{
    take_update_unrelevant(i, i, new, ns);
    drop_update_unrelevant(i+1, i, new, ns);
    close_nodes(node, i, update(i, new, ns));
}
@*/
