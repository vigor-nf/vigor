#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

/**
 * If index is free map[index] == 0, 1 otherwise
 */

struct indexmap{
	bool* map;
	size_t size;
	size_t n_elem;
};

struct indexmap* create_indexmap(size_t size);
size_t take_first_free_index(struct indexmap* imap);
void free_indexmap_index(struct indexmap* imap, size_t index);
bool is_indexmap_full(struct indexmap* imap);
void free_indexmap(struct indexmap* imap);

