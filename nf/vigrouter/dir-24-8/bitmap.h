#include <stdlib.h>
#include <stdbool.h>

/**
 * If index is free map[index] == 0, 1 otherwise
 */

struct bitmap{
	bool* map;
	size_t size;
	size_t n_elem;
};

struct bitmap* create_bitmap(size_t size);
size_t take_first_free_index(struct bitmap* bmap);
void free_bitmap_index(struct bitmap* bmap, size_t index);
bool is_bitmap_full(struct bitmap* bmap);
void free_bitmap(struct bitmap* bmap);

