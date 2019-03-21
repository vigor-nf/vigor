#include "bitmap.h"

void fill_map_zeros(struct bitmap* bmap){
	for(size_t i = 0; ; i++)
	{
		if(i == bmap->size){
			break;
		}
		
		bmap->map[i] = 0;
	}
}

size_t double_ceil(double x){
	
	size_t res = (double)((size_t)x) == x ? (size_t)x : (size_t)x + 1;
	return res;
}

struct bitmap* create_bitmap(size_t size){
	
	struct bitmap* bmap = malloc(sizeof(struct bitmap));
	
	if(bmap == 0){abort();}
	
	bool* map = malloc(double_ceil(size/sizeof(size_t)));
	
	if(map == 0){
		free(bmap);
		abort();
	}
	
	bmap->map = map;
	bmap->size = size;
	bmap->n_elem = 0;
	
	fill_map_zeros(bmap);
	
	return bmap;
	
}


size_t take_first_free_index(struct bitmap* bmap)
{
	if(is_bitmap_full(bmap)){
		return bmap->size;
	}
	
	size_t index = 0;
	while(bmap->map[index]){
		index++;
	}
	
	bmap->map[index] = 1;
	bmap->n_elem++;
	
	return index;
}

void free_bitmap_index(struct bitmap* bmap, size_t index)
{
	if(index < bmap->size){
		bmap->map[index] = 0;
		bmap->n_elem--;
	}
}

bool is_bitmap_full(struct bitmap* bmap)
{
	bool res = bmap->size == bmap->n_elem;
	return res;
}

void free_bitmap(struct bitmap* bmap)
{
	free(bmap->map);
	free(bmap);
}
