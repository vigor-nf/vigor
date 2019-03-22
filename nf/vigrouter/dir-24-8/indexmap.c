#include "indexmap.h"

void fill_map_zeros(struct indexmap* imap){
	for(size_t i = 0; ; i++)
	{
		if(i == imap->size){
			break;
		}
		
		imap->map[i] = false;
	}
}


struct indexmap* create_indexmap(size_t size){
	
	struct indexmap* imap = malloc(sizeof(struct indexmap));
	
	if(imap == 0){abort();}
		
	bool* map = malloc(size * sizeof(bool));
	
	if(map == 0){
		free(imap);
		abort();
	}
	
	imap->map = map;
	imap->size = size;
	imap->n_elem = 0;
	
	fill_map_zeros(imap);
	
	return imap;
	
}


size_t take_first_free_index(struct indexmap* imap)
{
	if(is_indexmap_full(imap)){
		return imap->size;
	}
	
	size_t index = 0;
	while(imap->map[index]){
		index++;
	}
	
	imap->map[index] = true;
	imap->n_elem++;
	
	return index;
}

void free_indexmap_index(struct indexmap* imap, size_t index)
{
	if(index < imap->size){
		imap->map[index] = 0;
		imap->n_elem--;
	}
}

bool is_indexmap_full(struct indexmap* imap)
{
	bool res = imap->size == imap->n_elem;
	return res;
}

void free_indexmap(struct indexmap* imap)
{
	free(imap->map);
	free(imap);
}
