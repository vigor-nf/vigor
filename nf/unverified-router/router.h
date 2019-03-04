
#ifndef _router_h
#define _router_h

#define MAX_ROUTES_ENTRIES 256

#include "lpm_trie/lpm_trie_mem.h"
#include "parse_utils.h"
#include <stdio.h>
//#include <math.h>
#include <ctype.h>


/**
 * insert all routes from the csv file to the lpm trie
 */
int * insert_all(FILE * f, struct lpm_trie * t);

#endif
