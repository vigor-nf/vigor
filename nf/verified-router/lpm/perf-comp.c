#include "lpm_trie/lpm_trie_mem.h"
#include "dir-24-8/dir-24-8-basic.h"

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdbool.h>
#include <limits.h>
#include <math.h>
#include <time.h>
#include <unistd.h>

//Print data stored in a node in as data[0].data[1]. ... /prefixlen
void print_node_data(struct lpm_trie_node *node, struct lpm_trie *trie)
{
    for(int i = 0; i < LPM_DATA_SIZE; i++){
        printf("%d", node->data[i]);
        if(i < LPM_DATA_SIZE - 1)
            printf(".");
    }
    printf("/%d\n", node->prefixlen);
}

//Print representation of a node
void print_node(struct lpm_trie_node *node, struct lpm_trie *trie)
{
    printf("=============================\n");

    // int mem_index = node->mem_index;
    // printf("mem_index: %d\n", mem_index);

    int value = node->value;
    if(node->flags == 1) {
        printf("value: ---\n");
    } else {
        int val = node->value;
        printf("value: %d\n", val);
    }

    print_node_data(node, trie);

    printf("child0: ");
    if(node->has_l_child == 0)
        printf("---\n");
    else
        print_node_data(trie->node_mem_blocks + node->l_child, trie);
        printf("child0-index: %d\n", node->l_child);

    printf("child1: ");
    if(node->has_r_child == 0)
        printf("---\n");
    else
        print_node_data(trie->node_mem_blocks + node->r_child, trie);
        printf("child1-index: %d\n", node->r_child);

    printf("=============================\n");
}

struct lpm_trie_node *pointer_from_int(int index, struct lpm_trie *trie)
{
    return trie->node_mem_blocks + index;
}

void update_trie(uint8_t max_val)
{
    size_t plen = 0;
    uint8_t data_0 = 0;
    int value = 0;
    int trie_res = 0;
    struct lpm_trie_key *t_key = malloc(sizeof(struct lpm_trie_key));
    size_t max_entries = 256;
    struct lpm_trie *trie = lpm_trie_alloc(max_entries);

    struct timespec start, end;
    clock_gettime(CLOCK_REALTIME, &start);

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)) && value < max_val; j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            t_key->prefixlen = plen;
            memcpy(t_key->data, data, LPM_DATA_SIZE);
            value ++;
            trie_res = trie_update_elem(trie, t_key, value);
            if(trie_res)
                break;
            data_0 = 0;
        }
        if(trie_res)
            break;
    }

    clock_gettime(CLOCK_REALTIME, &end);
    uint64_t delta_us = (end.tv_sec - start.tv_sec) * 1000000 + (end.tv_nsec - start.tv_nsec) / 1000;

    if(trie_res) {
        printf("something went wrong after %d iterations\n", value);
    } else {
        printf("performed %d iterations of trie update in %ld microseconds\n", value, delta_us);
    }

    value = 0;
    data_0 = 0;
    clock_gettime(CLOCK_REALTIME, &start);

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)) && value < max_val; j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            t_key->prefixlen = plen;
            memcpy(t_key->data, data, LPM_DATA_SIZE);
            value ++;
            trie_res = trie_lookup_elem(trie, t_key);
            data_0 = 0;
        }
    }

    clock_gettime(CLOCK_REALTIME, &end);
    delta_us = (end.tv_sec - start.tv_sec) * 1000000 + (end.tv_nsec - start.tv_nsec) / 1000;

    printf("performed %d iterations of trie lookup in %ld microseconds\n", value, delta_us);

    value = 0;
    data_0 = 0;
    clock_gettime(CLOCK_REALTIME, &start);

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)) && value < max_val; j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            t_key->prefixlen = plen;
            memcpy(t_key->data, data, LPM_DATA_SIZE);
            value ++;
            trie_res = trie_delete_elem(trie, t_key);
            if(trie_res)
                break;
            data_0 = 0;
        }
        if(trie_res)
            break;
    }

    clock_gettime(CLOCK_REALTIME, &end);
    delta_us = (end.tv_sec - start.tv_sec) * 1000000 + (end.tv_nsec - start.tv_nsec) / 1000;

    if(trie_res) {
        printf("something went wrong after %d iterations: %d\n", value, trie_res);
    } else {
        printf("performed %d iterations of trie delete in %ld microseconds\n", value, delta_us);
    }

}

void update_tbl(uint8_t max_val)
{
    size_t plen = 0;
    uint8_t data_0 = 0;
    uint8_t value = 0;
    int tbl_res = 0;
    struct key *key = malloc(sizeof(struct key));
    size_t max_entries = 256;
    struct tbl *tbl = tbl_allocate(max_entries);

    struct timespec start, end;
    clock_gettime(CLOCK_REALTIME, &start);

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)) && value < max_val; j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            key->prefixlen = plen;
            memcpy(key->data, data, LPM_DATA_SIZE);
            value ++;
            tbl_res = tbl_update_elem(tbl, key, value);
            if(tbl_res)
                break;
            data_0 = 0;
        }
        if(tbl_res)
            break;
    }

    clock_gettime(CLOCK_REALTIME, &end);
    uint64_t delta_us = (end.tv_sec - start.tv_sec) * 1000000 + (end.tv_nsec - start.tv_nsec) / 1000;

    if(tbl_res) {
        printf("something went wrong after %d iterations\n", value);
    } else {
        printf("performed %d iterations of table update in %ld microseconds\n", value, delta_us);
    }

    value = 0;
    data_0 = 0;
    clock_gettime(CLOCK_REALTIME, &start);

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)) && value < max_val; j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            key->prefixlen = plen;
            memcpy(key->data, data, LPM_DATA_SIZE);
            value ++;
            tbl_res = tbl_lookup_elem(tbl, key);
            data_0 = 0;
        }
    }

    clock_gettime(CLOCK_REALTIME, &end);
    delta_us = (end.tv_sec - start.tv_sec) * 1000000 + (end.tv_nsec - start.tv_nsec) / 1000;

    printf("performed %d iterations of table lookup in %ld microseconds\n", value, delta_us);

    value = 0;
    data_0 = 0;
    clock_gettime(CLOCK_REALTIME, &start);

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)) && value < max_val; j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            key->prefixlen = plen;
            memcpy(key->data, data, LPM_DATA_SIZE);
            value ++;
            tbl_res = tbl_delete_elem(tbl, key);
            if(tbl_res)
                break;
            data_0 = 0;
        }
        if(tbl_res)
            break;
    }

    clock_gettime(CLOCK_REALTIME, &end);
    delta_us = (end.tv_sec - start.tv_sec) * 1000000 + (end.tv_nsec - start.tv_nsec) / 1000;

    if(tbl_res) {
        printf("something went wrong after %d iterations\n", value);
    } else {
        printf("performed %d iterations of table delete in %ld microseconds\n", value, delta_us);
    }
}

void trie_lookups(FILE *f)
{
    size_t plen = 0;
    uint8_t data_0 = 0;
    int value = 0;
    int trie_res = 0;
    int lookup_res = 0;
    uint64_t delta_us;
    struct lpm_trie_key *t_key = malloc(sizeof(struct lpm_trie_key));
    size_t max_entries = 256;
    struct lpm_trie *trie = lpm_trie_alloc(max_entries);

    struct timespec start, end;

    fprintf(f, "plen depth time\n");

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)); j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            t_key->prefixlen = plen;
            memcpy(t_key->data, data, LPM_DATA_SIZE);
            value ++;
            trie_res = trie_update_elem(trie, t_key, value);
            if(trie_res)
                break;
            data_0 = 0;
        }
        for(int j = 1; j <= 8; j++) {
            uint8_t data[4] = {0, 0, 0, 0};
            t_key->prefixlen = j;
            memcpy(t_key->data, data, LPM_DATA_SIZE);
            clock_gettime(CLOCK_REALTIME, &start);
            lookup_res = trie_lookup_elem(trie, t_key);
            clock_gettime(CLOCK_REALTIME, &end);
            delta_us = (end.tv_sec - start.tv_sec) * 1000000000 + (end.tv_nsec - start.tv_nsec);
            fprintf(f, "%d %d %ld\n", j, i, delta_us);
        }
        if(trie_res)
            break;
    }
}

void tbl_lookups(FILE *f)
{
    size_t plen = 0;
    uint8_t data_0 = 0;
    int value = 0;
    int trie_res = 0;
    int lookup_res = 0;
    uint64_t delta_us;
    struct key *key = malloc(sizeof(struct key));
    size_t max_entries = 256;
    struct tbl *tbl = tbl_allocate(max_entries);

    struct timespec start, end;

    fprintf(f, "plen n_entr time\n");

    for(uint8_t i = 1; i <= 8; i++) {
        plen = i;
        for(uint8_t j = 0; j < (1 << (i-1)); j++) {
            data_0 |= (j << (8-i));
            uint8_t data[4] = {data_0, 0, 0, 0};
            key->prefixlen = plen;
            memcpy(key->data, data, LPM_DATA_SIZE);
            value ++;
            trie_res = tbl_update_elem(tbl, key, value);
            data_0 = 0;
        }
        for(int j = 1; j <= 8; j++) {
            uint8_t data[4] = {0, 0, 0, 0};
            key->prefixlen = j;
            memcpy(key->data, data, LPM_DATA_SIZE);
            clock_gettime(CLOCK_REALTIME, &start);
            lookup_res = tbl_lookup_elem(tbl, key);
            clock_gettime(CLOCK_REALTIME, &end);
            delta_us = (end.tv_sec - start.tv_sec) * 1000000000 + (end.tv_nsec - start.tv_nsec);
            fprintf(f, "%d %d %ld\n", j, value, delta_us);
        }
    }
}

void main()
{
    update_trie(255);
    update_tbl(255);

    /*
    FILE *trie_f = fopen("trie_results.dat", "w");
    if (trie_f == NULL)
    {
        printf("Error opening file!\n");
        exit(1);
    }
    FILE *tbl_f = fopen("tbl_results.dat", "w");
    if (tbl_f == NULL)
    {
        printf("Error opening file!\n");
        exit(1);
    }
    trie_lookups(trie_f);
    tbl_lookups(tbl_f);
    */

}
