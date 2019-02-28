#include "dir-24-8-basic.h"
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

void print_tbl_24_entry(struct tbl *tbl, size_t index)
{
    uint16_t tbl_24_entry = tbl->tbl_24[index];
    int flag = (tbl_24_entry & TBL_24_FLAG_MASK) >> 15;
    int prefixlen = (tbl_24_entry & TBL_24_PLEN_MASK) >> 8;
    int value = tbl_24_entry & TBL_24_VAL_MASK;

    printf("Printing tbl_24 entry at: %ld\n", index);
    printf("========== tbl_24 entry ==========\n");
    printf("flag: %d\n", flag);
    printf("prefix length: %d\n", prefixlen);
    printf("value: %d\n", value);
    printf("==================================\n");
}

void print_tbl_long_entry(struct tbl *tbl, size_t index){
    uint16_t tbl_long_entry = tbl->tbl_long[index];
    int prefixlen = (tbl_long_entry & TBL_LONG_PLEN_MASK) >> 8;
    int value = tbl_long_entry & TBL_LONG_VAL_MASK;

    printf("Printing tbl_long entry at: %ld\n", index);
    printf("========= tbl_long entry =========\n");
    printf("prefix length: %d\n", prefixlen);
    printf("value: %d\n", value);
    printf("==================================\n");
}

struct key *allocate_key(uint8_t *data, uint8_t prefixlen)
{
    struct key *key = (struct key *) malloc(sizeof(struct key));
    if(!key){
        return NULL;
    }

    memcpy(key->data, data, 4);
    key->prefixlen = prefixlen;

    return key;
}

int test_update_elem()
{
    int res;
    struct tbl *tbl = tbl_allocate(256);
    if(!tbl)
        return -1;
    uint16_t *tbl_24 = tbl->tbl_24;

    uint8_t data_1[4] = {10, 54, 0, 0};
    struct key *key_1 = allocate_key(data_1, 16);
    if(!key_1){
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_2[4] = {10, 54, 34, 192};
    struct key *key_2 = allocate_key(data_2, 26);
    if(!key_2){
        free(key_1);
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_3[4] = {10, 54, 34, 0};
    struct key *key_3 = allocate_key(data_3, 24);
    if(!key_3){
        free(key_1);
        free(key_2);
        tbl_free(tbl);
        return -1;
    }

    printf("##### Inserting first entry #####\n");
    res = tbl_update_elem(tbl, key_1, 10);
    if(res)
        goto out;
    printf("##### Inserted first entry #####\n");

    size_t index = tbl_24_extract_first_index(key_1->data);
    print_tbl_24_entry(tbl, index);

    index = tbl_24_extract_last_index(key_1);
    print_tbl_24_entry(tbl, index);

    printf("##### Inserting second entry #####\n");
    res = tbl_update_elem(tbl, key_2, 12);
    if(res)
        goto out;
    printf("##### Inserted second entry #####\n");

    index = tbl_24_extract_first_index(key_2->data);
    print_tbl_24_entry(tbl, index);
    index = 191;
    print_tbl_long_entry(tbl, index);
    index = 192;
    print_tbl_long_entry(tbl, index);
    index = 255;
    print_tbl_long_entry(tbl, index);

    printf("##### Inserting third entry #####\n");
    res = tbl_update_elem(tbl, key_3, 11);
    if(res)
        goto out;
    printf("##### Inserted third key #####\n");

    index = tbl_24_extract_first_index(key_3->data);
    print_tbl_24_entry(tbl, index);
    index = 0;
    print_tbl_long_entry(tbl, index);
    index = 191;
    print_tbl_long_entry(tbl, index);
    index = 192;
    print_tbl_long_entry(tbl, index);

out:
    tbl_free(tbl);
    free(key_3);
    free(key_2);
    free(key_1);
    return res;
}

int test_delete_elem()
{
    int res;
    struct tbl *tbl = tbl_allocate(256);
    if(!tbl)
        return -1;

    uint16_t *tbl_24 = tbl->tbl_24;
    uint16_t *tbl_long = tbl->tbl_long;
    if(!tbl_24 || !tbl_long){
        free(tbl);
        return -1;
    }

    uint8_t data_1[4] = {10, 54, 0, 0};
    struct key *key_1 = allocate_key(data_1, 16);
    if(!key_1){
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_2[4] = {10, 54, 34, 192};
    struct key *key_2 = allocate_key(data_2, 26);
    if(!key_2){
        free(key_1);
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_3[4] = {10, 54, 34, 0};
    struct key *key_3 = allocate_key(data_3, 24);
    if(!key_3){
        free(key_1);
        free(key_2);
        tbl_free(tbl);
        return -1;
    }

    //Fill table manually, the update function is not tested here
    uint8_t val_1 = 10;
    uint8_t val_2 = 12;
    uint8_t val_3 = 11;

    uint16_t tbl_24_entry_1 = val_1;
    tbl_24_entry_1 = tbl_24_entry_put_plen(tbl_24_entry_1, key_1->prefixlen);
    size_t tbl_24_first_1 = tbl_24_extract_first_index(key_1->data);
    size_t tbl_24_last_1 = tbl_24_extract_last_index(key_1);

    uint16_t tbl_24_entry_2 = 0;
    tbl_24_entry_2 = tbl_24_entry_put_plen(tbl_24_entry_2, key_2->prefixlen);
    tbl_24_entry_2 = tbl_24_entry_set_flag(tbl_24_entry_2);
    size_t tbl_24_first_2 = tbl_24_extract_first_index(key_2->data);
    uint16_t tbl_long_entry_2 = val_2;
    tbl_long_entry_2 = tbl_long_entry_put_plen(tbl_long_entry_2,
                                                key_2->prefixlen);

    uint16_t tbl_long_entry_3 = val_3;
    tbl_long_entry_3 = tbl_long_entry_put_plen(tbl_long_entry_3,
                                                key_3->prefixlen);

    for(int i = tbl_24_first_1; i <= tbl_24_last_1; i ++){
        tbl_24[i] = tbl_24_entry_1;
    }

    tbl_24[tbl_24_first_2] = tbl_24_entry_2;

    for(int i = 0; i <= 191; i++){
        tbl_long[i] = tbl_long_entry_3;
    }

    for(int i = 192; i <= 255; i++){
        tbl_long[i] = tbl_long_entry_2;
    }

    //Table is filled, we can remove entries
    printf("##### Deleting first entry #####\n");
    res = tbl_delete_elem(tbl, key_1);
    if(res)
        goto out;
    printf("##### Deleted first entry #####\n");
    print_tbl_24_entry(tbl, tbl_24_first_1);
    print_tbl_24_entry(tbl, tbl_24_first_2);
    print_tbl_24_entry(tbl, tbl_24_last_1);

    printf("##### Deleting second entry #####\n");
    res = tbl_delete_elem(tbl, key_2);
    if(res)
        goto out;
    printf("##### Deleted second entry #####\n");
    print_tbl_24_entry(tbl, tbl_24_first_2);
    print_tbl_long_entry(tbl, 192);
    print_tbl_long_entry(tbl, 255);

    printf("##### Deleting third entry #####\n");
    res = tbl_delete_elem(tbl, key_3);
    if(res)
        goto out;
    printf("##### Deleted third entry #####\n");
    print_tbl_24_entry(tbl, tbl_24_first_2);
    print_tbl_long_entry(tbl, 0);
    print_tbl_long_entry(tbl, 255);

out:
    tbl_free(tbl);
    free(key_1);
    free(key_2);
    free(key_3);
    return 0;
}

int test_lookup_elem()
{
    int res;
    struct tbl *tbl = tbl_allocate(256);
    if(!tbl)
        return -1;

    uint16_t *tbl_24 = tbl->tbl_24;
    uint16_t *tbl_long = tbl->tbl_long;
    if(!tbl_24 || !tbl_long){
        free(tbl);
        return -1;
    }

    uint8_t data_1[4] = {10, 54, 0, 0};
    struct key *key_1 = allocate_key(data_1, 16);
    if(!key_1){
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_2[4] = {10, 54, 34, 192};
    struct key *key_2 = allocate_key(data_2, 26);
    if(!key_2){
        free(key_1);
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_3[4] = {10, 54, 34, 0};
    struct key *key_3 = allocate_key(data_3, 24);
    if(!key_3){
        free(key_1);
        free(key_2);
        tbl_free(tbl);
        return -1;
    }

    //Fill table manually, the update function is not tested here
    uint8_t val_1 = 10;
    uint8_t val_2 = 12;
    uint8_t val_3 = 11;

    uint16_t tbl_24_entry_1 = val_1;
    tbl_24_entry_1 = tbl_24_entry_put_plen(tbl_24_entry_1, key_1->prefixlen);
    size_t tbl_24_first_1 = tbl_24_extract_first_index(key_1->data);
    size_t tbl_24_last_1 = tbl_24_extract_last_index(key_1);

    uint16_t tbl_24_entry_2 = 0;
    tbl_24_entry_2 = tbl_24_entry_put_plen(tbl_24_entry_2, key_2->prefixlen);
    tbl_24_entry_2 = tbl_24_entry_set_flag(tbl_24_entry_2);
    size_t tbl_24_first_2 = tbl_24_extract_first_index(key_2->data);
    uint16_t tbl_long_entry_2 = val_2;
    tbl_long_entry_2 = tbl_long_entry_put_plen(tbl_long_entry_2,
                                                key_2->prefixlen);

    uint16_t tbl_long_entry_3 = val_3;
    tbl_long_entry_3 = tbl_long_entry_put_plen(tbl_long_entry_3,
                                                key_3->prefixlen);

    for(int i = tbl_24_first_1; i <= tbl_24_last_1; i ++){
        tbl_24[i] = tbl_24_entry_1;
    }

    tbl_24[tbl_24_first_2] = tbl_24_entry_2;

    for(int i = 0; i <= 191; i++){
        tbl_long[i] = tbl_long_entry_3;
    }

    for(int i = 192; i <= 255; i++){
        tbl_long[i] = tbl_long_entry_2;
    }

    uint8_t data_4[4] = {10, 54, 1, 0};//lookup->10
    struct key *key_4 = allocate_key(data_4, 32);
    if(!key_4){
        free(key_1);
        free(key_2);
        free(key_3);
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_5[4] = {10, 54, 34, 1};//lookup->12
    struct key *key_5 = allocate_key(data_5, 32);
    if(!key_5){
        free(key_1);
        free(key_2);
        free(key_3);
        free(key_4);
        tbl_free(tbl);
        return -1;
    }

    uint8_t data_6[4] = {10, 54, 34, 193};//lookup->11
    struct key *key_6 = allocate_key(data_6, 32);
    if(!key_5){
        free(key_1);
        free(key_2);
        free(key_3);
        free(key_4);
        free(key_5);
        tbl_free(tbl);
        return -1;
    }

    //Table is filled, we can lookup entries
    printf("##### looking up first key #####\n");
    res = tbl_lookup_elem(tbl, key_4);// 10
    if(res < 0)
        goto out;
    printf("value found: %d\n", res);
    printf("##### looked up first key #####\n");

    printf("##### looking up second key #####\n");
    res = tbl_lookup_elem(tbl, key_5);// 12
    if(res < 0)
        goto out;
    printf("value found: %d\n", res);
    printf("##### looked up second key #####\n");

    printf("##### looking up third key #####\n");
    res = tbl_lookup_elem(tbl, key_6);// 11
    if(res < 0)
        goto out;
    printf("value found: %d\n", res);
    printf("##### looked up third key #####\n");
out:
    tbl_free(tbl);
    free(key_1);
    free(key_2);
    free(key_3);
    free(key_4);
    free(key_5);
    free(key_6);
    return 0;
}

int main()
{
    printf("########## Beginning of test_update_elem ##########\n");
    int res = test_update_elem();
    if(res)
        printf("Something went wrong: %d\n", res);
    printf("########## End of test_update_elem ##########\n");

    printf("########## Beginning of test_delete_elem ##########\n");
    res = test_delete_elem();
    if(res)
        printf("Something went wrong: %d\n", res);
    printf("########## End of test_delete_elem ##########\n");

    printf("########## Beginning of test_lookup_elem ##########\n");
    res = test_lookup_elem();
    if(res)
        printf("Something went wrong: %d\n", res);
    printf("########## End of test_lookup_elem ##########\n");
}
