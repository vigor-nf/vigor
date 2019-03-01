#include <ctype.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <math.h>

#define IPV4_IP_SIZE 4

/**
 * Transform a small string in an integer between 0-255
 */
uint8_t get_number(const char * s, size_t size);


/**
 * Transform a string that represents an ip address in a list of integers between 0-255
 */
uint8_t * parse_ip(char * ip, size_t size);


/**
 * Takes n elements of a string of size = length starting at index = starting
 */
char * take(size_t starting, size_t n, const char * s, size_t length);
