
#include "parse_utils.h"
#define MAX_OCTET_VALUE 255

/**
 * Transform a small string in an integer between 0-255
 */
uint8_t get_number(const char * s, size_t size){
	
	int buffer = 0;
	
	for(size_t i = 0; i < size; i++){
		
		if(!isdigit(s[i])){
			printf("Error while parsing routes, invalid ip !\n"); 
			exit(-1);
		}

		buffer += (s[i] - '0') * fast_exp(10,size -i -1);
		
	}
	if(buffer > MAX_OCTET_VALUE){
		printf("Error while parsing routes, invalid ip !\n"); 
		exit(-1);
	}
	
	return (uint8_t)buffer;
}

/**
 * Transform a string that represents an ip address in a list of integers between 0-255
 */
uint8_t * parse_ip(const char * ip, size_t size){

	if(ip == NULL){
		return NULL;
	}
	
	uint8_t * res = calloc(IPV4_IP_SIZE, sizeof(uint8_t));
	
	if(! res){
		return NULL;
	}
	
	size_t count = 0;
	size_t j = 0;
		
	for(size_t i = 0; i < size; ++i){
		
		if(ip[i] == '.'){
			char * octet = take(i - count, count, ip, size);
			res[j] = get_number(octet, count);
			
			count = 0;
			j++;
			free(octet);
		}
		else if(i == size -1){
			++count;
			char * octet = take(i - count +1, count, ip, size);
			res[j] = get_number(octet, count);
			free(octet);
		}
		else{
			count++;
		}
	}
	
	return res;
	
}

/**
 * Takes n elements of a string of size = length starting at index = starting
 */
char * take(size_t starting, size_t n, const char * s, size_t length){
	
	if(n + starting > length){
		
		return NULL;
	}
	
	char * res = calloc(n, sizeof(char));
	if(!res){
		return NULL;
	}
	
	for(size_t i = 0; i < n; ++i){
		
		res[i] = s[i + starting];
	}

	
	return res;
}


