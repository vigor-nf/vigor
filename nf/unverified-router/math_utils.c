
#include "math_utils.h"


int tail_rec_pow(int base, int exp, int acc);

/**
 * Fast exponentiation implementation for positive integers
 */
int fast_exp(int base, int exp){
	
	if(exp < 0){
		abort();
	}
	
	return tail_rec_pow(base, exp, 1);
}


int tail_rec_pow(int base, int exp, int acc){
	
		
	if(exp == 0){
		return acc;
	}
	
	else if(exp % 2 == 0){
		
		return tail_rec_pow(base*base, exp/2, acc);
	}
	else{
		return tail_rec_pow(base, exp -1, acc * base);
	}
		
		
}
