//@ #include <bitops.gh>
/*@
	inductive lpm_rule = rule(int, int, int); //ipv4, prefixlen, route
	//the values are kept without the flag
	inductive lpm_rule_24 = next_hop(int) | index_long(int) | empty;
	inductive lpm_rule_long = next_hop_l(int) | empty_l;

	inductive dir_24_8 = tables(list<lpm_rule_24>, list<lpm_rule_long>, int); //last is for tbl_long_index


	fixpoint lpm_rule init_rule(int ipv4, int prefixlen, int route){
		return rule(ipv4, prefixlen, route);
	}

	fixpoint int rule_ipv4(lpm_rule rule){
		switch(rule){
			case rule(ipv4, prefixlen, route): return ipv4;
		}
	}

	fixpoint int rule_prefixlen(lpm_rule rule){
		switch(rule){
			case rule(ipv4, prefixlen, route): return prefixlen;
		}
	}

	fixpoint int rule_route(lpm_rule rule){
		switch(rule){
			case rule(ipv4, prefixlen, route): return route;
		}
	}
	
	fixpoint int rule_24_get_value(lpm_rule_24 rule){
		switch(rule){
			case next_hop(next): return next;
			case index_long(index): return index;
			case empty: return -1;
		}
	}
	
// INDEX COMPUTING FUNCTIONS
	fixpoint int index24_from_ipv4(int ipv4){
		return ipv4 >> 8;
	}

	fixpoint int indexlong_from_ipv4(int ipv4, int index){
		return index * 256 + ipv4 & 0xFF;
	}

	fixpoint bool extract_flag(int entry){
		return ((entry >> 15) & 0x1) != 0;
	}
	
	fixpoint int set_flag(int entry){
		return entry | 0xFFFF;
	}
//Assuming that prefixlen <= 32
	fixpoint int compute_rule_size(int prefixlen){
		return prefixlen < 24 ? pow_nat(2, nat_of_int(24 - prefixlen)) : pow_nat(2, nat_of_int(32 - prefixlen));
	}
	
	fixpoint int mask_from_prefixlen(int prefixlen){
		return (0xFFFFFFFF >> prefixlen) << prefixlen;
	}

	fixpoint int compute_starting_index_24(lpm_rule rule){
		switch(rule){
			case rule(ipv4, prefixlen, route): return ipv4 & mask_from_prefixlen(prefixlen);
		}
	}
	
	fixpoint int compute_starting_index_long(lpm_rule rule, int base_index){
		switch(rule){
			case rule(ipv4, prefixlen, value): return base_index * 256 + (ipv4 & mask_from_prefixlen(prefixlen)) & 0xFF;
		}
	}
	
	fixpoint bool is_new_index_needed(lpm_rule_24 rule){
		switch(rule){
			case index_long(index): return false;
			case next_hop(next): return true;
			case empty: return true;
		}
	}
	
	fixpoint int option_get(option<int> o){
		switch(o){
		    case none: return -1;
		    case some(t): return t;
		}
	}

	
// LOOKUP FUNCTIONS
	fixpoint lpm_rule_24 lookup_tbl_24(int index, dir_24_8 dir){
		switch(dir){
		    case(tables(tbl_24, tbl_long, long_index)): return nth(index, tbl_24);
		}
	}

	fixpoint lpm_rule_long lookup_tbl_long(int index, dir_24_8 dir){
		switch(dir){
		    case(tables(tbl_24, tbl_long, long_index)): return nth(index, tbl_long);
		}
	}

	fixpoint option<int> lpm_dir_24_8_lookup(dir_24_8 dir, int ipv4){
		switch(dir){
			case tables(tbl_24, tbl_long, long_index): return
				switch(lookup_tbl_24(index24_from_ipv4(ipv4), dir)){
					case next_hop(next_24): return some(next_24);
					case index_long(index): return
						switch(lookup_tbl_long(indexlong_from_ipv4(ipv4, index), dir)){
							case next_hop_l(next_long): return some(next_long);
							case empty_l: return none;
						};
					case empty: return none;
				};
		}
	}

// ADD ROUTE FUNCTIONS


	fixpoint list<lpm_rule_24> update_n_tbl_24(list<lpm_rule_24> tbl_24, int start, int count, int value, bool is_long_index){
		switch(tbl_24){
			case nil: return nil;
			case cons(v, cs0): return 
				start == 0 ? 
					count == 0 ? 
						cons(v, cs0)
					:
						is_long_index ? 
							cons(index_long(value), update_n_tbl_24(cs0, 0, count-1, value, is_long_index))
						:
							cons(next_hop(value), update_n_tbl_24(cs0, 0, count-1, value, is_long_index))
				:
					update_n_tbl_24(cs0, start-1, count, value, is_long_index);		
		}
	}
	
	fixpoint list<lpm_rule_long> update_n_tbl_long(list<lpm_rule_long> tbl_long, int start, int count, int value){
		switch(tbl_long){
			case nil: return nil;
			case cons(v, cs0): return
				start == 0 ?
					count == 0 ?
						cons(v, cs0)
					:
						cons(next_hop_l(value), update_n_tbl_long(cs0, 0, count-1, value))
				:
					update_n_tbl_long(cs0, start-1, count, value);
		}
	}
	
	fixpoint list<lpm_rule_24> insert_route_24(list<lpm_rule_24> tbl_24, lpm_rule rule){
		switch(rule){
			case rule(ipv4, prefixlen, route): return update_n_tbl_24(tbl_24, compute_starting_index_24(rule), compute_rule_size(prefixlen), route, false);
		}
	}
	
	fixpoint list<lpm_rule_long> insert_route_long(list<lpm_rule_long> tbl_long, lpm_rule rule, int base_index){
		switch(rule){
			case rule(ipv4, prefixlen, route): return update_n_tbl_long(tbl_long, compute_starting_index_long(rule, base_index), compute_rule_size(prefixlen), route);
		}
	}

	fixpoint dir_24_8 insert_tbl_24(dir_24_8 dir, lpm_rule rule){
		switch(dir){
			case tables(tbl_24, tbl_long, long_index): return tables(insert_route_24(tbl_24, rule), tbl_long, long_index);
		}
	}

	fixpoint dir_24_8 insert_tbl_long(dir_24_8 dir, lpm_rule rule){
		switch(dir){
			case tables(tbl_24, tbl_long, long_index): return
				switch(rule){
					case rule(ipv4, prefixlen, route): return
						//Check whether a new index_long is needed 
						is_new_index_needed(lookup_tbl_24(index24_from_ipv4(ipv4), dir)) ? 
							//Check for available index, if not -> no change
							long_index == 256 ?
								tables(tbl_24, tbl_long, long_index)
							:
								//Update the value in tbl_24 and tbl_long
								tables(update_n_tbl_24(tbl_24, compute_starting_index_24(rule), 1, long_index, true), insert_route_long(tbl_long, rule, long_index), long_index + 1)
						:
							//No need to update the value in tbl_24, only in tlb_long
							tables(tbl_24, insert_route_long(tbl_long, rule, rule_24_get_value(lookup_tbl_24(index24_from_ipv4(ipv4), dir))), long_index);
						
				};		
		}
	}
	


	fixpoint dir_24_8 add_rule(dir_24_8 dir, lpm_rule rule){
		switch(rule){
			case rule(ipv4, prefixlen, route): return prefixlen < 24 ? insert_tbl_24(dir, rule) : insert_tbl_long(dir, rule);
		}
	}
@*/