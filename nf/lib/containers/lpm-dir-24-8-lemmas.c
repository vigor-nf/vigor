//@ #include "lpm-dir-24-8-lemmas.gh"
//@ #include "lpm-dir-24-8.gh"

// 0x8000 is tbl24 flag mask
// 0x7FFF is tbl24 value mask
// 16777216 is tbl24 max entries
// 0xFFFF is 0xFFFF

/* @
  lemma void equal_int32_equal_Z(int x, Z yZ, int data, int mask,
                               Z dataZ, Z maskZ)
  requires x == int_of_Z(yZ) &*&
           0 <= x &*& x <= 0xFFFFFFFF &*&
           0 <= data &*& data <= 0xFFFFFFFF &*&
           0 <= mask &*& mask <= 0xFFFFFFFF &*&
           dataZ == Z_of_int(data, N32) &*&
           maskZ == Z_of_int(mask, N32) &*&
           int_of_Z(dataZ) == data &*&
           int_of_Z(maskZ) == mask &*&
           yZ == Z_and(dataZ, maskZ);
  ensures Z_of_int(x, N32) == yZ;
  {
    bitand_def(data, dataZ, mask, maskZ);
    bitand_limits(data, mask, N32);
    int masked_data = data & mask;
    Z_of_uintN(masked_data, N32);
  }
  @*/

/*@
  lemma void flag_mask_MSB_one()
    requires true;
    ensures extract_flag(0x8000) == true;
  {
    Z maskZ = Z_of_uintN(0x8000, N16);
    shiftright_def(0x8000, maskZ, nat_of_int(15));
    Z shifted = Z_shiftright(maskZ, nat_of_int(15));
    assert 1 == int_of_Z(shifted);
  }
  @*/

/*@
  lemma void flag_mask_or_x_begins_with_one(int x)
    requires 0 <= x &*& x <= 0xFFFF;
    ensures extract_flag(x | 0x8000) == true;
  {

    Z xZ = Z_of_uintN(x, N16);
    Z maskZ = Z_of_uintN(0x8000, N16);
    flag_mask_MSB_one();
    assert true == extract_flag(0x8000);
  
    Z res = Z_or(xZ, maskZ);
    bitor_def(x, xZ, 0x8000, maskZ);
    assert int_of_Z(res) == (x | 0x8000);
  
    shiftright_def(int_of_Z(res), res, nat_of_int(15));
    Z shifted = Z_shiftright(res, nat_of_int(15));
    assert 1 == int_of_Z(shifted);
  }
  @*/

/*@
  lemma void flag_mask_or_x_not_affect_15LSB(int x)
    requires 0 <= x &*& x <= 0x7FFF;
    ensures x == ((x | 0x8000) & 0x7FFF);
  {
    Z xZ = Z_of_uintN(x, N16);
    Z flagMask = Z_of_uintN(0x8000, N16);
    Z valueMask = Z_of_uintN(0x7FFF, N16);
  
    bitor_def(x, xZ, 0x8000, flagMask);
    Z orRes = Z_or(xZ, flagMask);
  
    bitand_def((x | 0x8000), orRes, 0x7FFF, valueMask);
  }
  @*/

/*@
  lemma void extract_value_is_value(int entry)
    requires 0 <= entry &*& entry <= 0x7FFF;
    ensures entry == extract_value(entry);
  {
    Z entryZ = Z_of_uintN(entry, N16);
    Z valuemask = Z_of_uintN(0x7FFF, N16);
    
    bitand_def(entry, entryZ, 0x7FFF, valuemask);
  }
  @*/

/*@  
  lemma void valid_next_hop24(int entry, option<pair<bool, Z> > mapped)
    requires entry != 0xFFFF &*& 0 <= entry &*& entry <= 0x7FFF &*&
             false == extract_flag(entry) &*&
             entry_24_mapping(entry) == mapped &*& mapped == some(?p) &*&
             p == pair(?b, ?v);
    ensures b == false &*& entry == int_of_Z(v);
  {
    assert b == false;
    Z entryZ = Z_of_uintN(entry, N16);
    extract_value_is_value(entry);
    assert mapped == some(pair(false, entryZ));
  }
  @*/

/*@
  lemma void valid_next_bucket_long(int entry,
                                    option<pair<bool, Z> > mapped)
    requires entry != 0xFFFF &*&
             true == extract_flag(entry) &*&
             true == valid_entry24(entry) &*&
             entry_24_mapping(entry) == mapped &*& mapped == some(?p) &*&
             p == pair(?b, ?v);
    ensures b == true &*& extract_value(entry) == int_of_Z(v);
  {
    assert b == true;
    Z entryZ = Z_of_uintN(extract_value(entry), N16);
    extract_value_is_value(extract_value(entry));
    assert mapped == some(pair(true, entryZ));
  }
  @*/
  
/*@  
  lemma void valid_next_hop_long(int entry, option<Z> mapped)
    requires entry != 0xFFFF &*& 0 <= entry &*& entry <= 0x7FFF &*&
             entry_long_mapping(entry) == mapped &*& mapped == some(?v);
    ensures entry == int_of_Z(v);
  {
    Z entryZ = Z_of_uintN(entry, N16);
    assert v == entryZ;
  }
  @*/

/*@
  lemma void long_index_extraction_equivalence(int entry,
                                               option<pair<bool, Z> > mapped)
    requires entry_24_mapping(entry) == mapped &*& entry != 0xFFFF &*&
             mapped == some(?p) &*& p == pair(true, ?z) &*&
             true == valid_entry24(entry) &*&
             true == extract_flag(entry);
    ensures (entry & 0xFF) == extract24_value(mapped);
  {
    //assert z == Z_of_int(extract_value(entry), N16);
    
    //assert snd(get_some(mapped)) == z;
    Z_of_uintN(extract_value(entry), N16);
    //assert z == extractedZ;
    //assert mapped == some(pair(true, extractedZ));
    //assert snd(get_some(mapped)) == extractedZ;
    //assert int_of_Z(extractedZ) == extract_value(entry);
    
    //Show ((entry & 0xFF) == (entry & 0x7FFF))
    Z entryZ = Z_of_uintN(entry, N16);
    Z maskFF = Z_of_uintN(0xFF, N8);
    Z mask7FFF = Z_of_uintN(0x7FFF, N16);
    
    bitand_def(entry, entryZ, 0xFF, maskFF);
    bitand_def(entry, entryZ, 0x7FFF, mask7FFF);
  }
  @*/

/*@ 
  lemma void long_index_computing_equivalence_on_prefixlen32(int ipv4,
                                                             int base_index)
    requires 0 <= ipv4 &*& ipv4 <= 0xffffffff;
    ensures compute_starting_index_long(init_rule(ipv4, 32, 0), base_index) ==
            indexlong_from_ipv4(Z_of_int(ipv4, N32), base_index);
  {
    Z ipv4Z = Z_of_uintN(ipv4, N32);
    Z mask32 = Z_of_uintN(0xFFFFFFFF, N32);
    assert mask32 == mask32_from_prefixlen(32);
    
    bitand_def(ipv4, ipv4Z, 0xFFFFFFFF, mask32);
  }
  @*/

/*@
  lemma void value24_extraction_equivalence(int entry,
                                            option<pair<bool, Z> > mapped)
    requires 0 <= extract_value(entry) &*&
             extract_value(entry) <= 0xFF &*&
             extract_flag(entry) == true &*&
             valid_entry24(entry) == true &*&
             entry_24_mapping(entry) == mapped &*&
             mapped == some(?p) &*&
             p == pair(true, Z_of_int(extract_value(entry), N16));
    ensures extract_value(entry) == extract24_value(mapped);
  {
    assert 0 <= extract_value(entry);
    assert extract_value(entry) < 256;
    
    Z entry_valZ = Z_of_uintN(extract_value(entry), N16);
    
    option<pair<bool, Z> > mapped_entry =
                           some(pair(extract_flag(entry),
                                     entry_valZ));
    
    assert mapped == mapped_entry;
  }
  @*/

/*@
  lemma void first_index_depends_on_prefixlen(lpm_rule new_rule,
                                              int base_index,
                                              int prefixlen)
    requires 0 <= base_index &*& base_index < 256 &*& 24 <= prefixlen &*&
             prefixlen <= 32 &*& new_rule == rule(?ipv4, prefixlen, ?value) &*&
             0 <= int_of_Z(ipv4) &*& int_of_Z(ipv4) <= 0xFFFFFFFF;
    ensures compute_starting_index_long(new_rule, base_index) <=
            (16777216) - compute_rule_size(prefixlen);
  {
    bitand_def(int_of_Z(ipv4), ipv4, int_of_Z(mask32_from_prefixlen(prefixlen)),
               mask32_from_prefixlen(prefixlen));
    bitand_limits(int_of_Z(ipv4),
                  int_of_Z(mask32_from_prefixlen(prefixlen)), N32);
    
    Z andRes = Z_and(ipv4, mask32_from_prefixlen(prefixlen));
    
    Z maskZ = Z_of_uintN(0xFF, N8);
    
    bitand_def(int_of_Z(andRes), andRes, 0xFF, maskZ);
    bitand_limits(int_of_Z(andRes), 0xFF, N8);
    
  }
  @*/
