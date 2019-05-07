//@ #include "mod_pow2.gh"

unsigned loop(unsigned k, unsigned capacity)
//@     requires 0 < capacity &*& capacity < INT_MAX &*& is_pow2(capacity, N31) != none;
//@     ensures 0 <= result &*& result < capacity &*& result == loop_fp(k, capacity);
{
    //@ nat m = is_pow2_some(capacity, N31);
    //@ int m_int = int_of_nat(m);
    //@ assert (m_int < 32);
    //@ assert (capacity == pow2(m));
    //@ assert (capacity < pow2(N32));
    //@ assert (k < pow2(N32));

    //@ list<bool> k_bits = snd(bits_of_int(k, N32));
    //@ list<bool> capacity_bits = snd(bits_of_int(capacity - 1, N32));
    //@ list<bool> k_and_capacity_bits = snd(bits_of_int(k & (capacity - 1), N32));

    // k & (capacity - 1)
    //@ bits_of_int_pow2_mask(N32, m);

    //@ bitand_limits(k, capacity - 1, N32);
    //@ bits_of_int_remainder(k & (capacity - 1), N32);
    //@ bits_of_int_remainder(k, N32);
    //@ bits_of_int_remainder(capacity - 1, N32);
    //@ bits_of_int_apply_mask(k, k_bits, capacity - 1, capacity_bits, m_int, N32);
    //@ assert (take(m_int, k_and_capacity_bits) == take(m_int, k_bits));
    //@ assert (true == forall(drop(m_int, k_and_capacity_bits), (eq)(false)));
    
    // k % capacity

    //@ list<bool> r_bits = gen_r_bits(k_bits, m_int);
    //@ gen_r_bits_works(k_bits, m_int);
    
    //@ bits_of_int_split(k, N32, m_int, k_bits, k_and_capacity_bits, r_bits);
    //@ assert (k == int_of_bits(0, k_and_capacity_bits) + int_of_bits(0, r_bits));
    
    //@ int_of_bits_lt(k_and_capacity_bits, m);
    //@ int_of_bits_mul(r_bits, m);
    //@ assert (int_of_bits(0, k_and_capacity_bits) < capacity);
    //@ assert (int_of_bits(0, r_bits) % capacity == 0);
    //@ div_rem_nonneg_wrap(int_of_bits(0, r_bits), capacity);
    //@ assert (int_of_bits(0, r_bits) == int_of_bits(0, r_bits)/capacity * capacity);
    //@ mod_reduce(int_of_bits(0, k_and_capacity_bits), capacity, int_of_bits(0, r_bits)/capacity);
    //@ assert (k == int_of_bits(0, k_and_capacity_bits) + int_of_bits(0, r_bits)/capacity * capacity);
    //@ assert (k % capacity == int_of_bits(0, k_and_capacity_bits) % capacity);
    //@ mod_bijection(int_of_bits(0, k_and_capacity_bits), capacity);
    //@ assert (k % capacity == int_of_bits(0, k_and_capacity_bits));

    // Proof of equality

    //@ int_of_bits_of_int(k & (capacity - 1), N32);
    
    //@ assert ((k % capacity) == (k & (capacity - 1)) );
    //@ loop_fp_pop(k, capacity);
    //@ assert ((k % capacity) == loop_fp(k, capacity));

  return k & (capacity - 1);
}