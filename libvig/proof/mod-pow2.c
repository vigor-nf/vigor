//@ #include <bitops.gh>
//@ #include <nat.gh>
//@ #include <listex.gh>

//@ #include "mod-pow2.gh"
//@ #include "bitopsutils.gh"
//@ #include "stdex.gh"
//@ #include "listexex.gh"

/*@

    lemma void mod_mul(int a, int b, int k)
        requires    0 <= a &*& 0 < b &*& 0 < k &*& a % b == 0;
        ensures     ((k*a) % (k*b)) == 0;
    {
        div_rem_nonneg(a, b);
        mul_nonzero(b, k);
        mod_rotate_mul(a/b, b*k);
    }

    // ------------- k & (capacity - 1)  -------------

    lemma void bits_of_int_apply_mask(int k, list<bool> k_bits, int mask, list<bool> mask_bits, int m, nat n) 
        requires 
            bits_of_int(k, n) == pair(0, k_bits) &*& 
            bits_of_int(mask, n) == pair(0, mask_bits) &*& 
            true == forall(take(m, mask_bits), (eq)(true)) &*& 
            true == forall(drop(m, mask_bits), (eq)(false)) &*& 
            0 <= k &*& k < pow_nat(2, n) &*& 0 <= mask &*& mask < pow_nat(2, n) &*& 
            0 <= m &*& m < int_of_nat(n); 
        ensures 
            take(m, snd(bits_of_int(k & mask, n))) == take(m, k_bits) &*& 
            true == forall(drop(m, snd(bits_of_int(k & mask, n))), (eq)(false));
    {
        bits_of_int_and_def(k, k_bits, mask, mask_bits, n);
        assert ( (k & mask) == int_of_bits(0, bits_of_int_and(k_bits, mask_bits)) );

        length_bits_of_int(k, n);
        length_bits_of_int(mask, n);
        bits_of_int_and_mask(k_bits, mask_bits, m);

        length_bits_of_int_and(k_bits, mask_bits);
        bits_of_int_of_bits(bits_of_int_and(k_bits, mask_bits), n);
    }

    // ------------- k % capacity -------------

    lemma void bits_of_int_split(int k, nat n, int m, list<bool> k_bits, list<bool> l_bits, list<bool> r_bits) 
        requires 
            snd(bits_of_int(k, n)) == k_bits &*& 
            0 <= k &*& k < pow_nat(2, n) &*& 
            0 <= m &*& m < int_of_nat(n) &*& 
            length(l_bits) == length(r_bits) &*& length(r_bits) == length(k_bits) &*& 
            take(m, k_bits) == take(m, l_bits) &*& true == forall(drop(m, l_bits), (eq)(false)) &*& 
            drop(m, k_bits) == drop(m, r_bits) &*& true == forall(take(m, r_bits), (eq)(false));
        ensures
            k == int_of_bits(0, l_bits) + int_of_bits(0, r_bits);
    {
        switch (n) {
            case zero:
            case succ(n_pred):
                switch(k_bits) {
                    case nil:
                    case cons(k0, ks0):
                        switch(l_bits) {
                            case nil:
                            case cons(l0, ls0):
                                switch(r_bits) {
                                    case nil:
                                    case cons(r0, rs0):
                                        if (m > 0) {
                                            div_lt(k, pow_nat(2, n_pred), 2);
                                            div_exact(pow_nat(2, n_pred), 2);
                                            assert(k/2 < pow_nat(2, n_pred));
                                            div_ge(0, k, 2);
                                            division_round_to_zero(0, 2);
                                            bits_of_int_split(k/2, n_pred, m-1, ks0, ls0, rs0);

                                            assert (r0 == false);
                                            assert (int_of_bits(0, r_bits) == 2 * int_of_bits(0, rs0)); 
                                            div_rem_nonneg(k, 2); 
                                        } else { 
                                            assert (true == forall(l_bits, (eq)(false))); assert (k_bits == r_bits);
                                            int_of_bits_zero(l_bits);
                                            bits_of_int_remainder(k, n);
                                            int_of_bits_of_int(k, n);
                                        }
                                }
                        }
                }
        }
    }
    
    lemma void int_of_bits_mul(list<bool> bits, nat m)
        requires
            0 <= int_of_nat(m) &*& int_of_nat(m) < length(bits) &*&
            true == forall(take(int_of_nat(m), bits), (eq)(false));
        ensures
            int_of_bits(0, bits) % pow_nat(2, m) == 0;
    {
        switch(bits) {
            case nil:
            case cons(b, bs0):
                switch(m) {
                    case zero:
                        int_of_bits_bounds(bits);
                        assert (pow_nat(2, zero) == 1);
                        div_mod_gt_0(int_of_bits(0, bits) % pow_nat(2, m), int_of_bits(0, bits), pow_nat(2, m)); 
                    case succ(m_pred): 
                        int_of_bits_mul(bs0, m_pred);
                        assert (b == false);
                        assert (int_of_bits(0, bits) == 2 * int_of_bits(0, bs0)); 
                        assert (pow_nat(2, m) == 2 * pow_nat(2, m_pred)); 
                        assert (int_of_bits(0, bs0) % pow_nat(2, m_pred) == 0);

                        int_of_bits_bounds(bs0);
                        pow_nat_bounds(2, m_pred);
                        mod_mul(int_of_bits(0, bs0), pow_nat(2, m_pred), 2);
                }
        }
    }

    fixpoint list<bool> gen_r_bits(list<bool> k_bits, int m) {
        switch(k_bits) {
            case nil: return nil;
            case cons(k0, ks0): return ((m > 0) ? cons(false, gen_r_bits(ks0, m - 1)) : cons(k0, gen_r_bits(ks0, 0)));
        }
    }

    lemma void gen_r_bits_works(list<bool> k_bits, int m)
        requires    
            0 <= m &*& m <= length(k_bits);
        ensures     
            drop(m, gen_r_bits(k_bits, m)) == drop(m, k_bits) &*&
            true == forall(take(m, gen_r_bits(k_bits, m)), (eq)(false));
    {
        switch(k_bits) {
            case nil:
            case cons(k0, ks0): 
                if (m > 0) {
                    gen_r_bits_works(ks0,  m - 1);                    
                } else {
                    gen_r_bits_works(ks0, 0);
                }
        }
    }

    // This lemma is in fact, just a concluding part of mod_bitand_equiv,
    // but Z3 hangs if it is inlined.
    lemma void mod_bitand_equiv_conclude(int k, int capacity, list<bool> r_bits,
                                         list<bool> k_and_capacity_bits)
        requires k % capacity == loop_fp(k, capacity) &*&
                 0 <= int_of_bits(0, r_bits) &*& 0 < capacity &*&
                 int_of_bits(0, r_bits) % capacity == 0 &*&
                 0 <= int_of_bits(0, k_and_capacity_bits) &*&
                 (k == int_of_bits(0, k_and_capacity_bits) + int_of_bits(0, r_bits)) &*&
                 (int_of_bits(0, k_and_capacity_bits) < capacity) &*&
                 int_of_bits(0, k_and_capacity_bits) == (k & (capacity - 1)) ;
        ensures (k % capacity) == (k & (capacity - 1));
    {
        div_rem_nonneg(int_of_bits(0, r_bits), capacity);
        mod_reduce(int_of_bits(0, k_and_capacity_bits), capacity, int_of_bits(0, r_bits)/capacity);
        mod_bijection(int_of_bits(0, k_and_capacity_bits), capacity);
    }

    lemma void mod_bitand_equiv(int k, int capacity, nat m)
        requires    0 <= k &*& k < pow_nat(2, N32) &*& 0 < capacity &*& capacity < INT_MAX &*& capacity == pow_nat(2, m) &*& int_of_nat(m) < 32;
        ensures     (k % capacity) == (k & (capacity - 1)) &*& (k % capacity) == loop_fp(k, capacity);
    {
        int m_int = int_of_nat(m);
        list<bool> k_bits = snd(bits_of_int(k, N32));
        list<bool> capacity_bits = snd(bits_of_int(capacity - 1, N32));
        list<bool> k_and_capacity_bits = snd(bits_of_int(k & (capacity - 1), N32));

        // k & (capacity - 1)
        bits_of_int_pow2_mask(N32, m);

        bitand_limits(k, capacity - 1, N32);
        bits_of_int_remainder(k & (capacity - 1), N32);
        bits_of_int_remainder(k, N32);
        bits_of_int_remainder(capacity - 1, N32);
        bits_of_int_apply_mask(k, k_bits, capacity - 1, capacity_bits, m_int, N32);
        assert (take(m_int, k_and_capacity_bits) == take(m_int, k_bits));
        assert (true == forall(drop(m_int, k_and_capacity_bits), (eq)(false)));
        
        // k % capacity
        list<bool> r_bits = gen_r_bits(k_bits, m_int);
        gen_r_bits_works(k_bits, m_int);
        
        bits_of_int_split(k, N32, m_int, k_bits, k_and_capacity_bits, r_bits);
        assert (k == int_of_bits(0, k_and_capacity_bits) + int_of_bits(0, r_bits));
        
        int_of_bits_lt(k_and_capacity_bits, m);
        int_of_bits_mul(r_bits, m);
        assert (int_of_bits(0, k_and_capacity_bits) < capacity);
        assert (int_of_bits(0, r_bits) % capacity == 0);

        mod_bijection(int_of_bits(0, k_and_capacity_bits), capacity);

        // Proof of equality
        int_of_bits_of_int(k & (capacity - 1), N32);
        loop_fp_pop(k, capacity);

        assert (k % capacity) == loop_fp(k, capacity);
        mod_bitand_equiv_conclude(k, capacity, r_bits, k_and_capacity_bits);
    }

    // ------------- proof for check_pow2_valid -------------

    lemma nat is_pow2_some(int x, nat m)
        requires    is_pow2(x, m) != none;
        ensures     x == pow2(result) &*& int_of_nat(result) <= int_of_nat(m);
    {
        switch(m) {
            case zero:
                assert (x == pow2(zero));
                return zero;
            case succ(m_pred):
                if (x == pow2(m)) {
                    return m;
                } else {
                    return is_pow2_some(x, m_pred);
                }
        }
    }

    lemma void some_is_pow2(int x, nat n, nat m)
        requires    x == pow_nat(2, n) &*& int_of_nat(n) <= int_of_nat(m);
        ensures     is_pow2(x, m) == some(n);
    {
        switch(m) {
            case zero:
                assert (int_of_nat(n) == int_of_nat(m));
                nat_of_int_of_nat(n);
                nat_of_int_of_nat(m);
                assert (x == pow2(zero));
            case succ(m_pred): 
                if (int_of_nat(n) < int_of_nat(m)) {
                    pow_nat_gt(2, n, m);
                    some_is_pow2(x, n, m_pred);
                } else {
                    assert (int_of_nat(n) == int_of_nat(m));
                    nat_of_int_of_nat(n);
                    nat_of_int_of_nat(m);
                    assert (n == m);
                }
        }
    }

    lemma_auto(index_of(x, xs)) void index_of_bound<t>(t x, list<t> xs)
        requires    true;
        ensures     0 <= index_of(x, xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): index_of_bound(x, xs0);
        }
    }

    lemma void count_drop_index_of<t>(t x, list<t> xs)
       requires     0 < count(xs, (eq)(x));
       ensures      count(drop(index_of(x, xs) + 1, xs), (eq)(x)) == count(xs, (eq)(x)) - 1;
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (x0 == x) {
                    assert(index_of(x, xs) == 0);
                    assert (drop(1, xs) == xs0);
                    count_append(cons(x0, nil), xs0, (eq)(x));
                } else {
                    count_drop_index_of(x, xs0);
                    assert (count(xs, (eq)(x)) == count(xs0, (eq)(x)));
                    assert (index_of(x, xs0) == index_of(x, xs) - 1);
                    drop_append(index_of(x, xs) + 1, cons(x0, nil), xs0);
                    assert (drop(index_of(x, xs) + 1, xs) == drop(index_of(x, xs0) + 1, xs0) );
                }
        }
    }

    fixpoint int count_bits(list<bool> xs) {
        return count(xs, (eq)(true));
    }

    lemma void count_nonzero_to_mem<t>(t x, list<t> xs)
        requires    0 < count(xs, (eq)(x));
        ensures     true == mem(x, xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): 
                if (x0 != x) {
                    count_append(cons(x0, nil), xs0, (eq)(x));
                    count_nonnegative(cons(x0, nil), (eq)(x));
                    count_nonnegative(xs0, (eq)(x));
                    count_nonzero_to_mem(x, xs0);
                }
        }
    }

    lemma void int_of_bits_count_zero(list<bool> bits)
        requires    count_bits(bits) == 0;
        ensures     int_of_bits(0, bits) == 0;
    {
        switch(bits) {
            case nil:
            case cons(b, bs0): 
                count_append(cons(b, nil), bs0, (eq)(true));
                count_nonnegative(cons(b, nil), (eq)(true));
                count_nonnegative(bs0, (eq)(true));
                int_of_bits_count_zero(bs0);
        }
    }

    lemma void int_of_bits_count_nonzero(list<bool> bits)
        requires    0 < count_bits(bits);
        ensures     0 < int_of_bits(0, bits);
    {
        switch(bits) {
            case nil:
            case cons(b, bs0):
                if (b && count_bits(bits) == 1) {
                    assert (count_bits(bs0) == 0);
                    int_of_bits_count_zero(bs0);
                } else {
                    int_of_bits_count_nonzero(bs0);
                }
        }
    }

    lemma void bits_of_int_nonzero(int x, nat n)
        requires    0 < x &*& x < pow_nat(2, n);
        ensures     0 < count_bits(snd(bits_of_int(x, n)));
    {
        list<bool> x_bits = snd(bits_of_int(x, n));

        count_nonnegative(x_bits, (eq)(true));

        if (count_bits(x_bits) == 0) {
            int_of_bits_count_zero(x_bits);
            bits_of_int_remainder(x, n);
            int_of_bits_of_int(x, n);

            assert (int_of_bits(0, x_bits) == 0);
            assert (x == int_of_bits(0, x_bits));
            assert (false);
        }
    }

    lemma void count_ge_length<t>(list<t> xs, fixpoint (t,bool) fp)
        requires    true;
        ensures     count(xs, fp) <= length(xs);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0): count_ge_length(xs0, fp);
        }
    }

    lemma void bits_of_int_and_count_nonzero(list<bool> x_bits, list<bool> y_bits, int m)
        requires    
            length(x_bits) == length(y_bits) &*&
            0 <= m &*& m < length(x_bits) &*&
            drop(m, x_bits) == drop(m, y_bits) &*&
            0 < count_bits(drop(m, x_bits));
        ensures
            0 < count_bits(bits_of_int_and(x_bits, y_bits));
    {
        switch(x_bits) {
            case nil:
            case cons(x0, xs0):
                switch(y_bits) {
                    case nil:
                    case cons(y0, ys0):
                        if (m > 0) {
                            bits_of_int_and_count_nonzero(xs0, ys0, m - 1);
                        } else {
                            if (x0) {
                                count_append(cons(x0 && y0, nil), bits_of_int_and(xs0, ys0), (eq)(true));
                                count_nonnegative(cons(x0 && y0, nil), (eq)(true));
                                count_nonnegative(bits_of_int_and(xs0, ys0), (eq)(true));
                            } else {
                                count_append(cons(x0, nil), xs0, (eq)(true));
                                count_nonnegative(cons(x0, nil), (eq)(true));
                                count_nonnegative(xs0, (eq)(true));
                                assert (0 == count_bits(cons(x0, nil)));
                                assert (0 < count_bits(xs0));
                                count_ge_length(xs0, (eq)(true));
                                bits_of_int_and_count_nonzero(xs0, ys0, 0);
                            }
                        }
                }
        }
    }

    lemma void int_of_bits_pow2(list<bool> bits, nat m)
        requires    
            count_bits(bits) == 1 &*& int_of_nat(m) == index_of(true, bits) &*&
            0 <= int_of_nat(m) &*& int_of_nat(m) < length(bits);
        ensures
            int_of_bits(0, bits) == pow_nat(2, m);
    {
        switch(bits) {
            case nil:
            case cons(b, bs0):
                switch(m) {
                    case zero:
                        assert (b);
                        count_append(cons(b, nil), bs0, (eq)(true));
                        count_nonnegative(cons(b, nil), (eq)(true));
                        count_nonnegative(bs0, (eq)(true));
                        int_of_bits_count_zero(bs0);
                    case succ(m_pred): 
                        int_of_bits_pow2(bs0, m_pred);
                }
        }
    }
    
    lemma void index_of_up_bound<t>(t x, list<t> xs)
        requires    0 < count(xs, (eq)(x));
        ensures     index_of(x, xs) < length(xs) - (count(xs, (eq)(x)) - 1);
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                if (x0 == x) {
                    assert (index_of(x, xs) == 0);
                    count_ge_length(xs, (eq)(x));
                } else {
                    index_of_up_bound(x, xs0);
                }
        }
    }

    lemma void x_minus_one_drop(int x, nat m, nat n, list<bool> x_bits, list<bool> x_minus_one_bits)
        requires    
            snd(bits_of_int(x, n)) == x_bits &*&
            snd(bits_of_int(x-1, n)) == x_minus_one_bits &*&
            int_of_nat(m) == index_of(true, x_bits) &*&
            length(x_bits) == length(x_minus_one_bits) &*& length(x_bits) == int_of_nat(n) &*&
            0 < x &*& 0 <= int_of_nat(m) &*& int_of_nat(m) < int_of_nat(n) - 1;
        ensures
            drop(int_of_nat(m) + 1, x_bits) == drop(int_of_nat(m) + 1, x_minus_one_bits);
    {
        switch(x_bits) {
            case nil:
            case cons(x0, xs0):
                switch(x_minus_one_bits) {
                    case nil:
                    case cons(y0, ys0):
                        switch(n) {
                            case zero:
                            case succ(n_pred):
                                switch(m) {
                                    case zero:
                                        div_rem_nonneg(x, 2);
                                        assert(x-1==x/2*2);
                                        div_exact(x/2,2);
                                    case succ(m_pred):
                                        div_mod_gt_0(x%2, x, 2);
                                        div_rem_nonneg(x, 2);
                                        div_minus_one(x/2, 2);

                                        x_minus_one_drop(x/2, m_pred, n_pred, xs0, ys0);
                                }
                        }
                }
        }
    }

    lemma void check_pow2_valid(int x)
        requires    0 < x &*& x < pow_nat(2, N32) &*& (x & (x - 1)) == 0;
        ensures     is_pow2(x, N31) != none;
    {

        list<bool> x_bits = snd(bits_of_int(x, N32));
        list<bool> x_minus_one_bits = snd(bits_of_int(x - 1, N32));
        length_bits_of_int(x, N32);
        length_bits_of_int(x - 1, N32);
        bits_of_int_remainder(x, N32);
        bits_of_int_remainder(x - 1, N32);
        int_of_bits_of_int(x, N32);
        assert(x == int_of_bits(0, x_bits));

        // Proof that x has at least one bit set to true
        bits_of_int_nonzero(x, N32);
        assert(0 < count_bits(x_bits));

        int m = index_of(true, x_bits);
        count_nonzero_to_mem(true, x_bits);
        assert(0 <= m && m < int_of_nat(N32)); 
        assert (nth(m, x_bits) == true);

        if (1 < count_bits(x_bits)) { // Impossible case
            index_of_up_bound(true, x_bits);
            assert (m < int_of_nat(N32) - 1);

            nat m_nat = nat_of_int(m);
            x_minus_one_drop(x, m_nat, N32, x_bits, x_minus_one_bits);
            assert (drop(m+1, x_bits) == drop(m+1, x_minus_one_bits));
            
            count_drop_index_of(true, x_bits);
            assert (0 < count_bits(drop(m, x_bits)));

            bits_of_int_and_def(x, x_bits, x - 1, x_minus_one_bits, N32);
            assert (x & (x - 1) == int_of_bits(0, bits_of_int_and(x_bits, x_minus_one_bits)));

            bits_of_int_and_count_nonzero(x_bits, x_minus_one_bits, m+1);
            assert (0 < count_bits(bits_of_int_and(x_bits, x_minus_one_bits)));

            bitand_limits(x, x - 1, N32);
            bits_of_int_remainder(x & (x - 1), N32);
            int_of_bits_count_nonzero(bits_of_int_and(x_bits, x_minus_one_bits));

            assert (false);
        } else {
            assert (count_bits(x_bits) == 1);

            // Proof that x == 2^m
            int_of_bits_pow2(x_bits, nat_of_int(m));
            assert(int_of_bits(0, x_bits) == pow_nat(2, nat_of_int(m)));

            some_is_pow2(x, nat_of_int(m), N31);
        }
    }

@*/
