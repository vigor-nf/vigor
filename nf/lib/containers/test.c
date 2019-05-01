//@ #include "modulo.gh"
//@ #include "stdex.gh"
//@ #include <bitops.gh>
//@ #include <nat.gh>
//@ #include <listex.gh>


/*@

    lemma void loop_fp_pop(int k, int capacity)
        requires    0 <= k &*& 0 < capacity;
        ensures     loop_fp(k, capacity) == k % capacity;
    {
        div_mod_gt_0(k%capacity, k, capacity);
        mod_rotate(k%capacity, capacity);
        mod_bijection(k%capacity, capacity);
    }

    lemma void mod_add_zero(int a, int b, int k)
        requires    0 <= a &*& 0 < b &*& 0 <= k;
        ensures     (a + b*k) % b == a % b;
    {
        loop_injection_n(a, b, k);
        loop_fp_pop(a + b*k, b);
        loop_fp_pop(a, b);
    }

    lemma void mod_rotate_mul(int a, int b)
        requires    0 <= a &*& 0 < b;
        ensures     ((a * b) % b) == 0;
    {
        div_exact(a, b);
        div_rem_nonneg(a * b, b);
    }

    lemma void pow_nat_div_rem(int x, nat n)
        requires    0 < x &*& n != zero;
        ensures     pow_nat(x, n) / x == pow_nat(x, nat_predecessor(n)) &*& pow_nat(x, n) % x == 0;
    {
        switch(n) {
            case zero:
            case succ(n_pred):
                mod_rotate_mul(pow_nat(x, n_pred), x);
                div_rem_nonneg(pow_nat(x, n), x);
        }
    }

    // ------------- pow2 -------------

    fixpoint int pow2(nat m) { return pow_nat(2, m); }

    fixpoint int sum_pow2(nat n) {
        switch(n) {
            case zero: return 1;
            case succ(n_pred): return pow_nat(2, n) + sum_pow2(n_pred);
        }
    }

    lemma void sum_pow2_pred(nat n)
        requires    n != zero;
        ensures     sum_pow2(n) == pow_nat(2, n) + sum_pow2(nat_predecessor(n));
    {
        switch(n) {
            case zero:
            case succ(n_pred): 
        }
    }

    lemma void sum_pow2_val(nat m)
        requires    m != zero;
        ensures     sum_pow2(nat_predecessor(m)) == pow_nat(2, m) - 1;
    {
        switch(m) {
            case zero:
            case succ(m_pred):
                if (m_pred == zero) {
                    assert (sum_pow2(m_pred) == 1);
                    assert (pow_nat(2, m) == 2);
                } else {
                    sum_pow2_val(m_pred);
                    sum_pow2_pred(m_pred);
                }
        }
    }

    // ------------- bitwise representation of capacity -------------

    lemma void bits_of_int_zero(nat n)
        requires    true;
        ensures     true == forall(snd(bits_of_int(0, n)), (eq)(false));
    {
        switch(n) {
            case zero:
            case succ(n_pred):
                mod_rotate_mul(0, 2);
                assert (0%2 != 1);
                bits_of_int_zero(n_pred);
                assert (snd(bits_of_int(0, n)) == cons(0%2 == 1, snd(bits_of_int(0, n_pred))));
        }
    }


@*/


unsigned loop(unsigned k, unsigned capacity)
//@     requires 0 < capacity &*& capacity < INT_MAX;
//@     ensures 0 <= result &*& result < capacity &*& result == loop_fp(k, capacity);
{
    //@ nat m;
    //@ int m_int = int_of_nat(m);
    //@ assume (m_int < 32);
    //@ assume (capacity == pow_nat(2, m));
    //@ assert (capacity < pow_nat(2, nat_of_int(32))); 

    //@ Z k_bits = Z_of_uint32(k);
    //@ Z capacity_minus_bits = Z_of_uint32(capacity - 1);


    // Proof that capacity == 0...010...0
    

    // Proof that capacity - 1 == 0...01...1

    // forall(take(m_int, snd(capacity_minus_bits), (eq)(true));
    // forall(drop(m_int, snd(capacity_minus_bits), (eq)(false));
    // fst(capacity_minus_bits) == 0;


    // take(m_int, snd(k_bits)) == take(m_int, snd(Z_of_uint32(k & (capacity - 1))))

    //@ assert ((k % capacity) == (k & (capacity - 1)) );

    //@ loop_fp_pop(k, capacity);
    //@ assert ((k % capacity) == loop_fp(k, capacity));

    return k & (capacity - 1);
}