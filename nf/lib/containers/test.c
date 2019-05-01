//@ #include "modulo.gh"
//@ #include <bitops.gh>
//@ #include <nat.gh>

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


    // Proof that capacity == 0...010...0
    

    // Proof that capacity - 1 == 0...01...1


    //@ assert ((k % capacity) == (k & (capacity - 1)) );

    //@ loop_fp_pop(k, capacity);
    //@ assert ((k % capacity) == loop_fp(k, capacity));

    return k & (capacity - 1);
}