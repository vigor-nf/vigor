//@ #include "mod_pow2.gh"
//@ #include "modulo.gh"
//@ #include <nat.gh>

/*@

    fixpoint int pow2(nat m) {
        return pow_nat(2, m);
    }

    fixpoint option<nat> is_pow2(int x, nat m) {
        switch(m) {
            case zero: return (x == pow2(zero) ? some(zero) : none);
            case succ(m_pred): return (x == pow2(m) ? some(m) : is_pow2(x, m_pred));
        }
    }

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

@*/


unsigned loop(unsigned k, unsigned capacity)
//@     requires 0 < capacity &*& capacity < INT_MAX &*& is_pow2(capacity, N31) != none;
//@     ensures 0 <= result &*& result < capacity &*& result == loop_fp(k, capacity);
{
    //@ nat m = is_pow2_some(capacity, N31);
    //@ mod_bitand_equiv(k, capacity, m);
    //@ div_mod_gt_0(k%capacity, k, capacity);
    //@ assert ((k % capacity) == (k & (capacity - 1)) );
    //@ assert ((k % capacity) == loop_fp(k, capacity));

  return k & (capacity - 1);
}