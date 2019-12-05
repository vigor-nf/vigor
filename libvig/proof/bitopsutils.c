//@ #include <bitops.gh>
//@ #include <nat.gh>

//@ #include "modulo.gh"
//@ #include "bitopsutils.gh"

/*@

    // ------------- pow_nat -------------

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

    lemma void pow_nat_bounds(int x, nat n)
        requires    0 < x;
        ensures     0 < pow_nat(x, n);
    {
        switch(n) {
            case zero:
            case succ(n_pred): pow_nat_bounds(x, n_pred);
        }
    }

    lemma void pow_nat_gt(int x, nat n, nat m)
        requires    1 < x &*& int_of_nat(n) < int_of_nat(m);
        ensures     pow_nat(x, n) < pow_nat(x, m);
    {
        switch(m) {
            case zero:
            case succ(m_pred):
                switch(n) {
                    case zero: 
                        assert (pow_nat(x, n) == 1);
                        assert (pow_nat(x, m) == x * pow_nat(x, m_pred));
                        pow_nat_bounds(x, m_pred);
                    case succ(n_pred): 
                        pow_nat_gt(x, n_pred, m_pred);
                }
        }
    }

    // ------------- bits_of_int -------------

    lemma_auto(length(snd(bits_of_int(x, n)))) void length_bits_of_int(int x, nat n) 
        requires    true; 
        ensures     length(snd(bits_of_int(x, n))) == int_of_nat(n);
    {
        switch(n) {
            case zero:
            case succ(n_pred): length_bits_of_int(x/2, n_pred);
        }
    }

    lemma void bits_of_int_zero(nat n)
        requires    true;
        ensures     true == forall(snd(bits_of_int(0, n)), (eq)(false)) &*& fst(bits_of_int(0, n)) == 0;
    {
        switch(n) {
            case zero:
            case succ(n_pred):
                mod_rotate_mul(0, 2);
                div_rem_nonneg(0, 2);
                bits_of_int_zero(n_pred);
        }
    }

    lemma void bits_of_int_remainder(int x, nat n)
        requires    0 <= x &*& x < pow_nat(2, n);
        ensures     fst(bits_of_int(x, n)) == 0;
    {
        switch (n) {
            case zero:
            case succ(n_pred):
                assert (pow_nat(2, n) == 2 * pow_nat(2, n_pred));
                div_lt(x, pow_nat(2, n_pred), 2);
                div_exact(pow_nat(2, n_pred), 2);
                assert (x/2 < pow_nat(2, n_pred));
                div_ge(0, x, 2);
                division_round_to_zero(0, 2);
                bits_of_int_remainder(x/2, n_pred);
        }
    }

    lemma void bits_of_int_pow2_mask(nat n, nat m)
        requires
            int_of_nat(m) <= int_of_nat(n);
        ensures
            true == forall(take(int_of_nat(m), snd(bits_of_int(pow_nat(2, m)-1, n))), (eq)(true)) &*& 
            true == forall(drop(int_of_nat(m), snd(bits_of_int(pow_nat(2, m)-1, n))), (eq)(false)) &*& 
            0 == fst(bits_of_int(pow_nat(2, m)-1, n));
    {
        switch(m) {
            case zero:
                bits_of_int_zero(n);
            case succ(m_pred):
                switch(n) {
                    case zero:
                    case succ(n_pred):
                        bits_of_int_pow2_mask(n_pred, m_pred);
                        assert (snd(bits_of_int(pow_nat(2, m)-1, n)) == cons( (pow_nat(2, m)-1)%2==1 , snd(bits_of_int((pow_nat(2, m)-1)/2, n_pred)) ) );

                        pow_nat_div_rem(2, m);
                        pow_nat_bounds(2, m_pred);
                        div_minus_one(pow_nat(2, m_pred), 2);
                        assert((pow_nat(2, m)-1)/2 == pow_nat(2, m_pred) - 1);

                        div_rem_nonneg(pow_nat(2, m), 2);
                        div_rem_nonneg(pow_nat(2, m) - 1, 2);
                        assert((pow_nat(2, m)-1)%2==1);
                }
        }
    }

    // ------------- bits_of_int_and -------------

    lemma void length_bits_of_int_and(list<bool> x_bits, list<bool> y_bits)
        requires    true;
        ensures     length(bits_of_int_and(x_bits, y_bits)) == ((length(x_bits) < length(y_bits)) ? length(y_bits) : length(x_bits));
    {
        switch(x_bits) {
            case nil:
            case cons(x0, xs0):
                switch(y_bits) {
                    case nil:
                    case cons(y0, ys0): length_bits_of_int_and(xs0, ys0);
                }
        }
    }

    lemma void bits_of_int_and_zero(list<bool> x_bits, list<bool> y_bits)
        requires    length(x_bits) == length(y_bits) &*& true == forall(y_bits, (eq)(false)); 
        ensures     true == forall(bits_of_int_and(x_bits, y_bits), (eq)(false));
    {
        switch(x_bits) {
            case nil:
            case cons(x0, xs0):
                switch(y_bits) {
                    case nil:
                    case cons(y0, ys0): bits_of_int_and_zero(xs0, ys0);
                }
        }
    }

    lemma void bits_of_int_and_mask(list<bool> k_bits, list<bool> mask_bits, int m) 
        requires 
            length(k_bits) == length(mask_bits) &*& 
            true == forall(take(m, mask_bits), (eq)(true)) &*& 
            true == forall(drop(m, mask_bits), (eq)(false)) &*&
            0 <= m &*& m < length(k_bits);
        ensures
            take(m, k_bits) == take(m, bits_of_int_and(k_bits, mask_bits)) &*&
            true == forall(drop(m, bits_of_int_and(k_bits, mask_bits)), (eq)(false));
    {
        switch(k_bits) {
            case nil:
            case cons(k0, ks0):
                switch(mask_bits) {
                    case nil:
                    case cons(m0, ms0):
                        if (m > 0) {
                            bits_of_int_and_mask(ks0, ms0, m - 1);
                        } else {
                            bits_of_int_and_zero(k_bits, mask_bits);
                        }
                }
        }
    }

    lemma void Z_bits_of_int_and_equiv(list<bool> xs, list<bool> ys)
        requires    length(xs) == length(ys);
        ensures     Z_and(Z_of_bits(Zsign(false), xs), Z_of_bits(Zsign(false), ys)) == Z_of_bits(Zsign(false), bits_of_int_and(xs, ys));
    {
        switch(xs) {
            case nil: length_0_nil(ys);
            case cons(x0, xs0):
                switch(ys) {
                    case nil:
                    case cons(y0, ys0): Z_bits_of_int_and_equiv(xs0, ys0);
                }
        }
    }

    lemma void int_of_Z_of_bits(list<bool> bits)
        requires    true;
        ensures     int_of_Z(Z_of_bits(Zsign(false), bits)) == int_of_bits(0, bits);
    {
        switch(bits) {
            case nil:
            case cons(b, bs0): int_of_Z_of_bits(bs0);
        }
    }

    lemma void bits_of_int_and_def(int x, list<bool> x_bits, int y, list<bool> y_bits, nat n) 
        requires 
            bits_of_int(x, n) == pair(0, x_bits) &*& 
            bits_of_int(y, n) == pair(0, y_bits) &*& 
            0 <= x &*& x < pow_nat(2, n) &*& 0 <= y &*& y < pow_nat(2, n);
        ensures
            (x & y) == int_of_bits(0, bits_of_int_and(x_bits, y_bits));
    {
        Z_of_uintN(x, n);
        Z_of_uintN(y, n);
        bitand_def(x, Z_of_bits(Zsign(false), x_bits), y, Z_of_bits(Zsign(false), y_bits));

        length_bits_of_int(x, n);
        length_bits_of_int(y, n);
        Z_bits_of_int_and_equiv(x_bits, y_bits);

        int_of_Z_of_bits(bits_of_int_and(x_bits, y_bits));
    }

    // ------------- int_of_bits -------------

    lemma void int_of_bits_zero(list<bool> bits)
        requires    true == forall(bits, (eq)(false));
        ensures     int_of_bits(0, bits) == 0;
    {
        switch (bits) {
            case nil:
            case cons(b, bs0): int_of_bits_zero(bs0);
        }
    }

    lemma void int_of_bits_bounds(list<bool> bits)
        requires    true;
        ensures     0 <= int_of_bits(0, bits);
    {
        switch(bits) {
            case nil:
            case cons(b, bs0): int_of_bits_bounds(bs0);
        }
    }

    lemma void int_of_bits_lt(list<bool> bits, nat m)
        requires
            0 <= int_of_nat(m) &*& int_of_nat(m) < length(bits) &*&
            true == forall(drop(int_of_nat(m), bits), (eq)(false));
        ensures
            int_of_bits(0, bits) < pow_nat(2, m);
    {
        switch(bits) {
            case nil:
            case cons(b, bs0):
                switch(m) {
                    case zero:
                        pow_nat_bounds(2, m);
                        int_of_bits_zero(bits);
                    case succ(m_pred):
                        int_of_bits_lt(bs0, m_pred);
                }
        }
    }

    lemma void int_of_bits_ge(list<bool> bits, nat m)
        requires
            0 <= int_of_nat(m) &*& int_of_nat(m) < length(bits) &*&
            nth(int_of_nat(m), bits) == true;
        ensures
            pow_nat(2, m) <= int_of_bits(0, bits);
    {
        switch(bits) {
            case nil:
            case cons(b, bs0):
                switch(m) {
                    case zero:
                        assert (b == true);
                        int_of_bits_bounds(bs0);
                    case succ(m_pred):
                        int_of_bits_ge(bs0, m_pred);
                }
        }
    }

    lemma void bits_of_int_of_bits(list<bool> bits, nat n)
        requires    int_of_nat(n) == length(bits);
        ensures     bits == snd(bits_of_int(int_of_bits(0, bits), n));
    {
        switch(bits) {
            case nil:
            case cons(b, bs0):
                switch(n) {
                    case zero:
                    case succ(n_pred):
                        int int_bits = int_of_bits(0, bits);
                        int int_bs0 = int_of_bits(0, bs0);
                        list<bool> bits_int_bits = snd(bits_of_int(int_bits, n));
                        list<bool> bits_int_bs0 = snd(bits_of_int(int_bs0, n_pred));

                        bits_of_int_of_bits(bs0, n_pred);
                        assert (bs0 == snd(bits_of_int(int_bs0, n_pred)));

                        assert (int_bits == 2 * int_bs0 + (b ? 1 : 0));

                        if (!b) {
                            int_of_bits_bounds(bits);
                            div_rem_nonneg(int_bits, 2);
                            assert (int_bs0*2 == int_bits);
                            assert ( bits_int_bits == cons(int_bits%2==1, bits_int_bs0) );
                        } else {
                            int_of_bits_bounds(bits);
                            div_rem_nonneg(int_bits, 2);
                            assert (int_bits%2==1); 
                            assert ( bits_int_bits == cons(int_bits%2==1, bits_int_bs0) );
                        }
                }
        }
    }

@*/