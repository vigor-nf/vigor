//@ #include "prime.gh"

/*@

    // Assumption !
    lemma void prime_is_coprime_with_anything(int prime, int n)
        requires    true == is_prime(prime) &*& 0 < n;
        ensures     true == are_coprime(n, prime);
    {
        assume (true == are_coprime(n, prime));
    }

    lemma void modulo_less_than(int k, int m)
        requires 0 <= k &*& k < m &*& 0 < m;
        ensures k % m == k;
    {
        division_round_to_zero(k, m);
        div_rem_nonneg(k, m);
    }

    // Assumption !
    lemma void modulo_add_constant(int offset, int mod, int a, int b)
        requires 0 <= a &*& 0 <= b &*& 0 <= offset &*& 0 <= mod &*&
                a % mod != b % mod;
        ensures  (a + offset) % mod != (b + offset) % mod;
    {
        assume ((a + offset) % mod != (b + offset) % mod);
    }

    // Assumption !
    lemma void modulo_mul_coprime(int k, int s, int m)
        requires
            0 < k &*& k < m &*&
            0 < s &*& s < m &*&
            0 < m &*&
            (k % m != 0) &*& true == are_coprime(s, m);
        ensures
            (k * s) % m != 0;
    {
        assume ((k * s) % m != 0);
    }

    // Assumption !
    lemma void modulo_mul_split(int a, int b, int m)
        requires
            0 <= a &*& 0 <= b &*&
            0 < m &*&
            (b - a) % m != 0;
        ensures
            b % m != a % m;
    {
        assume (b % m != a % m);
    }

    lemma void modulo_permutation(int mul, int mod, int a, int b)
        requires
            0 <= a &*& a < mod &*&
            0 <= b &*& b < mod &*&
            0 < mul &*& mul < mod &*&
            0 < mod &*& a != b &*&
            true == are_coprime(mul, mod);
        ensures
            (mul * a) % mod != (mul * b) % mod;
    {
        if (b > a) {
            modulo_less_than(b - a, mod);
            modulo_mul_coprime(b - a, mul, mod);
            assert ((mul * (b - a)) % mod != 0 );
            mul_nonnegative(mul, a);
            mul_nonnegative(mul, b);
            modulo_mul_split(mul * a, mul * b, mod);
            assert ( (mul * b) % mod != (mul * a) % mod);
        } else {
            modulo_less_than(a - b, mod);
            modulo_mul_coprime(a - b, mul, mod);
            assert ((mul * (a - b)) % mod != 0 );
            mul_nonnegative(mul, a);
            mul_nonnegative(mul, b);
            modulo_mul_split(mul * b, mul * a, mod);
            assert ( (mul * b) % mod != (mul * a) % mod);
        }
    }

@*/
