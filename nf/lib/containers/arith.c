//@ #include "arith.gh"

/*@

    lemma void mul_equal(int a, int b, int c)
        requires    0 <= a &*& 0 < b &*& 0 <= c &*& a * b == c;
        ensures     a <= c;
    {
        for (int i = b; i > 1; i--)
            invariant 1 <= i &*& i <= b &*& a*i<=c;
            decreases i;
        {
        }
    }

    //Taken from https://groups.google.com/forum/#!topic/verifast/eCf5QzLtGlo
    lemma void mul_nonnegative(int x, int y)
        requires 0 <= x &*& 0 <= y;
        ensures 0 <= x * y;
    {
        for (int i = 0; i < x; i++)
            invariant 0 <= i &*& i <= x &*& 0 <= i * y;
            decreases x - i;
        {
        }
    }

    lemma void mul_mono(int i, int n, int a)
        requires i <= n &*& 0 <= a;
        ensures i * a <= n * a;
    {
        for (int j = i; j < n; j++)
            invariant i <= j &*& j <= n &*& i * a <= j * a;
            decreases n - j;
        {
        }
    }

    lemma void mul_nonzero(int a, int b)
        requires a > 0 &*& b > 0;
        ensures a * b > 0;
    {
        mul_nonnegative(a - 1, b);
        assert (a-1)*b < a*b;
    }

    lemma void mul_mono_strict(int i, int n, int a)
        requires 0 <= i &*& i < n &*& 0 < a;
        ensures 0 <= i * a &*& i * a < n * a;
    {
        mul_nonnegative(i, a);
        for (int j = 1; j < a; j++)
            invariant i < n &*& j <= a &*& i * j < n * j;
            decreases a - j;
        {
        }
    }

    lemma void mul_bounds(int x, int xb, int y, int yb)
        requires 0 <= x &*& x <= xb &*& 0 <= y &*& y <= yb;
        ensures 0 <= x * y &*& x * y <= xb * yb;
    {
        mul_nonnegative(x, y);
        mul_mono(x, xb, y);
        assert x * y <= xb * y;
        mul_mono(y, yb, xb);
        assert y * xb <= yb * xb;
    }

    lemma void mul_subst(int x, int y, int a)
    requires x == y &*& 0 <= a;
    ensures a*x == a*y;
    {
    for (int i = 0; i < a; i++)
        invariant 0 <= i &*& i <= a &*& i*x == i*y;
        decreases a-i;
    {}
    }

    lemma void less_than_neq(int a, int b)
    requires a < b;
    ensures a != b;
    {
    }

@*/
