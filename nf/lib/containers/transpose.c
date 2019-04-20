//@ #include "transpose.gh"
//@ #include "transpose-lemmas.gh"
//@ #include "listutils-lemmas.gh"

/*@

    // ------------- extract_row/column -------------

    lemma void extract_works(int nb_rows, int nb_cols, int n, int i, int j)
        requires
            extract_row(nb_cols, n) == i &*& extract_col(nb_cols, n) == j &*&
            0 < nb_rows &*& 0 < nb_cols &*&
            0 <= n &*& n < nb_rows * nb_cols;
        ensures
            n == i * nb_cols + j &*&
            0 <= i &*& i < nb_rows &*&
            0 <= j &*& j < nb_cols;
    {
        div_rem_nonneg(n, nb_cols);
        div_exact(nb_rows, nb_cols);
        div_lt(n, nb_rows, nb_cols);
    }

    lemma void extract_unique_row(int nb_rows, int nb_cols, int i1, int i2, int j)
        requires
            i1 != i2 &*& 0 < nb_rows &*& 0 < nb_cols &*&
            0 <= i1 &*& i1 < nb_rows &*&
            0 <= i2 &*& i2 < nb_rows &*&
            0 <= j &*& j < nb_cols;
        ensures
            i1 * nb_cols + j != i2 * nb_cols + j;
    {
        if (i1 < i2) {
            mul_mono_strict(i1, i2, nb_cols);
        } else {
            mul_mono_strict(i2, i1, nb_cols);

        }
    }

    lemma void extract_unique(int nb_rows, int nb_cols, int i1, int i2, int j1, int j2)
        requires
            i1 != i2 &*& j1 != j2 &*&
            0 < nb_rows &*& 0 < nb_cols &*&
            0 <= i1 &*& i1 < nb_rows &*&
            0 <= i2 &*& i2 < nb_rows &*&
            0 <= j1 &*& j1 < nb_cols &*&
            0 <= j2 &*& j2 < nb_cols;
        ensures
            i1 * nb_cols + j1 != i2 * nb_cols + j2;
    {
        if (i1 < i2) {
            mul_mono(i1 + 1, i2, nb_cols);
        } else {
            mul_mono(i2 + 1, i1, nb_cols);
        }
    }

    lemma void extract_bounds(int nb_rows, int nb_cols, int n)
        requires
            0 <= n &*& n < nb_rows * nb_cols &*&
            0 < nb_rows &*& 0 < nb_cols;
        ensures
            0 <= extract_row(nb_cols, n) &*& extract_row(nb_cols, n) < nb_rows &*&
            0 <= extract_col(nb_cols, n) &*& extract_col(nb_cols, n) < nb_cols;
    {
        div_rem_nonneg(n, nb_cols);
        div_lt(n, nb_rows, nb_cols);
        div_exact(nb_rows, nb_cols);
        div_mod_gt_0(n % nb_cols, n, nb_cols);
    }

    lemma void extract_val(int nb_rows, int nb_cols, int i, int j)
        requires    0 <= i &*& i < nb_rows &*& 0 <= j &*& j < nb_cols;
        ensures     extract_row(nb_cols, i * nb_cols + j) == i &*& extract_col(nb_cols, i * nb_cols + j) == j;
    {
        int n = i * nb_cols + j;

        mul_bounds(i, nb_rows - 1, nb_cols, nb_cols);
        div_rem_nonneg(n, nb_cols);
        div_exact(i + 1, nb_cols);
        div_lt(n, i + 1, nb_cols);
        div_exact(i, nb_cols);
        div_ge(i * nb_cols, n, nb_cols);
    }

    lemma void extract_row_ge(int nb_cols, int val, list<int> xs)
        requires    true == forall(xs, (ge)(val + nb_cols)) &*& 0 <= val &*& 0 < nb_cols;
        ensures     true == forall(map( (extract_row)(nb_cols), xs ), (ge)(val/nb_cols + 1));
    {
        switch(xs) {
            case nil:
            case cons(x0, xs0):
                forall_nth(xs, (ge)(val + nb_cols), 0);
                div_incr(val, nb_cols);
                div_ge(val + nb_cols, x0, nb_cols);
                extract_row_ge(nb_cols, val, xs0);
        }
    }

    // ------------- transpose -------------

    lemma_auto(length(transpose_rec_row(xs, nb_cols, idx_col_cst, idx_row, it_row))) void length_transpose_rec_row<t>(list<t> xs, int nb_cols, int idx_col_cst, int idx_row, nat it_row)
        requires    true;
        ensures     length(transpose_rec_row(xs, nb_cols, idx_col_cst, idx_row, it_row)) == int_of_nat(it_row);
    {
        switch(it_row) {
            case zero:
            case succ(it_row_pred): length_transpose_rec_row(xs, nb_cols, idx_col_cst, idx_row + 1, it_row_pred);
        }
    }

    lemma_auto(length(transpose_rec(xs, nb_rows, nb_cols, idx_col, it_col))) void length_transpose_rec<t>(list<t> xs, int nb_rows, int nb_cols, int idx_col, nat it_col)
        requires    0 <= nb_rows;
        ensures     length(transpose_rec(xs, nb_rows, nb_cols, idx_col, it_col)) == nb_rows * int_of_nat(it_col);
    {
        switch(it_col) {
            case zero:
            case succ(it_col_pred):
                length_transpose_rec(xs, nb_rows, nb_cols, idx_col + 1, it_col_pred);
                mul_subst(int_of_nat(it_col), int_of_nat(it_col_pred) + 1, nb_rows);
        }
    }

    lemma_auto(length(transpose(xs, nb_rows, nb_cols))) void length_transpose<t>(list<t> xs, int nb_rows, int nb_cols)
        requires    0 <= nb_rows && 0 <= nb_cols;
        ensures     length(transpose(xs, nb_rows, nb_cols)) == nb_rows * nb_cols;
    {
        length_transpose_rec(xs, nb_rows, nb_cols, 0, nat_of_int(nb_cols));
    }

    lemma void transpose_rec_row_to_src<t>(list<t> xs, int nb_rows, int nb_cols, int i, int idx_col_cst, int idx_row, nat it_row)
        requires
            length(xs) == nb_rows * nb_cols &*&
            0 <= i &*& i < nb_rows &*&
            0 <= idx_col_cst &*& idx_col_cst < nb_cols &*&
            0 <= idx_row &*& idx_row <= i &*&
            int_of_nat(it_row) == nb_rows - idx_row;
        ensures
            nth(i * nb_cols + idx_col_cst, xs) == nth(i - idx_row, transpose_rec_row(xs, nb_cols, idx_col_cst, idx_row, it_row));
    {
        switch(it_row) {
            case zero:
            case succ(it_row_pred): if (idx_row < i) transpose_rec_row_to_src(xs, nb_rows, nb_cols, i, idx_col_cst, idx_row + 1, it_row_pred);
        }
    }

    lemma void transpose_rec_to_src<t>(list<t> xs, list<t> xs_transpose, int nb_rows, int nb_cols, int i, int j, int idx_col, nat it_col)
        requires
            xs_transpose == transpose(xs, nb_rows, nb_cols) &*&
            length(xs) == nb_rows * nb_cols &*&
            0 <= i &*& i < nb_rows &*&
            0 <= j &*& j < nb_cols &*&
            0 <= idx_col &*& idx_col <= j &*&
            int_of_nat(it_col) == nb_cols - idx_col;
        ensures
            nth(i * nb_cols + j, xs) == nth((j - idx_col) * nb_rows + i, transpose_rec(xs, nb_rows, nb_cols, idx_col, it_col));
    {
        switch(it_col) {
            case zero:
            case succ(it_col_pred):
                if (idx_col < j) {
                    transpose_rec_to_src(xs, xs_transpose, nb_rows, nb_cols, i, j, idx_col + 1, it_col_pred);
                    mul_bounds(0, j - (idx_col + 1), nb_rows, nb_rows);
                    mul_bounds(j - (idx_col + 1), int_of_nat(it_col_pred) - 1, nb_rows, nb_rows);
                    nth_append_r(transpose_rec_row(xs, nb_cols, idx_col, 0, nat_of_int(nb_rows)) , transpose_rec(xs, nb_rows, nb_cols, idx_col + 1, it_col_pred), (j - (idx_col + 1)) * nb_rows + i);
                } else {
                    assert (idx_col == j);
                    assert ((j - idx_col) * nb_rows + i == i);
                    transpose_rec_row_to_src(xs, nb_rows, nb_cols, i, idx_col, 0, nat_of_int(nb_rows));
                    nth_append(transpose_rec_row(xs, nb_cols, idx_col, 0, nat_of_int(nb_rows)) , transpose_rec(xs, nb_rows, nb_cols, idx_col + 1, it_col_pred), i);
                }
        }
    }

    lemma void transpose_to_src<t>(list<t> xs, int nb_rows, int nb_cols, int i, int j)
        requires
            length(xs) == nb_rows * nb_cols &*&
            0 <= i &*& i < nb_rows &*&
            0 <= j &*& j < nb_cols;
        ensures
            nth(i * nb_cols + j, xs) == nth(j * nb_rows + i, transpose(xs, nb_rows, nb_cols));
    {
        transpose_rec_to_src(xs, transpose(xs, nb_rows, nb_cols), nb_rows, nb_cols, i, j, 0, nat_of_int(nb_cols));
    }

    lemma void transpose_twice<t>(list<t> xs, int nb_rows, int nb_cols, int i, int j)
        requires
            length(xs) == nb_rows * nb_cols &*&
            0 <= i &*& i < nb_rows &*&
            0 <= j &*& j < nb_cols;
        ensures
            nth(i * nb_cols + j, xs) == nth(i * nb_cols + j, transpose(transpose(xs, nb_rows, nb_cols), nb_cols, nb_rows));
    {
        transpose_to_src(xs, nb_rows, nb_cols, i, j);
        transpose_to_src(transpose(xs, nb_rows, nb_cols), nb_cols, nb_rows, j, i);
    }

    lemma void transpose_twice_list_rec<t>(list<t> xs, int nb_rows, int nb_cols, nat idx)
        requires    length(xs) == nb_rows * nb_cols &*& 0 < nb_rows &*& 0 < nb_cols &*& int_of_nat(idx) <= length(xs);
        ensures     take(int_of_nat(idx), xs) == take(int_of_nat(idx), transpose(transpose(xs, nb_rows, nb_cols), nb_cols, nb_rows));
    {
        switch(idx) {
            case zero:
            case succ(idx_pred):
                transpose_twice_list_rec(xs, nb_rows, nb_cols, idx_pred);

                int n = int_of_nat(idx) - 1;
                int i = extract_row(nb_cols, n);
                int j = extract_col(nb_cols, n);
                extract_works(nb_rows, nb_cols, n, i, j);

                take_plus_one(n, xs);
                take_plus_one(n, transpose(transpose(xs, nb_rows, nb_cols), nb_cols, nb_rows));
                transpose_twice(xs, nb_rows, nb_cols, i, j);
        }
    }

    lemma void transpose_twice_list<t>(list<t> xs, int nb_rows, int nb_cols)
        requires    length(xs) == nb_rows * nb_cols &*& 0 < nb_rows &*& 0 < nb_cols;
        ensures     xs == transpose(transpose(xs, nb_rows, nb_cols), nb_cols, nb_rows);
    {
        take_length(xs);
        take_length(transpose(transpose(xs, nb_rows, nb_cols), nb_cols, nb_rows));
        transpose_twice_list_rec(xs, nb_rows, nb_cols, nat_of_int(length(xs)));
    }

    // ------------- transpose with filter_idx and count -------------

    lemma_auto(length(gen_idx_transpose(idxs, nb_rows, nb_cols))) void length_gen_idx_transpose(list<int> idxs, int nb_rows, int nb_cols)
        requires    true;
        ensures     length(gen_idx_transpose(idxs, nb_rows, nb_cols)) == length(idxs);
    {
        switch(idxs) {
            case nil:
            case cons(i0, is0): length_gen_idx_transpose(is0, nb_rows, nb_cols);
        }
    }

    lemma void gen_idx_transpose_extract(int nb_rows, int nb_cols, int x, int y)
        requires
            true == eq_idx_transpose(nb_rows, nb_cols, x, y) &*&
            0 < nb_rows &*& 0 < nb_cols &*&
            0 <= x &*& x < nb_rows * nb_cols &*&
            0 <= y &*& y < nb_rows * nb_cols;
        ensures
            extract_row(nb_cols, x) == extract_col(nb_rows, y) &*&
            extract_col(nb_cols, x) == extract_row(nb_rows, y);
    {
        int i = extract_row(nb_cols, x);
        int j = extract_col(nb_cols, x);
        extract_bounds(nb_rows, nb_cols, x);
        extract_val(nb_cols, nb_rows, j, i);
    }

    lemma void gen_idx_transpose_map_extract(list<int> idxs, int nb_rows, int nb_cols)
        requires
            true == forall(idxs, (ge)(0)) &*& true == forall(idxs, (lt)(nb_rows * nb_cols)) &*&
            0 < nb_rows &*& 0 < nb_cols;
        ensures
            map( (extract_row)(nb_cols) , idxs ) == map( (extract_col)(nb_rows) , gen_idx_transpose(idxs, nb_rows, nb_cols) ) &*&
            map( (extract_col)(nb_cols) , idxs ) == map( (extract_row)(nb_rows) , gen_idx_transpose(idxs, nb_rows, nb_cols) );
    {
        switch(idxs) {
            case nil:
            case cons(i0, is0):
                gen_idx_transpose_map_extract(is0, nb_rows, nb_cols);

                int i = extract_row(nb_cols, i0);
                int j = extract_col(nb_cols, i0);
                extract_works(nb_rows, nb_cols, i0, i, j);

                mul_bounds(j, nb_cols - 1, nb_rows, nb_rows);
                gen_idx_transpose_extract(nb_rows, nb_cols, i0, j * nb_rows + i);
        }
    }

    lemma void gen_idx_transpose_works(list<int> idxs, int nb_rows, int nb_cols)
        requires    true;
        ensures     true == forall2(idxs, gen_idx_transpose(idxs, nb_rows, nb_cols), (eq_idx_transpose)(nb_rows, nb_cols));
    {
        switch(idxs) {
            case nil:
            case cons(i0, is0): gen_idx_transpose_works(is0, nb_rows, nb_cols);
        }
    }

    lemma void gen_idx_transpose_distinct_helper(list<int> is0, int nb_rows, int nb_cols, int i0)
        requires
            false == mem(i0, is0) &*&
            0 < nb_rows &*& 0 < nb_cols &*&
            true == forall(cons(i0, is0), (ge)(0)) &*& true == forall(cons(i0, is0), (lt)(nb_rows * nb_cols));
        ensures
            false == mem(extract_col(nb_cols, i0) * nb_rows + extract_row(nb_cols, i0), gen_idx_transpose(is0, nb_rows, nb_cols));
    {
        switch(is0) {
            case nil:
            case cons(i00, is00):
                int row0 = extract_row(nb_cols, i0);
                int col0 = extract_col(nb_cols, i0);
                int row00 = extract_row(nb_cols, i00);
                int col00 = extract_col(nb_cols, i00);
                extract_works(nb_rows, nb_cols, i0, row0, col0);
                extract_works(nb_rows, nb_cols, i00, row00, col00);
                assert (i0 != i00);
                assert (row0 != row00 || col0 != col00);

                int i0_transform = col0 * nb_rows + row0;
                int i00_transform = col00 * nb_rows + row00;
                if (row0 != row00 && col0 != col00) {
                    extract_unique(nb_cols, nb_rows, col0, col00, row0, row00);
                } else if (col0 != col00) {
                    assert (row0 == row00);
                    extract_unique_row(nb_cols, nb_rows, col0, col00, row0);
                }
                assert (i0_transform != i00_transform);

                gen_idx_transpose_distinct_helper(is00, nb_rows, nb_cols, i0);
        }
    }

    lemma void gen_idx_transpose_distinct(list<int> idxs, int nb_rows, int nb_cols)
        requires
            true == distinct(idxs) &*&
            0 < nb_rows &*& 0 < nb_cols &*&
            true == forall(idxs, (ge)(0)) &*& true == forall(idxs, (lt)(nb_rows * nb_cols));
        ensures
            true == distinct(gen_idx_transpose(idxs, nb_rows, nb_cols));
    {
        switch(idxs) {
            case nil:
            case cons(i0, is0):
                gen_idx_transpose_distinct(is0, nb_rows, nb_cols);
                gen_idx_transpose_distinct_helper(is0, nb_rows, nb_cols, i0);
        }
    }

    lemma void transpose_filter_idx_transfer<t>(list<t> xs, int nb_rows, int nb_cols, int i, int j, fixpoint (t, bool) fp)
        requires
            true == mem(i * nb_cols + j, filter_idx(xs, 0, fp)) &*&
            length(xs) == nb_rows * nb_cols &*&
            0 <= i &*& i < nb_rows &*&
            0 <= j &*& j < nb_cols;
        ensures
            true == mem(j * nb_rows + i, filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp));
    {
        mul_bounds(i, nb_rows - 1, nb_cols, nb_cols);
        filter_idx_mem_to_nth(xs, 0, fp, i * nb_cols + j);

        transpose_to_src(xs, nb_rows, nb_cols, i, j);

        mul_bounds(j, nb_cols - 1, nb_rows, nb_rows);
        filter_idx_nth_to_mem(transpose(xs, nb_rows, nb_cols), 0, fp, j * nb_rows + i);
    }

    lemma void transpose_filter_idx_helper<t>(list<t> xs, int nb_rows, int nb_cols, fixpoint (t, bool) fp, list<int> idxs, list<int> idxs_transpose)
        requires
            length(xs) == nb_rows * nb_cols &*& 0 < nb_rows &*& 0 < nb_cols &*&
            length(idxs) == length(idxs_transpose) &*&
            true == forall(idxs, (contains)(filter_idx(xs, 0, fp))) &*&
            true == forall(idxs, (ge)(0)) &*& true == forall(idxs, (lt)(nb_rows * nb_cols)) &*&
            true == forall2(idxs, idxs_transpose, (eq_idx_transpose)(nb_rows, nb_cols));
        ensures
            true == forall(idxs_transpose, (contains)(filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp)));
    {
        switch(idxs) {
            case nil: length_0_nil(idxs_transpose);
            case cons(i0, is0):
                switch(idxs_transpose) {
                    case nil:
                    case cons(i0_transpose, is0_transpose):
                        transpose_filter_idx_helper(xs, nb_rows, nb_cols, fp, is0, is0_transpose);

                        int i = extract_row(nb_cols, i0);
                        int j = extract_col(nb_cols, i0);
                        extract_works(nb_rows, nb_cols, i0, i, j);

                        transpose_filter_idx_transfer(xs, nb_rows, nb_cols, i, j, fp);
                        forall2_nth(idxs, idxs_transpose, (eq_idx_transpose)(nb_rows, nb_cols), 0);
                }
        }
    }

    lemma void transpose_filter_idx_length_leq<t>(list<t> xs, int nb_rows, int nb_cols, fixpoint (t, bool) fp)
        requires    length(xs) == nb_rows * nb_cols &*& 0 < nb_rows &*& 0 < nb_cols;
        ensures     length(filter_idx(xs, 0, fp)) <= length(filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp));
    {
        list<t> xs_transpose = transpose(xs, nb_rows, nb_cols);
        list<int> filter_xs_transpose = filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp);

        list<int> idxs = filter_idx(xs, 0, fp);
        filter_idx_ge(xs, 0, fp);
        filter_idx_lt(xs, 0, fp);
        subset_refl(filter_idx(xs, 0, fp));
        assert (true == forall(idxs, (ge)(0)));
        assert (true == forall(idxs, (lt)(length(xs))));
        assert (true == forall(idxs, (contains)(filter_idx(xs, 0, fp))));

        list<int> idxs_transpose = gen_idx_transpose(idxs, nb_rows, nb_cols);
        gen_idx_transpose_works(idxs, nb_rows, nb_cols);
        assert (true == forall2(idxs, idxs_transpose, (eq_idx_transpose)(nb_rows, nb_cols)));

        transpose_filter_idx_helper(xs, nb_rows, nb_cols, fp, idxs, idxs_transpose);

        filter_idx_distinct(xs, 0, fp);
        assert (true == distinct(idxs));

        gen_idx_transpose_distinct(idxs, nb_rows, nb_cols);

        assert (true == distinct(idxs_transpose));
        assert (true == subset(idxs_transpose, filter_xs_transpose));
        distinct2_subset_sublen(idxs_transpose, filter_xs_transpose);
    }

    lemma void transpose_filter_idx_length<t>(list<t> xs, int nb_rows, int nb_cols, fixpoint (t, bool) fp)
        requires    length(xs) == nb_rows * nb_cols &*& 0 < nb_rows &*& 0 < nb_cols;
        ensures     length(filter_idx(xs, 0, fp)) == length(filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp));
    {
        transpose_filter_idx_length_leq(xs, nb_rows, nb_cols, fp);
        transpose_filter_idx_length_leq(transpose(xs, nb_rows, nb_cols), nb_cols, nb_rows, fp);
        transpose_twice_list(xs, nb_rows, nb_cols);
    }

    lemma void transpose_preserves_count<t>(list<t> xs, int nb_rows, int nb_cols, fixpoint (t, bool) fp)
        requires    length(xs) == nb_rows * nb_cols &*& 0 < nb_rows &*& 0 < nb_cols;
        ensures     count(transpose(xs, nb_rows, nb_cols), fp) == count(xs, fp);
    {
        transpose_filter_idx_length(xs, nb_rows, nb_cols, fp);
        filter_idx_length_count_equiv(xs, 0, fp);
        filter_idx_length_count_equiv(transpose(xs, nb_rows, nb_cols), 0, fp);
    }

    lemma void transpose_preserves_integer_copies(list<int> xs, int nb_rows, int nb_cols, int nb_copies, nat val)
        requires    true == integer_copies(val, nb_copies, xs) &*& length(xs) == nb_rows * nb_cols &*& 0 < nb_rows &*& 0 < nb_cols;
        ensures     true == integer_copies(val, nb_copies, transpose(xs, nb_rows, nb_cols));
    {
        switch(val) {
            case zero:  transpose_preserves_count(xs, nb_rows, nb_cols, (eq)(0));
            case succ(val_pred):
                transpose_preserves_count(xs, nb_rows, nb_cols, (eq)(int_of_nat(val)));
                transpose_preserves_integer_copies(xs, nb_rows, nb_cols, nb_copies, val_pred);
        }
    }

    lemma void transpose_extract_filter_idx_subset<t>(list<t> xs, int nb_rows, int nb_cols, fixpoint (t, bool) fp)
        requires
            length(xs) == nb_rows * nb_cols &*&
            0 < nb_rows &*& 0 < nb_cols;
        ensures
            true == subset(map((extract_row)(nb_cols) , filter_idx(xs, 0, fp)), map((extract_col)(nb_rows) , filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp))) &*&
            true == subset(map((extract_col)(nb_cols) , filter_idx(xs, 0, fp)), map((extract_row)(nb_rows) , filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp)));
    {
        list<t> xs_transpose = transpose(xs, nb_rows, nb_cols);
        list<int> filter_xs_transpose = filter_idx(transpose(xs, nb_rows, nb_cols), 0, fp);

        list<int> idxs = filter_idx(xs, 0, fp);
        filter_idx_ge(xs, 0, fp);
        filter_idx_lt(xs, 0, fp);
        subset_refl(filter_idx(xs, 0, fp));

        list<int> idxs_transpose = gen_idx_transpose(idxs, nb_rows, nb_cols);
        gen_idx_transpose_works(idxs, nb_rows, nb_cols);

        transpose_filter_idx_helper(xs, nb_rows, nb_cols, fp, idxs, idxs_transpose);
        assert (true == subset(idxs_transpose, filter_xs_transpose));

        subset_map(idxs_transpose, filter_xs_transpose, (extract_col)(nb_rows));
        subset_map(idxs_transpose, filter_xs_transpose, (extract_row)(nb_rows));
        gen_idx_transpose_map_extract(idxs, nb_rows, nb_cols);
    }

@*/
