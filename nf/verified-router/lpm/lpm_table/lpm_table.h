//@ #include <list.gh>
//@ #include <listex.gh>

/*@
    inductive lpmTable = lpmTable(list<pair<list<int>, int>>, size_t);

    predicate lpmTable_p(struct lpm_table *lpm_table, lpmTable tbl);
    predicate lpmPrefix_p(struct lpm_prefix *lpm_prefix, list<int>);

    fixpoint size_t lpmTable_max(lpmTable tbl){
        switch(tbl) { case lpmTable(entries, max):
            return max;
        }
    }

    fixpoint list<pair<list<int>, int>> lpmTable_entries(lpmTable tbl){
        switch(tbl) { case lpmTable(entries, max):
            return entries;
        }
    }

    fixpoint lpmTable lpmTable_empty_fp(size_t max){
        return lpmTable(nil, max);
    }

    fixpoint int lpmTable_n_entries(lpmTable tbl){
        switch(tbl){
            case lpmTable(entries, max):
                return length(entries);
        }
    }

    fixpoint bool lpmTable_contains_prefix(lpmTable tbl, list<int> prefix){
        switch(tbl){
            case lpmTable(entries, max):
                return exists(entries, (lpm_entry_contains_prefix)(prefix));
        }
    }

    fixpoint bool lpm_entry_contains_prefix(list<int> prefix,
                                        pair<list<int>, int> entry)
    {
        switch(entry) { case pair(p, val):
            return p == prefix;
        }
    }

    fixpoint bool lpmTable_contains_value(lpmTable tbl, int value){
        switch(tbl) { case lpmTable(entries, max):
            return exists(entries, (lpm_entry_contains_value)(value));
        }
    }

    fixpoint bool lpm_entry_contains_value(int val, pair<list<int>, int> entry){
        switch(entry) { case pair(p, v):
            return v == val;
        }
    }

    fixpoint bool lpmTable_contains_entry(lpmTable tbl,
                                        pair<list<int>, int> entry)
    {
        switch(tbl) { case lpmTable(entries, max):
            return contains(entries, entry);
        }
    }


    fixpoint lpmTable lpmTable_remove_prefix(lpmTable tbl, list<int> prefix){
        swicth(tbl) { case lpmTable(entries, max):
            return lpmTable(lpm_entries_remove_prefix(entries), max);
        }
    }

    fixpoint list<pair<lpmKey, int>> lpm_entries_remove_prefix(
                            list<pair<list<int>, in>> entries, list<int> prefix)
    {
        switch(entries) {
            case nil:
                return entries;
            case cons(h, t):
                switch(h) { case pair(p, v):
                    if(p == prefix){
                        return lpm_entries_remove_prefix(t, prefix);
                    } else {
                        return cons(h, lpm_entries_remove_prefix(t, prefix));
                    }
                }
        }
    }

    fixpoint lpmTable lpmTable_remove_entry(lpmTable tbl,
                                        pair<list<int>, int> entry){
        switch(tbl) { case lpmTable(entries, max):
            return lpmTable(remove(entry, entries), max);
        }
    }

    fixpoint int match_length(list<int> p1, list<int> p2){
        return match_length_aux(p1, p2, 0);
    }

    fixpoint int match_length_aux(list<int> p1, list<int> p2, int acc){
        switch(p1) {
            case nil: return acc;
            case cons(h1, t1):
                switch(p2) {
                    case nil: return acc;
                    case cons(h2, t2):
                        if(h1 == h2){
                            return match_length_aux(t1, t2, acc+1)
                        } else {
                            return acc;
                        }
                }
        }
    }

    fixpoint lpmKey lpmTable_get_prefix_for_value(lpmTable tbl, int val){
        switch(tbl) { case lpmTable(entries, max):
            return lpm_entries_get_prefix_for_value(entries, val);
        }
    }

    fixpoint lpmKey lpm_entries_get_prefix_for_value(
                                    list<pair<list<int>, int>> entries, int val)
    {
        switch(entries) {
            case nil: return nil;
            case cons(h, t):
                switch(h) { case pair(prefix, v):
                    if(v == val){
                        return prefix;
                    } else {
                        return lpm_entries_get_prefix_for_value(t, val);
                    }
                }
        }
    }

    fixpoint bool prefix_lower_matchlength(int matchlen, list<int> prefix,
                                            pair<lpmKey, int> entry)
    {
        switch(entry) { case pair(p, val):
            return matchlength(prefix, p) <= matchlen;
        }
    }
}
@*/

int lpm_table_allocate(struct lpm_table *table_out, size_t max_entries);
/*@ requires max_entries > 0 &*&
             table_out |-> ?old_val; @*/
/*@ ensures result == 0 ?
                table_out |-> ?tbl &*&
                lpmTable_p(tbl, lpmTable_empty_fp(max_entries)) :
                table_out |-> old_val; @*/

int lpm_table_update_elem(struct lpm_table *table, struct lpm_prefix *prefix,
                            int value);
/*@ requires lpmTable_p(table, ?old_tbl) &*&
              lpmTable_n_entries(old_tbl) < lpmTable_max(old_tbl); @*/
/*@ ensures lpmTable_p(table, ?new_tbl) &*&
            lpmPrefix_p(prefix, ?p) &*&
            lpmTable_contains_entry(new_tbl, pair(p, value)) &*&
            lpmTable_remove_entry(new_tbl, pair(p, value)) ==
                lpmTable_remove_prefix(old_tbl, p) &*&
            lpmTable_n_entries(new_tbl) = lpmTable_contains_prefix(old_tbl, p) ?
                lpmTable_n_entries(old_tbl):
                lpmTable_n_entries(old_tbl) + 1;
            @*/

int lpm_table_delete_elem(struct lpm_table *table, struct lpm_prefix *prefix);
/*@ requires lpmTable_p(table, ?old_tbl) &*&
             lpmPrefix_p(prefix, ?p) &*&
             lpmTable_contains_prefix(old_tbl, p); @*/
/*@ ensures lpmTable_p(table, ?new_tbl) &*&
            new_tbl == lpmTable_remove_prefix(old_tbl, p) &*&
            lpmTable_n_entries(new_tbl) == lpmTable_n_entries(old_tbl) - 1; @*/

int lpm_table_lookup(struct lpm_table *table, struct lpm_prefix *prefix);
/*@ requires lpmTable_p(table, ?tbl) &*&
             lpmTable_n_entries(tbl) > 0; @*/
/*@ ensures lpmPrefix_p(prefix, ?p) &*&
            lpmTable_contains_value(tbl, result) &*&
            forall(lpmTable_entries(tbl),
                    (prefix_lower_matchlength)
                    (matchlength(p, lpmTable_get_prefix_for_value(tbl, result)))
                    (p)
                );@*/
