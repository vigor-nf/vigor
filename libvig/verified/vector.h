#ifndef _VECTOR_H_INCLUDED_
#define _VECTOR_H_INCLUDED_

//@ #include "../proof/stdex.gh"
//@ #include "../proof/listexex.gh"
//@ #include "../proof/listutils.gh"

#define VECTOR_CAPACITY_UPPER_LIMIT 140000

struct Vector;

/*@
  predicate vectorp<t>(struct Vector* vector,
                       predicate (void*;t) entp,
                       list<pair<t, real> > values,
                       list<void*> addrs);

  fixpoint list<pair<t, real> > vector_erase_fp<t>(list<pair<t, real> > vector,
                                                   int index) {
    return update(index, pair(fst(nth(index, vector)), 1.0), vector);
  }

  fixpoint list<pair<t, real> > vector_erase_all_fp<t>(list<pair<t, real> > vector,
                                                       list<int> indices) {
    switch(indices) {
      case nil: return vector;
      case cons(h,t):
        return vector_erase_fp(vector_erase_all_fp(vector, t), h);
    }
  }

  fixpoint list<t> vector_get_values_fp<t>(list<pair<t, real> > vector,
                                           list<int> indices) {
    return map((sup)(fst, (nth2)(vector)), indices);
  }

  fixpoint real vector_getf<t>(list<pair<t, real> > vector, t key) {
    return mem(key, map(fst, vector)) ?
             snd(nth(index_of(key, map(fst, vector)), vector)) :
             0.0;
  }
  @*/

/*@
  lemma void vector_addrs_same_len_nodups<t>(struct Vector* vector);
  requires vectorp<t>(vector, ?entp, ?values, ?addrs);
  ensures vectorp<t>(vector, entp, values, addrs) &*&
          length(values) == length(addrs) &*&
          true == no_dups(addrs);
  @*/

/*@
  lemma void vector_erase_all_same_len<t>(list<pair<t, real> > vector,
                                          list<int> indices);
  requires true;
  ensures length(vector) == length(vector_erase_all_fp(vector, indices));
  @*/

/*@
  lemma void vector_get_values_append<t>(list<pair<t, real> > vector,
                                         list<int> indices,
                                         int index, t v);
  requires 0 <= index &*& index < length(vector) &*&
           nth(index, vector) == pair(v, _);
  ensures append(vector_get_values_fp(vector, indices), cons(v, nil)) ==
          vector_get_values_fp(vector, append(indices, cons(index, nil)));
  @*/

/*@
  lemma void vector_erase_all_keeps_val<t>(list<pair<t, real> > vector,
                                           list<int> indices,
                                           int index);
  requires 0 <= index &*& index < length(vector);
  ensures fst(nth(index, vector_erase_all_fp(vector, indices))) ==
          fst(nth(index, vector));
  @*/

/*@
   lemma void vector_erase_one_more<t>(list<pair<t, real> > vector,
                                       list<int> indices,
                                       int index);
   requires true;
   ensures vector_erase_fp(vector_erase_all_fp(vector, indices), index) ==
           vector_erase_all_fp(vector, append(indices, cons(index, nil)));
  @*/

/*@
  lemma void vector_erase_all_keep_inv<t>(list<pair<t, real> > vector,
                                          list<int> indices,
                                          fixpoint (t,bool) inv);
  requires true == forall(vector, (sup)(inv, fst));
  ensures true == forall(vector_erase_all_fp(vector, indices), (sup)(inv, fst));
  @*/

/*@
   fixpoint bool is_one<t>(pair<t,real> r) { return snd(r) == 1.0; }
  @*/

/*@
  lemma_auto void forall_is_one_update<t>(list<pair<t, real> > lst, int i, t v)
  requires true == forall(lst, is_one);
  ensures true == forall(update(i, pair(v, 1.0), lst), is_one);
  {
    forall_update(lst, is_one, i, pair(v, 1.0));
  }
  @*/

typedef void vector_init_elem/*@ <t> (predicate (void*;t) entp,
                                      int elem_size,
                                      t val) @*/
                             (void* elem);
/*@ requires chars(elem, elem_size, _); @*/
/*@ ensures entp(elem, val); @*/

int vector_allocate/*@ <t> @*/(int elem_size, unsigned capacity,
                               vector_init_elem* init_elem,
                               struct Vector** vector_out);
/*@ requires [_]is_vector_init_elem<t>(init_elem, ?entp, elem_size, ?val) &*&
             0 < elem_size &*& elem_size < 4096 &*&
             0 <= capacity &*& capacity < VECTOR_CAPACITY_UPPER_LIMIT &*&
             *vector_out |-> ?old_vo; @*/
/*@ ensures result == 0 ?
            (*vector_out |-> old_vo) :
            (*vector_out |-> ?new_vo &*&
             result == 1 &*&
             vectorp<t>(new_vo, entp, ?contents, ?addrs) &*&
             length(contents) == capacity &*&
             contents == repeat(pair(val, 1.0), nat_of_int(capacity)) &*&
             true == forall(contents, is_one)); @*/

void vector_borrow/*@ <t> @*/(struct Vector* vector, int index, void** val_out);
/*@ requires vectorp<t>(vector, ?entp, ?values, ?addrs) &*&
             0 <= index &*& index < length(values) &*&
             nth(index, values) == pair(?val, ?frac) &*&
             *val_out |-> _; @*/
/*@ ensures *val_out |-> ?vo &*&
            vectorp<t>(vector, entp, update(index, pair(val, 0.0), values), addrs) &*&
            vo == nth(index, addrs) &*&
            vo != 0 &*&
            (frac == 0.0 ? true : [frac]entp(vo, val)); @*/

void vector_return/*@ <t> @*/(struct Vector* vector, int index, void* value);
/*@ requires vectorp<t>(vector, ?entp, ?values, ?addrs) &*&
             0 <= index &*& index < length(values) &*&
             value == nth(index, addrs) &*&
             [?frac]entp(value, ?v) &*&
             nth(index, values) == pair(_, 0); @*/
/*@ ensures vectorp<t>(vector, entp, update(index, pair(v, frac), values), addrs) &*&
            (frac == 0 ? [0]entp(value, v) : true); @*/

#endif//_VECTOR_H_INCLUDED_
