#ifndef INDUCTIVE_H
#define INDUCTIVE_H

#include "common.h"
/*
 * Part 2: Warm Up: Classic List Reversal
 *
 * type list_shape = { cell : int -> lst; size : int }
 *
 * invariant { 0 <= size }
 * invariant { forall i. 0 <= i < size -> cell[i] <> nil }
 * invariant { forall i. 0 <= i < size ->
 * forall j. 0 <= j <= size -> i <> j -> cell[i] <> cell[j] }
 *
 * predicate listLR (ls: list_shape) (m: mem) (p: lst) (lo hi: int) (q: lst) =
 *      0 <= lo <= hi <= ls.size /\ p = ls.cell[lo] /\ q = ls.cell[hi] /\
 *      forall i. lo <= i < hi -> m.mcdr[ls.cell[i]] = ls.cell[i+1]
 *
 * predicate listRL (ls: list_shape) (m: mem) (p: lst) (k: int) =
 *      (k = 0 /\ p = nil) \/
 *      (0 < k <= ls.size /\ p = ls.cell[k-1] /\ m.mcdr[ls.cell[0]] = nil /\
 *      forall i. 0 < i < k -> m.mcdr[ls.cell[i]] = ls.cell[i-1])
 */

/*@
   predicate well_formed_list_shape(list_shape shape) =
       shape.count >= 0 &&
       \forall integer i ; 0 <= i <= shape.count ==> shape.cells[i] != NULL &&
       \forall integer j ; 0 <= j <= shape.count ==> \forall integer i ; 0 <= i
   <= shape.count ==> i != j ==> shape.cells[i] != shape.cells[j];
 */

/*@
  predicate listLR (list_shape ls, lst_t p, integer lo, integer hi, lst_t q) =
      0 <= lo <= hi <= ls.count &&
      p == ls.cells[lo] &&
      q == ls.cells[hi] &&
      \forall integer i; lo <= i < hi ==> ls.cells[i]->cdr == ls.cells[i + 1];
 */

/*@
    predicate listRL (list_shape ls, lst_t p, integer k) =
        (k == 0 && p == NULL) ||
        (
            0 < k <= ls.count && p == ls.cells[k - 1] &&
            ls.cells[0]->cdr == \null &&
            \valid(ls.cells[0]) &&
            \forall integer i; 0 < i < k ==> ls.cells[i]->cdr == ls.cells[i - 1] && \valid(ls.cells[i])
        );
 */




/*@
    predicate reversal{L1, L2}(list_shape ls, integer k) =
        \forall integer i; 0 <= i < \at(ls.count, L1) ==> (
            i < k || \at(ls.count, L1) - k <= i ==>
            \at(ls.cells[i]->car, L1) == \at(ls.cells[i]->car, L2) && (
                k <= i < \at(ls.count, L1) - k ==> \at(ls.cells[i]->car, L1) ==
   \at( ls.cells[ls.count - 1 - i]->car , L2)
            )
        );
 */

/*@ predicate valid_or_null(lst_t p) = p == NULL || \valid(p); */

/*@ logic lst_t nth(lst_t l, integer n) =
    l == \null ? (lst_t)\null :
    n == 0 ? l :
    nth(l->cdr, n-1);
*/

/*@
  predicate separated_list_aux(lst_t p, integer n) =
    \forall integer i, j; 0 <= i < j < n ==>
      \separated(nth(p, i), nth(p, j));
*/

/*@
  predicate separated_list(lst_t p) =
    \exists integer n; n >= 0 &&
      nth(p, n) == \null &&
      (\forall integer i; 0<= i < n ==> \valid(nth(p, i))) &&
      separated_list_aux(p, n);
*/

/*@ predicate valid_list(lst_t p) =
    p == NULL || (\valid(p) && separated_list(p) && valid_list(p->cdr));
*/

/*@ lemma non_null_valid_list_is_valid:
    \forall lst_t x; x != NULL && valid_list(x) ==> \valid(x);
 */

/*@ lemma non_null_valid_list_next_is_valid:
    \forall lst_t x; x != NULL && valid_list(x) ==> valid_list(x->cdr);
 */

/*@ logic integer length(lst_t l) =
  l == \null ? 0 : 1 + length(l->cdr);
*/

/*@ predicate two_separated(lst_t l1, lst_t l2) =
  (l1 == \null || l2 == \null) ||
  \forall integer i, j; length(l1) > i >= 0 && length(l2) > j >= 0 ==> \separated(nth(l1, i), nth(l2, j));
*/



// /*@ predicate two_separated(lst_t l1, lst_t l2) =
//   (l1 == \null || l2 == \null) ||
//   \exists integer n1, n2; n1 >= 0 && n2 >= 0 && nth(l1, n1) == \null &&
//   \forall integer i, j; n1 > i >= 0 && n2 > j >= 0 ==> \separated(nth(l1, i), nth(l2, j));
// */

/*@ lemma length_of_nonnull_valid:
    \forall lst_t l;
    valid_list(l) && l != \null ==>
      \exists integer n; n >= 1 && nth(l, n) == \null &&
        \forall integer i; 0 <= i < n ==> \valid(nth(l, i));
 */

 /*@ lemma sep_pointers:
  \forall lst_t l1, l2; \separated(l1, l2) ==> l1 != l2;
 */

/*@ lemma two_sep_first_elem:
  \forall lst_t l1, l2, integer n1, n2;
    n1 >= 1 && n2 >= 1 &&
    nth(l1, n1) == \null && nth(l2, n2) == \null &&
    (\forall integer i, j; 0 <= i < n1 && 0 <= j < n2 ==> \separated(nth(l1, i), nth(l2, j)))
    ==> \separated(nth(l1, 0), nth(l2, 0));
*/

/*@ lemma two_sep_first_elem_direct:
  \forall lst_t l1, l2, integer n1, n2;
    n1 >= 1 && n2 >= 1 &&
    (\forall integer i, j; 0 <= i < n1 && 0 <= j < n2 ==> \separated(nth(l1, i), nth(l2, j)))
    ==> \separated(l1, l2);
*/

/*@ lemma nth_zero:
  \forall lst_t l; nth(l, 0) == l;
*/

/*@ lemma nth_cons:
  \forall lst_t x, integer n;
    \valid(x) && n >= 1 ==>
    nth(x, n) == nth(x->cdr, n-1);
*/

/*@ lemma separated_from_tail:
  \forall lst_t x, integer n;
    \valid(x) &&
    n >= 0 &&
    nth(x->cdr, n) == \null &&
    (\forall integer i; 0 <= i < n ==> \separated(x, nth(x->cdr, i))) &&
    separated_list_aux(x->cdr, n)
    ==> separated_list_aux(x, n+1);
*/

/*@ lemma nth_shift:
  \forall lst_t x, integer k;
    \valid(x) && k >= 1 ==> nth(x, k) == nth(x->cdr, k-1);
*/

/*@ lemma separated_list_witness:
  \forall lst_t p, integer n;
    n >= 0 &&
    nth(p, n) == \null &&
    (\forall integer i; 0 <= i < n ==> \valid(nth(p, i))) &&
    separated_list_aux(p, n)
    ==> separated_list(p);
*/


/*@ lemma separated_list_from_two_sep:
  \forall lst_t x, y, integer n;
  \valid(x) && x->cdr == y && n >= 0 &&
  nth(y, n) == \null &&
  (\forall integer i; 0 <= i < n ==> \valid(nth(y, i))) &&
  separated_list_aux(y, n) &&
  (\forall integer i; 0 <= i < n ==> \separated(x, nth(y, i)))
  ==> separated_list(x);
*/

/*@ lemma separated_preserved{L1, L2}:
  \forall lst_t a, b;
    \separated(a, b) &&
    \valid{L2}(a) && \valid{L2}(b)
    ==> \separated(a, b);
*/

/*@ lemma two_sep_gives_x_sep_from_y{L}:
  \forall lst_t x, y, integer n1, n2;
    n1 >= 1 && n2 >= 0 &&
    nth{L}(x, n1) == \null &&
    nth{L}(y, n2) == \null &&
    (\forall integer i, j; 0 <= i < n1 && 0 <= j < n2 ==> \separated(nth{L}(x, i), nth{L}(y, j)))
    ==> (\forall integer j; 0 <= j < n2 ==> \separated(x, nth{L}(y, j)));
*/

/*@ lemma nth_succ{L}:
  \forall lst_t x, integer n;
    \valid{L}(x) && n >= 0
    ==> nth{L}(x, n+1) == nth{L}(\at(x->cdr, L), n);
*/

/*@ lemma nth_cdr_eq{L}:
  \forall lst_t x, y, integer n;
    \valid{L}(x) &&
    \at(x->cdr, L) == y &&
    n >= 0
    ==> nth{L}(x, n+1) == nth{L}(y, n);
*/

/*@ lemma cons_null_at{L}:
  \forall lst_t x, y, integer n;
    \valid{L}(x) &&
    \at(x->cdr, L) == y &&
    n >= 0 &&
    nth{L}(y, n) == \null
    ==> nth{L}(x, n+1) == \null;
*/

/*@ lemma cons_all_valid{L}:
  \forall lst_t x, y, integer n;
    \valid{L}(x) &&
    \at(x->cdr, L) == y &&
    n >= 0 &&
    (\forall integer i; 0 <= i < n ==> \valid{L}(nth{L}(y, i)))
    ==> (\forall integer i; 0 <= i < n+1 ==> \valid{L}(nth{L}(x, i)));
*/

/*@ lemma cons_separated_aux{L}:
  \forall lst_t x, y, integer n;
    \valid{L}(x) &&
    \at(x->cdr, L) == y &&
    n >= 0 &&
    separated_list_aux{L}(y, n) &&
    (\forall integer i; 0 <= i < n ==> \separated(x, nth{L}(y, i)))
    ==> separated_list_aux{L}(x, n+1);
*/

/*@ lemma still_separated_final{L}:
  \forall lst_t x, y, integer n;
    n >= 0 &&
    \valid{L}(x) &&
    \at(x->cdr, L) == y &&
    nth{L}(y, n) == \null &&
    (\forall integer i; 0 <= i < n ==> \valid{L}(nth{L}(y, i))) &&
    separated_list_aux{L}(y, n) &&
    (\forall integer i; 0 <= i < n ==> \separated(x, nth{L}(y, i)))
    ==> separated_list{L}(x);
*/


/*@ lemma still_valid_explicit{L}:
  \forall lst_t x, y;
    \valid{L}(x) &&
    \at(x->cdr, L) == y &&
    separated_list{L}(x) &&
    valid_list{L}(y)
    ==> valid_list{L}(x);
*/



// /*@ lemma good_until_length:
//   \forall lst_t l; valid_list(l) ==> \forall integer i; 0 <= i < length(l) ==> \valid(nth(l, i));
// */

/*@ predicate reachable(lst_t root, lst_t p) =
  \exists integer i; 0 <= i < length(root) && nth(root, i) == p;
*/

/*@ predicate cdrs_did_not_change{L1,L2}(lst_t l) =
  valid_list{L1}(l) &&
  valid_list{L2}(l) &&
  length{L1}(l) == length{L2}(l) &&
  (\forall lst_t p;
    reachable{L1}(l, p) && p != \null ==>
    \at(p->cdr, L1) == \at(p->cdr, L2));
*/

/*@ predicate only_cars_changed{L1,L2}(lst_t *cells, integer count) =
  \forall integer i; 0 <= i < count ==>
    \at(cells[i]->cdr, L1) == \at(cells[i]->cdr, L2);
*/


// /*@
//     predicate frame_list{L1, L2}(list_shape ls)=
//     only_cars_changed{L1, L2}(ls.cells, ls.count) &&
//         \forall integer i; 0 <= i < ls.count ==> \valid{L1}(\at(ls.cells[i], L1)) &&
//    \at(ls.cells[i], L2) &&
//         \forall lst_t p; (\forall integer i; 0 <= i < ls.count ==> p !=
//             \at(ls.cells[i], L1)) ==>
//                 \at(p->car, L1) == \at(p->car, L2) &&
//                 \at(p->cdr, L1) == \at(p->cdr, L2);
//  */

/*
(** the contents of the `car` fields in ls[k..size-k[ have been swapped *)
predicate reversal (ls: list_shape) (m1 m2: mem) (k: int) =
  forall i. 0 <= i < ls.size ->
    (i < k \/ ls.size - k <= i ->
      m1.mcar (ls.cell i) = m2.mcar (ls.cell i)) /\
    (k <= i < ls.size - k ->
      m1.mcar (ls.cell i) = m2.mcar (ls.cell (ls.size - 1 - i)))
*/


/*
 *
 * type tree_shape = {
 *    cell : int -> loc;  (* location *)
 *    clmd : int -> int;  (* left-most descendant *)
 *    clst : int -> int;  (* left subtree *)
 *    crst : int -> int;  (* right subtree *)
 *    crmd : int -> int;  (* right-most descendant *)
 *    size : int;
 *  }
 *
 *
 *  invariant { 0 <= size }
 *  invariant {
 *    forall i. 0 <= i < size -> cell i <> null }
 *  invariant {
 *    forall i. 0 <= i < size ->
 *      forall j. 0 <= j < size -> i <> j -> cell i <> cell j }
 *  invariant {
 *    forall i. 0 <= i < size ->
 *      0 <= clmd i = clmd (clst i) <= clst i <=
 *        i <= crst i <= crmd (crst i) = crmd i < size }
 *  invariant {
 *    forall i. 0 <= i < size -> clst i = i -> clmd i = i }
 *  invariant {
 *    forall i. 0 <= i < size -> crst i = i -> crmd i = i }
 *  invariant {
 *    forall i. 0 <= i < size -> clst i < i -> crmd (clst i) = i-1 }
 *  invariant {
 *    forall i. 0 <= i < size -> crst i > i -> clmd (crst i) = i+1 }
 *
 */

/*@
  predicate wf_lst(tree_shape_t ts, integer lo, integer hi) =
      \forall integer i; 0 <= lo <= i < hi <= ts.size ==>
          (ts.lmdt[i] == ts.lchd[i] && ts.lchd[i] == i &&
           ts.cell[i]->left == \null) ||
          (ts.lchd[i] <= ts.rmdt[ts.lchd[i]] && ts.rmdt[ts.lchd[i]] == i-1 &&
           ts.cell[i]->left == ts.cell[ts.lchd[i]]);
@*/

/*@
  predicate wf_rst(tree_shape_t ts, integer lo, integer hi) =
      \forall integer i; 0 <= lo <= i < hi <= ts.size ==>
          (i == ts.rchd[i] && i == ts.rmdt[i] &&
           ts.cell[i]->right == \null) ||
          (i+1 == ts.lmdt[ts.rchd[i]] && ts.lmdt[ts.rchd[i]] <= ts.rchd[i] &&
           ts.cell[i]->right == ts.cell[ts.rchd[i]]);
@*/

/*@
  predicate warped_rst(tree_shape_t ts, integer lo, integer hi) =
      \forall integer i; 0 <= lo <= i < hi <= ts.size ==>
          (i == ts.rchd[i] && i == ts.rmdt[i] &&
           ((i < ts.size-1 && ts.lmdt[i+1] <= lo &&
             ts.cell[i]->right == ts.cell[i+1]) ||
            (i < ts.size-1 && lo < ts.lmdt[i+1] &&
             ts.cell[i]->right == \null) ||
            (i == ts.size-1 &&
             ts.cell[i]->right == \null))) ||
          (i+1 == ts.lmdt[ts.rchd[i]] && ts.lmdt[ts.rchd[i]] <= ts.rchd[i] &&
           ts.cell[i]->right == ts.cell[ts.rchd[i]]);
@*/

/*@
  predicate frame_tree{L1, L2}(tree_shape_t ts) =
      (\forall integer i; 0 <= i < ts.size ==> \at(ts.cell[i], L1) &&
\at(ts.cell[i], L2)) &&
      (\forall tree_t p; (\forall integer i; 0 <= i < ts.size ==> p !=
\at(ts.cell[i], L1)) ==>
              \at(p->dat, L1) == \at(p->dat, L2) &&
              \at(p->left, L1) == \at(p->left, L2) &&
              \at(p->right, L1) == \at(p->right, L2));
@*/

/*@ predicate valid_tree(tree_t p) =
    p == \null || (\valid(p) && valid_tree(p->left) && valid_tree(p->right));
*/

#endif // INDUCTIVE_H
