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
  predicate listLR (list_shape ls, lst_t p, int lo, int hi, lst_t q) =
      0 <= lo <= hi <= ls.count &&
      p == ls.cells[lo] &&
      q == ls.cells[hi] &&
      \forall int i; lo <= i < hi ==> ls.cells[i]->cdr == ls.cells[i + 1];
 */

/*@
    predicate listRL (list_shape ls, lst_t p, int k) =
        (k == 0 && p == NULL) ||
        (
            0 < k <= ls.count && p == ls.cells[k - 1] &&
            ls.cells[0]->cdr == NULL &&
            \forall int i; 0 < i < k ==> ls.cells[i]->cdr == ls.cells[i - 1]
        );
 */

/*@
    predicate frame_list{L1, L2}(list_shape ls)=
        \forall int i; 0 <= i < ls.count ==> \at(ls.cells[i], L1) &&
   \at(ls.cells[i], L2) &&
        \forall lst_t p; (\forall int i; 0 <= i < ls.count ==> p !=
            \at(ls.cells[i], L1)) ==>
                \at(p->car, L1) == \at(p->car, L2) &&
                \at(p->cdr, L1) == \at(p->cdr, L2);
 */

/*
(** the contents of the `car` fields in ls[k..size-k[ have been swapped *)
predicate reversal (ls: list_shape) (m1 m2: mem) (k: int) =
  forall i. 0 <= i < ls.size ->
    (i < k \/ ls.size - k <= i ->
      m1.mcar (ls.cell i) = m2.mcar (ls.cell i)) /\
    (k <= i < ls.size - k ->
      m1.mcar (ls.cell i) = m2.mcar (ls.cell (ls.size - 1 - i)))
*/

/*@
    predicate reversal{L1, L2}(list_shape ls, int k) =
        \forall int i; 0 <= i < \at(ls.count, L1) ==> (
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
      \forall integer i; i < n ==> \valid(nth(p, i)) &&
      separated_list_aux(p, n);
*/

/*@ predicate valid_list(lst_t p) =
    p == NULL || (\valid(p) && separated_list(p) && valid_list(p->cdr));
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

#endif // INDUCTIVE_H
