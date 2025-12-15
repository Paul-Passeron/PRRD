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
    predicate frame{L1, L2}(list_shape ls)=
        \forall int i; 0 <= i < ls.count ==> \at(ls.cells[i], L1) && \at(ls.cells[i], L2) &&
        \forall lst_t p; (\forall int i; 0 <= i < ls.count ==> p !=
            \at(ls.cells[i], L1)) ==>
                \at(p->car, L1) == \at(p->car, L2) &&
                \at(p->cdr, L1) == \at(p->cdr, L2);
 */

#endif // INDUCTIVE_H
