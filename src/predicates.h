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
  predicate wf_lst{L}(tree_shape t, mem m, integer lo, integer hi) =
    \forall integer i;
      lo <= i < hi && 0 <= lo && hi <= t.size ==>
        (( t.clmd(i) == i &&
            t.clst(i) == i &&
            \at(m.mlst(t.cell(i)), L) == \null )
        ||
          ( t.clst(i) <= t.crmd(t.clst(i)) &&
            t.crmd(t.clst(i)) == i-1 &&
            \at(m.mlst(t.cell(i)), L) == t.cell(t.clst(i)) ));
*/


/*@
  predicate wf_rst{L}(tree_shape t, mem m, integer lo, integer hi) =
    \forall integer i;
      lo <= i < hi && 0 <= lo && hi <= t.size ==>
        (( t.crst(i) == i &&
            t.crmd(i) == i &&
            \at(m.mrst(t.cell(i)), L) == \null )
        ||
          ( t.clmd(t.crst(i)) == i+1 &&
            t.clmd(t.crst(i)) <= t.crst(i) &&
            \at(m.mrst(t.cell(i)), L) == t.cell(t.crst(i)) ));
*/

/*@
  predicate warped_rst{L}(tree_shape t, mem m, integer lo, integer hi) =
    \forall integer i;
      lo <= i < hi && 0 <= lo && hi <= t.size ==>
        (( t.crst(i) == i &&
            t.crmd(i) == i &&
            (( i < t.size-1 &&
                t.clmd(i+1) <= lo &&
                \at(m.mrst(t.cell(i)), L) == t.cell(i+1) )
            ||
              ( i < t.size-1 &&
                lo < t.clmd(i+1) &&
                \at(m.mrst(t.cell(i)), L) == \null )
            ||
              ( i == t.size-1 &&
                \at(m.mrst(t.cell(i)), L) == \null )))
        ||
          ( t.clmd(t.crst(i)) == i+1 &&
            t.clmd(t.crst(i)) <= t.crst(i) &&
            \at(m.mrst(t.cell(i)), L) == t.cell(t.crst(i)) ));
*/

/*@
  predicate frame{L1,L2}(tree_shape t, mem m1, mem m2) =
    \forall loc p;
      (\forall integer i; 0 <= i < t.size ==> p != \at(t.cell(i),L1)) ==>
        \at(m1.mdat(p),L1) == \at(m2.mdat(p),L2) &&
        \at(m1.mlst(p),L1) == \at(m2.mlst(p),L2) &&
        \at(m1.mrst(p),L1) == \at(m2.mrst(p),L2);
*/


#endif // INDUCTIVE_H
