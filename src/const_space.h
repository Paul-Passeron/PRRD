#ifndef CONST_SPACE_H
#define CONST_SPACE_H
#include "common.h"
#include "lst.h"

void back_again(lst_t bp, lst_t sp, lst_t np);
void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp);
void value_reverse(lst_t sp, lst_t qp);

#ifdef CONST_SPACE_IMPL
#include "predicates.h"

//@ ghost list_shape ls;
//@ ghost int tortoise_hare_k;
//@ ghost int back_again_k;



/*@ requires qp == NULL || \exists int i; 0 <= i < ls.count ==>
 ls.cells[i] == qp;
  @ requires valid_list(sp);
  @ requires valid_list(qp);
  @ requires ls.count < 10E5;
  @ requires \valid(ls.cells[0..ls.count]);
  @ requires listLR(ls, sp, (int)0, (int)ls.count,
 qp);
  @ requires \valid(ls.cells[0..ls.count]);
  @ assigns ls.cells[0..ls.count]->car;
  @ ensures listLR(ls, sp, (int)0, (int)ls.count,
 qp);
  @ ensures \forall int i; 0 <= i < ls.count ==>
    ls.cells[i]->car ==
 \old(ls.cells[ls.count - 1 - i]->car) &&
    ls.cells[i]->cdr ==
 \old(ls.cells[ls.count - 1 - i]->cdr);
 @ ensures frame_list{Old, Post}(ls);
 */
void value_reverse(lst_t sp, lst_t qp) {

  //@ ghost tortoise_hare_k = 0;
  tortoise_hare(NULL, sp, sp, qp);
}

/*@ lemma non_null_valid_list_is_valid:
    \forall lst_t x; x != NULL && valid_list(x) ==> \valid(x);
 */

/*@ lemma non_null_valid_list_next_is_valid:
    \forall lst_t x; x != NULL && valid_list(x) ==> valid_list(x->cdr);
 */



/*@ predicate two_separated(lst_t l1, lst_t l2) =
  \exists integer n1, n2; n1 >= 0 && n2 >= 0 && nth(l1, n1) == \null && 
  \forall integer i, j; n1 > i >= 0 && n2 > j >= 0 ==> \separated(nth(l1, i), nth(l2, j));
*/

/*@ lemma length_of_nonnull_valid:
    \forall lst_t l;
    valid_list(l) && l != \null ==>
      \exists integer n; n >= 1 && nth(l, n) == \null && 
        \forall integer i; i < n ==> \valid(nth(l, i));
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


/*@ lemma still_separated{L1, L2}:
  \forall lst_t x, y; two_separated{L1}(\at(x, L1), \at(y, L1)) && \at(x, L1) == \at(x, L2) && \valid{L2}(x) &&
  valid_list{L1}(\at(y, L1)) && valid_list{L2}(\at(y, L2)) && \at(y, L1) ==
  \at(y, L2) && \at(x->cdr, L2) == \at(y, L2) ==> separated_list{L2}(\at(x, L2));
*/

/*@ lemma still_valid{L1, L2}:
    \forall lst_t x, y; two_separated{L1}(\at(x, L1), \at(y, L1)) && \at(x, L1) == \at(x, L2) && \valid{L2}(x) &&
   valid_list{L1}(\at(y, L1)) && valid_list{L2}(\at(y, L2)) && \at(y, L1) ==
   \at(y, L2) && \at(x->cdr, L2) == \at(y, L2) ==> valid_list{L2}(\at(x, L2));
*/

/*@ requires \valid(ls.cells[0..ls.count]);
  @ requires ((bp == NULL || sp == NULL) && back_again_k >= 0) || back_again_k >
0;
  @ requires bp != NULL && sp != NULL ==> sp != bp;
  @ requires valid_list(sp);
  @ requires valid_list(bp);
  @ requires valid_list(np);
  @ requires ls.count < 10E5;
  @ requires listLR(ls, sp, back_again_k, ls.count,
ls.cells[ls.count]);
  @ requires listRL(ls, bp, back_again_k);
  @ requires back_again_k <= ls.count - back_again_k;
  @ requires ls.cells[ls.count - back_again_k] == np;
  @ requires \valid(ls.cells[0..ls.count]);
  @ decreases back_again_k;
  @ assigns ls.cells[0..ls.count]->car;
  @ ensures listLR(ls, ls.cells[0], (int)0,
(int)(ls.count), ls.cells[ls.count]);
  @ ensures reversal{Old, Post}(ls, (int)0);
  @ ensures frame_list{Old, Post}(ls);
  @ ensures back_again_k >= 0;
*/
void back_again(lst_t bp, lst_t sp, lst_t np) {

  if (bp == NULL || np == NULL)
    return;
  elt_t tmp = bp->car;
  // /*@ assert \valid_list(np); */
  bp->car = np->car;
  /*@ assert valid_list(bp); */
  np->car = tmp;
  /*@ assert valid_list(np); */
  lst_t nbp = bp->cdr;
  /*@ assert valid_list(nbp); */
  /*@ assert valid_list(sp); */
  /*@ assert \valid(bp); */
  /*@ assert valid_or_null(nbp); */
  //@ assert(two_separated(bp, sp)); 
  bp->cdr = sp;
  /*@ assert \valid(bp); */
  /*@ assert valid_list(sp); */
  /*@ assert valid_list(bp); */
  /*@ assert valid_list(nbp); */

  //@ assert back_again_k > 0;
  //@ ghost back_again_k = back_again_k - 1;

  back_again(nbp, bp, np->cdr);
}

/*@ requires fp == NULL ==> qp == NULL;
  @ requires bp != NULL && sp != NULL ==> sp != bp;
  @ requires tortoise_hare_k >= 0;
  @ requires valid_list(bp);
  @ requires valid_list(sp);
  @ requires valid_list(fp);
  @ requires valid_list(qp);
  @ requires ls.count < 10E5;
  @ requires ls.count >= 0;
  @ requires \valid(ls.cells[0..ls.count]);
  @ requires listLR(ls, sp, tortoise_hare_k,
  ls.count, qp);
  @ requires listRL(ls, bp, tortoise_hare_k);
  @ requires 2 * tortoise_hare_k <= ls.count;
  @ requires ls.cells[2*tortoise_hare_k] == fp;
  @ decreases ls.count - tortoise_hare_k;
  @ assigns *ls.cells[0..ls.count];
  @ ensures listLR(ls, ls.cells[0], (int)0,
  ls.count, qp);
  @ ensures reversal{Old, Post}(ls, (int)0);
  @ ensures frame_list{Old, Post}(ls);
  @ ensures ls.count >= 0;
  @ ensures tortoise_hare_k >= 0;
 */

void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp) {
  lst_t nfp;
  if (fp == qp) {
    //@ ghost back_again_k = tortoise_hare_k;
    back_again(bp, sp, sp);
  } else if (sp && fp && (nfp = fp->cdr) && nfp == qp) {
    //@ ghost back_again_k = tortoise_hare_k;
    back_again(bp, sp, sp->cdr);
  } else {
    //@ assert valid_list(nfp);
    //@ assert valid_list(nfp->cdr);
    nfp = fp->cdr->cdr;
    //@ assert valid_list(nfp);
    lst_t nsp = sp->cdr;
    //@ assert valid_list(nsp);
    //@ assert valid_list(bp);
    sp->cdr = bp;
    //@ assert valid_list(sp->cdr);
    //@ assert valid_list(sp);

    //@ ghost tortoise_hare_k = tortoise_hare_k + 1;
    tortoise_hare(sp, nsp, nfp, qp);
  }
}

#endif // CONST_SPACE_IMPL
#endif // CONST_SPACE_H

#include <stdlib.h>


