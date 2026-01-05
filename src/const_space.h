#ifndef CONST_SPACE_H
#define CONST_SPACE_H
#include "common.h"
#include "lst.h"

void back_again(lst_t bp, lst_t sp, lst_t np);
void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp);
void value_reverse(lst_t sp, lst_t qp);

#ifdef CONST_SPACE_IMPL
#include "predicates.h"

//@ ghost int tortoise_hare_k;
//@ ghost list_shape tortoise_hare_ls;
//
//@ ghost int back_again_k;
//@ ghost list_shape back_again_ls;
//
//@ ghost list_shape value_reverse_ls;

/*@ requires qp == NULL || \exists int i; 0 <= i < value_reverse_ls.count ==>
 value_reverse_ls.cells[i] == qp;
  @ requires valid_list(sp);
  @ requires valid_list(qp);
  @ requires value_reverse_ls.count < 10E5;
  @ requires \valid(value_reverse_ls.cells[0..value_reverse_ls.count]);
  @ requires listLR(value_reverse_ls, sp, (int)0, (int)value_reverse_ls.count,
 qp);
  @ assigns value_reverse_ls.cells[0..value_reverse_ls.count]->car;
  @ ensures listLR(value_reverse_ls, sp, (int)0, (int)value_reverse_ls.count,
 qp);
  @ ensures \forall int i; 0 <= i < value_reverse_ls.count ==>
    value_reverse_ls.cells[i]->car ==
 \old(value_reverse_ls.cells[value_reverse_ls.count - 1 - i]->car) &&
    value_reverse_ls.cells[i]->cdr ==
 \old(value_reverse_ls.cells[value_reverse_ls.count - 1 - i]->cdr);
 @ ensures frame_list{Old, Post}(value_reverse_ls);
 */
void value_reverse(lst_t sp, lst_t qp) {
  //@ ghost tortoise_hare_ls = value_reverse_ls;
  //@ ghost tortoise_hare_k = 0;
  tortoise_hare(NULL, sp, sp, qp);
}

/*@ lemma non_null_valid_list_is_valid:
    \forall lst_t x; x != NULL && valid_list(x) ==> \valid(x);
 */

 /*@ lemma non_null_valid_list_next_is_valid:
     \forall lst_t x; x != NULL && valid_list(x) ==> valid_list(x->cdr);
  */


/*@ lemma still_valid{L1, L2}:
    \forall lst_t x, y; \at(x, L1) == \at(x, L2) && \valid{L2}(x) && valid_list{L1}(\at(y, L1)) && valid_list{L2}(\at(y, L2)) && \at(y, L1) ==
   \at(y, L2) && \at(x->cdr, L2) == \at(y, L2) ==> valid_list{L2}(\at(x, L2));
*/

/*@ requires \valid(back_again_ls.cells[0..back_again_ls.count]);
  @ requires valid_list(sp);
  @ requires valid_list(bp);
  @ requires valid_list(np);
  @ requires back_again_ls.count < 10E5;
  @ requires listLR(back_again_ls, sp, back_again_k, back_again_ls.count,
back_again_ls.cells[back_again_ls.count]);
  @ requires listRL(back_again_ls, bp, back_again_k);
  @ requires back_again_k <= back_again_ls.count - back_again_k;
  @ requires back_again_ls.cells[back_again_ls.count - back_again_k] == np;
  @ decreases back_again_k;
  @ assigns back_again_ls.cells[0..back_again_ls.count]->car;
  @ ensures listLR(back_again_ls, back_again_ls.cells[0], (int)0,
(int)(back_again_ls.count), back_again_ls.cells[back_again_ls.count]);
  @ ensures reversal{Old, Post}(back_again_ls, (int)0);
  @ ensures frame_list{Old, Post}(back_again_ls);
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
  bp->cdr = sp;
  /*@ assert valid_list(bp); */
  /*@ assert valid_list(nbp); */

  //@ ghost back_again_k = back_again_k - 1;
  //@ ghost back_again_ls = back_again_ls;
  back_again(nbp, bp, np->cdr);
}

/*@ requires fp == NULL ==> qp == NULL;
  @ requires valid_list(bp);
  @ requires valid_list(sp);
  @ requires valid_list(fp);
  @ requires valid_list(qp);
  @ requires tortoise_hare_ls.count < 10E5;
  @ requires tortoise_hare_ls.count >= 0;
  @ requires \valid(tortoise_hare_ls.cells[0..tortoise_hare_ls.count]);
  @ requires listLR(tortoise_hare_ls, sp, tortoise_hare_k,
  tortoise_hare_ls.count, qp);
  @ requires listRL(tortoise_hare_ls, bp, tortoise_hare_k);
  @ requires 2 * tortoise_hare_k <= tortoise_hare_ls.count;
  @ requires tortoise_hare_ls.cells[2*tortoise_hare_k] == fp;
  @ decreases tortoise_hare_ls.count - tortoise_hare_k;
  @ assigns *tortoise_hare_ls.cells[0..tortoise_hare_ls.count];
  @ ensures listLR(tortoise_hare_ls, tortoise_hare_ls.cells[0], (int)0,
  tortoise_hare_ls.count, qp);
  @ ensures reversal{Old, Post}(tortoise_hare_ls, (int)0);
  @ ensures frame_list{Old, Post}(tortoise_hare_ls);
  @ ensures tortoise_hare_ls.count >= 0;
 */
void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp) {
  lst_t nfp;
  if (fp == qp) {
    //@ghost back_again_k = tortoise_hare_k;
    //@ghost back_again_ls = tortoise_hare_ls;
    back_again(bp, sp, sp);
  } else if (sp && fp && (nfp = fp->cdr) && nfp == qp) {
    //@ghost back_again_k = tortoise_hare_k;
    //@ghost back_again_ls = tortoise_hare_ls;
    back_again(bp, sp, sp->cdr);
  } else {
    nfp = fp->cdr->cdr;
    lst_t nsp = sp->cdr;
    sp->cdr = bp;
    //@ ghost tortoise_hare_ls = tortoise_hare_ls;
    //@ ghost tortoise_hare_k = tortoise_hare_k + 1;
    tortoise_hare(sp, nsp, nfp, qp);
  }
}

#endif // CONST_SPACE_IMPL
#endif // CONST_SPACE_H
