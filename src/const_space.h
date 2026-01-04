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

void value_reverse(lst_t sp, lst_t qp) {
  //@ ghost tortoise_hare_ls = value_reverse_ls;
  //@ ghost tortoise_hare_k = 0;
  tortoise_hare(NULL, sp, sp, qp);
}

/*@
    predicate reversal{L1, L2}(list_shape ls, int k) =
        \forall int i; 0 <= i < \at(ls.count, L1) ==> (
            i < k || \at(ls.count, L1) - k <= i ==>
            \at(ls.cells[i]->car, L1) == \at(ls.cells[i]->car, L2) && (
                k <= i < \at(ls.count, L1) - k ==> \at(ls.cells[i]->car, L1) == \at(
                    ls.cells[ls.count - 1 - i]->car
                , L2)
            )
        );

 */

void back_again(lst_t bp, lst_t sp, lst_t np) {
    //@ requires listLR(back_again_ls, sp, back_again_k, back_again_ls.count, back_again_ls.cells[back_again_ls.count-1]);
    //@ requires listRL(back_again_ls, bp, back_again_k);
    //@ requires back_again_k <= back_again_ls.count - back_again_k;
    //@ requires back_again_ls.cells[back_again_ls.count - back_again_k] == np;
    //@ requires reversal{Pre, Post}(back_again_ls, back_again_k);
  if (bp == NULL || np == NULL)
    return;

  elt_t tmp = bp->car;
  bp->car = np->car;
  np->car = tmp;

  lst_t nbp = bp->cdr;
  bp->cdr = sp;

  //@ ghost back_again_k = back_again_k - 1;
  //@ ghost back_again_ls = back_again_ls;
  back_again(nbp, bp, np->cdr);
}

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
