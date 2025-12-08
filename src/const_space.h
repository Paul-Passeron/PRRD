#ifndef LIST_SHAPE_H
#define LIST_SHAPE_H
#include "lst.h"
#include "common.h"


typedef struct list_shape_t {
  lst_t *cells;
  size_t count;
} list_shape;

void back_again(lst_t bp, lst_t sp, lst_t np);
void tortoise_hare(
    // list_shape ls, int k,
    lst_t bp, lst_t sp, lst_t fp, lst_t qp);
void value_reverse(lst_t sp, lst_t qp);

#ifdef LIST_SHAPE_IMPL

void value_reverse(lst_t sp, lst_t qp) { tortoise_hare(NULL, sp, sp, qp); }

// TODO: Add requirements
void back_again(
    // list_shape ls, int k,
    lst_t bp, lst_t sp, lst_t np) {
  if (bp == NULL || np == NULL)
    return;

  elt_t tmp = bp->car;
  bp->car = np->car;
  np->car = tmp;

  lst_t nbp = bp->cdr;
  bp->cdr = sp;

  back_again(nbp, bp, np->cdr);
}

// TODO: add requirements
void tortoise_hare(
    // list_shape ls, int k,
    lst_t bp, lst_t sp, lst_t fp, lst_t qp) {
  lst_t nfp;
  if (fp == qp) {
    back_again(/*ls, k, */ bp, sp, sp);
  } else if (sp && fp && (nfp = fp->cdr) && nfp == qp) {
    back_again(/*ls, k,*/ bp, sp, sp->cdr);
  } else {
    nfp = fp->cdr->cdr;
    lst_t nsp = sp->cdr;
    sp->cdr = bp;
    tortoise_hare(/*ls, k + 1, */ sp, nsp, nfp, qp);
  }
}

#endif // LIST_SHAPE_IMPL
#endif // LIST_SHAPE_H
