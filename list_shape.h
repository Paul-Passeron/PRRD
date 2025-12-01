#ifndef LIST_SHAPE_H
#define LIST_SHAPE_H
#include "lst.h"

typedef struct list_shape_t {
  lst *cells;
  size_t count;
} list_shape;

void back_again(lst_t bp, lst_t sp, lst_t np);
void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp);


#ifdef LIST_SHAPE_IMPL

void back_again(lst_t bp, lst_t sp, lst_t np) {
    if (bp == NULL || np == NULL) return;

    elt_t tmp = bp->car;
    bp->car = np->car;
    np->car = tmp;

    lst_t nbp = bp->cdr;
    bp->cdr = sp;

    back_again(nbp, bp, np->cdr);
}

void tortoise_hare(lst_t bp, lst_t sp, lst_t fp, lst_t qp) {
    if (fp == qp) {
        back_again(bp, sp, sp);
        return;
    }

    if (sp && fp && fp->cdr == qp) {
        back_again(bp, sp, sp->cdr);
        return;
    }
    
    if ()

    // TODO: voir si c'est bon de ne rien faire dans le dernier cas

}

#endif // LIST_SHAPE_IMPL
#endif // LIST_SHAPE_H
