#ifndef GRAPHS_H
#define GRAPHS_H

#include "common.h"

struct tree {
  struct tree *left;
  struct tree *rigth;
  elt_t dat;
};

typedef struct tree *tree_t;

typedef struct tree_shape_t {
    tree_t *cell;
    int *lchd;
    int *rchd;
    int *lmdt;
    int *rmdt;
    int size;
}tree_shape_t;

#endif // GRAPHS_H
