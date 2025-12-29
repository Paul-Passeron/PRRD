#ifndef COMMON_H
#define COMMON_H

#include <stddef.h>

typedef int elt_t;

struct lst {
  elt_t car;
  struct lst *cdr;
};

typedef struct lst *lst_t;


typedef struct list_shape_t {
  lst_t *cells;
  int count;
} list_shape;

struct tree {
  struct tree *left;
  struct tree *right;
  elt_t dat;
};


typedef struct tree *tree_t;

typedef struct tree_shape_t {
    tree_t *cell; //tree node
    int *lchd; // left child
    int *rchd; // right child
    int *lmdt; // leftmost descendant
    int *rmdt; // rightmost descendant
    int size;
}tree_shape_t;

#endif // COMMON_H
