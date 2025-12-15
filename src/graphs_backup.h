#ifndef GRAPHS_H
#define GRAPHS_H

#include "common.h"
#include "mem.h"
#include <stddef.h>
#include <stdio.h>
#include <stdbool.h>

struct tree {
  struct tree *left;
  struct tree *right;
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

bool wrap(tree_t t);
void visit(tree_t t);
void morris(tree_t t);

#ifdef TREE_IMPL

void visit(tree_t t){
  printf("%d ", t->dat);
}

//@ ghost tre_shape_t morris_t;
//@ ghost int morris_r;
//@ ghost int morris_c;
//@ ghost int morris_k;

void morris(tree_t t){
  tree_t current = t;
  while (current != NULL) {
    if (current->left == NULL) {
        visit(current);
        current = current->right;
    }
    else {
      if (wrap(current)) {
          current = current->left;
      }
      else {
          visit(current);
          //@ ghost
          current = current-> right;
      }
    }
  }
}


bool wrap(tree_t current) {
  if (current->left == NULL){return false;}
    tree_t pred = current->left;
    while (pred->right != NULL && pred->right != current) {
        pred = pred->right;
    }
    if (pred->right == NULL) {
        pred->right = current;
        return true;
    } else {
        pred->right = NULL;
        return false;
    }
}


#endif // TREE_IMPL
#endif // GRAPHS_H
