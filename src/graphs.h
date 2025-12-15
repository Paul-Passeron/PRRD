#ifndef GRAPHS_H
#define GRAPHS_H

#include "common.h"
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

bool warp(tree_t t, tree_t q);
void visit(tree_t t);
void traversal(tree_t t);
void morris(tree_t t);

#ifdef TREE_IMPL

//@ ghost tre_shape_t morris_t;
//@ ghost int morris_r;
//@ ghost int morris_c;
//@ ghost int morris_k;

bool warp(tree_t t, tree_t q) {
    if (q->right == NULL) {
        q->right = t;
        return true;
    }
    if (q->right == t) {
        q->right = NULL;
        return false;
    }
    return warp(t, q->right);
}

void traversal(tree_t t) {
    if (t != NULL)
        morris(t);
}

void visit(tree_t t) {
    printf("%d ", t->dat);
}

void morris(tree_t t) {
    if (t->left != NULL && warp(t, t->left)) {
        morris(t->left);
    } else {
        visit(t);
        if (t->right != NULL)
            morris(t->right);
    }
}



#endif // TREE_IMPL
#endif // GRAPHS_H
