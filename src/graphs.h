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
    tree_t *cell; //tree node
    int *lchd; // left child
    int *rchd; // right child
    int *lmdt; // leftmost descendant
    int *rmdt; // rightmost descendant
    int size;
}tree_shape_t;


bool warp(tree_t t, tree_t q);
void visit(tree_t t);
void traversal(tree_t t);
void morris(tree_t t);

#ifdef TREE_IMPL

//@ ghost tree_shape_t morris_t;
//@ ghost int morris_r;
//@ ghost int morris_c;
//@ ghost int morris_k;
//@ ghost int  warp_j;


bool warp(tree_t p, tree_t q) {
    if (q->right == NULL) {
        q->right = p;
        return true;
    }
    if (q->right == p) {
        q->right = NULL;
        return false;
    }
    //@ ghost warp_j = morris_t.rchd[warp_j];
    return warp(p, q->right);
}

void traversal(tree_t p) {
    if (p != NULL)
    //@ ghost morris_t = morris_t;
    //@ ghost morris_r = morris_k;
    //@ ghost morris_c = 0;
    //@ ghost morris_k = morris_k;
        morris(p);
}

void visit(tree_t p) {
    printf("%d ", p->dat);
}


void morris_visit(tree_t p) {
      //@ ghost warp_j = morris_t.lchd[morris_k];
    if (p->left != NULL && warp(p, p->left)) {
        //@ ghost morris_t = morris_t;
        //@ ghost morris_r = morris_r;
        //@ ghost morris_c = morris_c;
        //@ ghost morris_k = morris_t.lchd[morris_k];
        morris_visit(p->left);
    } else {
        visit(p);
        if (p->right != NULL)
          //@ ghost morris_t = morris_t;
          //@ ghost morris_r = morris_r;
          //@ ghost morris_c = morris_c + 1;
          //@ ghost if (morris_t.lchd[morris_k] = morris_k)  {morris_k = morris_k + 1;} else {morris_k = morris_t.lchd[morris_k];}
          morris_visit(p->right);
    }
}
                               


#endif // TREE_IMPL
#endif // GRAPHS_H
