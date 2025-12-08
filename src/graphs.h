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


void morris(tree t){
  tree *current = t;
  while (current != NULL) {
    if (current->left == NULL) {
        printf("%d ", current->dat);  
        current = current->right;  
    }
    if (p->left == NULL) {
      visit(p);
      morris(p->right);  
    }
    else {
        if (warp(p)) {
            morris(p->left); 
        }
        else {
            visit(p);
            morris(p->right);
        }
    }
  }
}


bool wrap (tree t){
  tree *current = t;
  tree *pred = current->left;
   while (pred->right != NULL && pred->right != current) {
        pred = pred->right;
      } 
      if (pred->right == NULL){
      pred->right = current;
      return true;
      }
      else {
        pred->right = NULL;
        return false;
      }
}

void visit(tree t ){
  printf("%d ", t->data);
}


#endif // GRAPHS_H
