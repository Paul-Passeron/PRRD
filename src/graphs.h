#ifndef GRAPHS_H
#define GRAPHS_H

#include "common.h"
#include <stddef.h>
#include <stdio.h>
#include <stdbool.h>
#include "common.h"
#include "predicates.h"

bool warp(tree_t t, tree_t q);
void visit(tree_t t);
void traversal(tree_t t);
void morris(tree_t t);

#ifdef TREE_IMPL
#define MAX_NODES 1024

//@ ghost tree_shape_t morris_t;
//@ ghost int morris_r;
//@ ghost int morris_c;
//@ ghost int morris_k;
//@ ghost int warp_j;

//@ ghost struct tree *trace[MAX_NODES];
//@ ghost int trace_len;




/*@ requires 0 <= warp_j < morris_k;
@ requires q == morris_t.cell[warp_j];
@ requires morris_t.rmdt[warp_j] == warp_j - 1;
@ requires morris_c < morris_k ==> wf_rst(morris_t,0, morris_k);
@ requires morris_c == morris_k ==> (wf_rst(morris_t, 0, morris_k -1)) && (morris_t.cell[morris_k - 1]->right == p);
@ requires morris_t.size <= MAX_NODES;
@ decreases morris_k - warp_j;
@ assigns morris_t, warp_j;
@ ensures \result <==> morris_c != morris_k;
@ ensures morris_c == morris_k ==> morris_t.cell[morris_k-1]->right == \null;
@ ensures morris_c < morris_k ==> morris_t.cell[morris_k-1]->right == p;
@ ensures morris_c < morris_k ==> warped_rst (morris_t, morris_t.lchd[morris_k], morris_k);
@ ensures frame_tree{Old,Post}(morris_t);
*/
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


/*@ requires trace_len == 0;
@ requires 0 <= morris_k <= morris_t.size;
@ requires (morris_t.size == 0 ==> p == \null) && (morris_t.size > 0 ==> morris_k < morris_t.size && morris_t.cell[morris_k] == p && morris_t.lmdt[morris_k] == 0 && morris_t.rmdt[morris_k] == morris_t.size - 1);
@ requires wf_lst (morris_t, 0, morris_t.size);
@ requires wf_rst (morris_t, 0, morris_t.size);
@ requires morris_t.size <= MAX_NODES;
@ assigns morris_t.cell[0 .. morris_t.size-1]->right, trace_len, trace[0 .. MAX_NODES-1];
@ ensures \forall integer i; 0 <= i < morris_t.size ==> morris_t.cell[i]->right == \old(morris_t.cell[i]->right);
@ ensures trace_len == morris_t.size;
@ ensures \forall integer i; 0 <= i < morris_t.size ==> trace[i] == morris_t.cell[i]; 
*/
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

/*@ requires 0 == morris_t.lmdt[morris_r] && morris_r <= morris_t.rmdt[morris_r] && morris_t.rmdt[morris_r] == morris_t.size - 1;
@ requires 0 <= morris_c && morris_c == trace_len && morris_c <= morris_k && morris_k < morris_t.size;
@ requires p == morris_t.cell[morris_k];
@ requires wf_lst(morris_t, 0, morris_t.size);
@ requires \forall integer i; 0 <= i < morris_c ==> trace[i] == morris_t.cell[i];
@ requires morris_c < morris_k ==> (morris_c == morris_t.lmdt[morris_k] && wf_rst(morris_t, 0, morris_k));
@ requires (morris_c == morris_k && morris_t.lchd[morris_k] < morris_k) ==>  (wf_rst(morris_t, 0, morris_k-1) && morris_t.cell[morris_k-1]->right == p);
@ requires (morris_c == morris_k && morris_t.lchd[morris_k] == morris_k) ==> wf_rst(morris_t, 0, morris_k);
@ requires warped_rst(morris_t, morris_k, morris_t.size);
@ requires morris_t.size <= MAX_NODES;
@ decreases (morris_t.size - morris_c) + morris_k; 
@ ensures wf_rst(morris_t, 0, morris_t.size);
@ ensures trace_len == morris_t.size;
@ ensures \forall integer i; 0 <= i <= morris_t.size ==> trace[i] == morris_t.cell[i];
@ ensures frame_tree{Old,Post}(morris_t); */
void morris_visit(tree_t p) {
    if (p->left != NULL && warp(p, p->left)) {
        //@ ghost warp_j = morris_t.lchd[morris_k];
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
          //@ ghost if (morris_t.lchd[morris_k] == morris_k)  {morris_k = morris_k + 1;} else {morris_k = morris_t.lchd[morris_k];}
          morris_visit(p->right);
    }
}



#endif // TREE_IMPL
#endif // GRAPHS_H
