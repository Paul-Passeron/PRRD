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
void morris_visit(tree_t t);

#ifdef TREE_IMPL
#define MAX_NODES 1024

//@ ghost tree_shape_t morris_t;
//@ ghost int morris_r;
//@ ghost int morris_c;
//@ ghost int morris_k;
//@ ghost int warp_j;

//@ ghost struct tree *trace[MAX_NODES];


/*@ requires 0 <= warp_j < morris_k;
@ requires q == morris_t.cell[warp_j];
@ requires morris_t.rmdt[warp_j] == morris_k - 1;
@ requires morris_c < morris_k ==> wf_rst(morris_t,0, morris_k);
@ requires morris_c == morris_k ==> (wf_rst(morris_t, 0, morris_k -1)) && (morris_t.cell[morris_k - 1]->right == p);
@ requires morris_t.size <= MAX_NODES;
@ requires valid_tree(p);
@ requires \valid(q);
@ decreases morris_k - warp_j;
@ assigns warp_j, morris_t.cell[0 .. morris_t.size-1]->right 
\from warp_j, morris_k, morris_t.rchd[0 .. morris_t.size-1], 
morris_t.cell[0 .. morris_t.size-1], p, q, 
morris_t.cell[0 .. morris_t.size-1]->right;
@ ensures \result <==> morris_c != morris_k;
@ ensures morris_c == morris_k ==> morris_t.cell[morris_k-1]->right == \null;
@ ensures morris_c < morris_k ==> morris_t.cell[morris_k-1]->right == p;
@ ensures morris_c < morris_k ==> warped_rst(morris_t, morris_t.lchd[morris_k], morris_k);
@ ensures frame_tree{Old,Post}(morris_t);
*/
bool warp(tree_t p, tree_t q) {
    //@ assert \valid(q);
    //@ assert q == morris_t.cell[warp_j];
    if (q->right == NULL) {
        //@ assert warp_j == morris_t.rmdt[warp_j];
        q->right = p;
        //@ assert q->right == p;
        return true;
    }
    if (q->right == p) {
        //@ assert warp_j == morris_t.rmdt[warp_j];
        q->right = NULL;
        //@ assert q->right == \null;
        return false;
    }
    //@ assert q->right != \null && q->right != p;
    //@ ghost warp_j = morris_t.rchd[warp_j];
    //@ assert warp_j < morris_k;
    return warp(p, q->right);
}


/*@ requires morris_c == 0;
@ requires 0 <= warp_j < morris_k;
@ requires 0 <= morris_k <= morris_t.size;
@ requires (morris_t.size == 0 ==> p == \null) && (morris_t.size > 0 ==> morris_k < morris_t.size && morris_t.cell[morris_k] == p && morris_t.lmdt[morris_k] == 0 && morris_t.rmdt[morris_k] == morris_t.size - 1);
@ requires wf_lst (morris_t, 0, morris_t.size);
@ requires wf_rst (morris_t, 0, morris_t.size);
@ requires morris_t.size <= MAX_NODES;
@ requires valid_tree(p);
@ assigns morris_t.cell[0 .. morris_t.size-1]->right, morris_c, trace[0 .. MAX_NODES-1] 
\from p, morris_t.size, morris_t.cell[0 .. morris_t.size-1], 
morris_t.lchd[0 .. morris_t.size-1], morris_t.rchd[0 .. morris_t.size-1], 
morris_t.lmdt[0 .. morris_t.size-1], morris_t.rmdt[0 .. morris_t.size-1], 
morris_t.cell[0 .. morris_t.size-1]->left,
morris_t.cell[0 .. morris_t.size-1]->right,
morris_c, trace[0 .. MAX_NODES-1];
@ ensures \forall integer i; 0 <= i < morris_t.size ==> morris_t.cell[i]->right == \old(morris_t.cell[i]->right);
@ ensures morris_c == morris_t.size;
@ ensures \forall integer i; 0 <= i < morris_t.size ==> trace[i] == morris_t.cell[i]; 
*/
void traversal(tree_t p) {
    //@ ghost morris_t = morris_t;
    //@ ghost morris_r = morris_k;
    //@ ghost morris_c = 0;
    //@ ghost morris_k = morris_k;
    if (p != NULL)
        morris_visit(p);
}


/*@requires morris_c < 1024;
@ requires \valid(p);
@assigns trace[morris_c], morris_c \from morris_c, p;
@ensures morris_c == \old(morris_c) + 1;
@ensures trace[\old(morris_c)] == p;
*/
void visit(tree_t p) {
    //@ ghost trace[morris_c] = p;
    //@ ghost morris_c++;
    //@ assert valid_tree(p);
    printf("%d ", p->dat);
}

/*@ requires 0 == morris_t.lmdt[morris_r] && morris_r <= morris_t.rmdt[morris_r] && morris_t.rmdt[morris_r] == morris_t.size - 1;
@ requires 0 <= morris_c && morris_c == morris_c && morris_c <= morris_k && morris_k < morris_t.size;
@ requires p == morris_t.cell[morris_k];
@ requires wf_lst(morris_t, 0, morris_t.size);
@ requires \forall integer i; 0 <= i < morris_c ==> trace[i] == morris_t.cell[i];
@ requires morris_c < morris_k ==> (morris_c == morris_t.lmdt[morris_k] && wf_rst(morris_t, 0, morris_k));
@ requires (morris_c == morris_k && morris_t.lchd[morris_k] < morris_k) ==>  (wf_rst(morris_t, 0, morris_k-1) && morris_t.cell[morris_k-1]->right == p);
@ requires (morris_c == morris_k && morris_t.lchd[morris_k] == morris_k) ==> wf_rst(morris_t, 0, morris_k);
@ requires warped_rst(morris_t, morris_k, morris_t.size);
@ requires morris_t.size <= MAX_NODES;
@ requires \valid(p);
@ requires 0 <= warp_j < morris_k;
@ decreases (morris_t.size - morris_c) + morris_k; 
@ assigns morris_c,trace[0 .. MAX_NODES-1],p->right;
@ ensures wf_rst(morris_t, 0, morris_t.size);
@ ensures morris_c == morris_t.size;
@ ensures \forall integer i; 0 <= i < morris_t.size ==> trace[i] == morris_t.cell[i];
@ ensures frame_tree{Old,Post}(morris_t); */
void morris_visit(tree_t p) {
    //@ assert 0 <= morris_k < morris_t.size;
    //@ assert morris_t.lmdt[morris_k] <= morris_k <= morris_t.rmdt[morris_k];
    if (p->left != NULL && warp(p, p->left)) {
        //@ assert \valid(p->left);
        //@ assert valid_tree(p->left);
        //@ assert morris_c < morris_k ==> wf_rst(morris_t, 0, morris_k);
        //@ assert warped_rst(morris_t, morris_k, morris_t.size);
        //@ assert morris_t.size <= MAX_NODES;
        //@ assert 0 <= warp_j < morris_k;
        //@ assert morris_c < morris_k;
        //@ assert p->left != \null;
        //@ ghost morris_t = morris_t;
        //@ ghost morris_r = morris_r;
        //@ ghost morris_c = morris_c;
        //@ ghost morris_k = morris_t.lchd[morris_k];
        morris_visit(p->left);
    } else {
        //@ assert morris_c < 1024;
        visit(p);
        if (p->right != NULL)
        //@ assert \valid(p->right);
        //@ assert valid_tree(p->right);
        //@ assert morris_c <= morris_t.size;
        //@ assert warped_rst(morris_t, morris_k, morris_t.size);
        //@ assert p->right != NULL;
        //@ ghost morris_t = morris_t;
        //@ ghost morris_r = morris_r;
        //@ ghost morris_c = morris_c + 1;
        //@ ghost if (morris_t.rchd[morris_k] == morris_k)  {morris_k = morris_k + 1;} else {morris_k = morris_t.lchd[morris_k];}
        morris_visit(p->right);
    }
}


#endif // TREE_IMPL
#endif // GRAPHS_H
