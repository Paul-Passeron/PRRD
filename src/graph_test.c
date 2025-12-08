#include <stdlib.h>
#include <time.h>
#define TREE_IMPL
#include "graphs.h"



tree_t sample_tree(int depth) {
    if (depth == 0) { return NULL; }
    // srand(time(NULL));
    int value = rand() % 255;
    tree_t res = malloc(sizeof(struct tree));
    *res = (struct tree){0};
    res->dat = value;
    // Left child
    if (rand() % 2  == 0) {
        res->left = sample_tree(depth - 1);
    }
    if (rand() % 2  == 0) {
        res->right = sample_tree(depth - 1);
    }

    return res;
}
