#include <stdlib.h>
#include <time.h>
#define TREE_IMPL
#include "graphs.h"

void print_tree(tree_t t, int depth) {
    if (t == NULL) return;

    print_tree(t->right, depth + 1);

    for (int i = 0; i < depth; i++) printf("│   ");
    if (depth > 0) printf("└-- ");
    printf("%d\n", t->dat);

    print_tree(t->left, depth + 1);
}


tree_t sample_tree(int depth, int min, int max) {
    if (depth == 0 || min > max) return NULL;

    int value = min + rand() % (max - min + 1);
    tree_t res = malloc(sizeof(struct tree));
    *res = (struct tree){0};
    res->dat = value;

    res->left = sample_tree(depth - 1, min, value - 1);   
    res->right = sample_tree(depth - 1, value + 1, max); 

    return res;
}


int main() {
    srand(time(NULL));
    tree_t t = sample_tree(3,0,100);
    printf("Structure de l'arbre :\n");
    print_tree(t, 0);
    printf("\nParcours Morris in-order :\n");
    morris(t);
    printf("\n");
    return 0;
}