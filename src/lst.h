#ifndef LST_H
#define LST_H

#include "common.h"
#include <stddef.h>


void print_lst(lst_t l);
lst_t list_reversal(lst_t l);
lst_t build_lst(elt_t *elts, size_t count);

#ifdef LST_IMPL
#include "mem.h"

#include <stdlib.h>

void print_lst(lst_t l) {
  bool first = true;
  printf("[");
  while (l) {
    if (!first) {
      printf(", ");
    }
    first = false;
    printf("%d", l->car);
    l = l->cdr;
  }
  printf("]");
}

lst_t aux(lst_t r, lst_t l) {
  if (!l) {
    return r;
  } else {
    lst_t n = l->cdr;
    l->cdr = r;
    return aux(l, n);
  }
}

lst_t list_reversal(lst_t l) { return aux(NULL, l); }

lst_t build_lst(elt_t *elts, size_t count) {
    reset_mem();
  lst_t head = NULL;
  for (int i = count - 1; i >= 0; --i) {
    lst_t new_head = (lst_t)malloc(sizeof(struct lst));
    if (!new_head) {
      exit(1);
    }
    add_to_mem(new_head, elts[i], head);
    new_head->car = elts[i];
    new_head->cdr = head;
    head = new_head;
  }
  return head;
}

#endif // LST_IMPL
#endif // LST_H
