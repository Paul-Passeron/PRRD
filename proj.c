#include <stdbool.h>
#include <stdio.h>

#define LST_IMPL
#include "lst.h"

#define LIST_SHAPE_IMPL
#include "list_shape.h"

// Sect.2

int main(void) {
  elt_t elements[] = {1, 2, 3, 4, 5, 6};
  size_t count = sizeof(elements) / sizeof(elt_t);

  lst_t l = build_lst(elements, count);
  printf("l = ");
  print_lst(l);
  printf("\n");
  lst_t m = list_reversal(l);
  printf("m = ");
  print_lst(m);
  printf("\n");

  l = build_lst(elements, count);
  printf("l = ");
  print_lst(l);
  printf("\n");

  value_reverse(l, NULL);
  printf("l = ");
  print_lst(l);
  printf("\n");


  return 0;
}
