#ifndef COMMON_H
#define COMMON_H

#include <stddef.h>

typedef int elt_t;

struct lst {
  elt_t car;
  struct lst *cdr;
};

typedef struct lst *lst_t;


typedef struct list_shape_t {
  lst_t *cells;
  int count;
} list_shape;

#endif // COMMON_H
