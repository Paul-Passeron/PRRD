#ifndef MEM_H
#define MEM_H

#include "lst.h"

typedef struct ptr_elem_tuple {
  lst_t ptr;
  elt_t elt;
} ptr_elem_tuple;

typedef struct ptr_ptr_tuple {
  lst_t ptr;
  lst_t assoc;
} ptr_ptr_tuple;

typedef struct ptr_to_elt_map {
  size_t count;
  ptr_elem_tuple *items;
  size_t capacity;
} ptr_to_elt_map;

typedef struct ptr_to_ptr_map {
  size_t count;
  ptr_ptr_tuple *items;
  size_t capacity;
} ptr_to_ptr_map;

typedef struct mem_t {
  ptr_to_elt_map mcar;
  ptr_to_ptr_map mcdr;
} mem_t;

extern mem_t mem;

void add_to_mem(void *ptr, elt_t car, void *cdr);
void reset_mem(void);

#include <assert.h>
#include <stdlib.h>

#ifndef FREE
#define FREE free
#endif

#ifndef REALLOC
#define REALLOC realloc
#endif

#ifndef ASSERT
#define ASSERT assert
#endif

#ifndef DA_INIT_CAP
#define DA_INIT_CAP 8
#endif // DA_INIT_CAP

#ifndef da_append
// Append an item to a dynamic array
#define da_append(da, item)                                                    \
  do {                                                                         \
    if ((da)->count >= (da)->capacity) {                                       \
      (da)->capacity = (da)->capacity == 0 ? DA_INIT_CAP : (da)->capacity * 2; \
      (da)->items =                                                            \
          REALLOC((da)->items, (da)->capacity * sizeof(*(da)->items));         \
      ASSERT((da)->items != NULL && "No more memory");                         \
    }                                                                          \
    (da)->items[(da)->count++] = (item);                                       \
  } while (0)
#endif // da_append

#ifndef da_free
#define da_free(da)                                                            \
  do {                                                                         \
    if ((da).items)                                                            \
      FREE((da).items);                                                        \
  } while (0)
#endif // da_free

#ifdef MEM_IMPL

mem_t mem;

void add_to_mem(void *ptr, elt_t car, void *cdr) {
  ptr_elem_tuple elem_tuple = {.ptr = ptr, .elt = car};
  ptr_ptr_tuple ptr_tuple = {.ptr = ptr, .assoc = cdr};
  da_append(&mem.mcar, elem_tuple);
  da_append(&mem.mcdr, ptr_tuple);
}

void reset_mem(void) {
  da_free(mem.mcar);
  da_free(mem.mcdr);
}

#endif // MEM_IMPL

#endif // MEM_H
