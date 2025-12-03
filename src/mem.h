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
  size_t cap;
} ptr_to_elt_map;

typedef struct ptr_to_ptr_map {
  size_t count;
  ptr_ptr_tuple *items;
  size_t cap;
} ptr_to_ptr_map;

typedef struct mem_t {
  ptr_to_elt_map mcar;
  ptr_to_ptr_map mcdr;
} mem_t;

extern mem_t mem;

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
#define da_free(da) FREE((da).items)
#endif // da_free

#ifdef MEM_IMPL

mem_t mem;

#endif // MEM_IMPL

#endif // MEM_H
