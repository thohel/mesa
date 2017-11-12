/*
 * Copyright © 2017 Thomas Helland
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice (including the next
 * paragraph) shall be included in all copies or substantial portions of the
 * Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 *
 */
#ifndef _POINTER_SET_H
#define _POINTER_SET_H

#include <stdlib.h>
#include <inttypes.h>
#include <stdbool.h>
#include "c99_compat.h"
#include "macros.h"

#ifdef __cplusplus
extern "C" {
#endif

struct pointer_set_entry {
   const void *key;
};

struct pointer_set {
   struct pointer_set_entry *keys;

   uint32_t size;
   uint32_t max_entries;
   uint32_t entries;
   uint32_t deleted_entries;
};

struct pointer_set *
_mesa_pointer_set_create(void *mem_ctx);

void _mesa_pointer_set_destroy(struct pointer_set *set,
      void (*delete_function)(struct pointer_set_entry *entry));

void _mesa_pointer_set_clear(struct pointer_set *set);

static inline uint32_t _mesa_pointer_set_num_entries(struct pointer_set *set)
{
   return set->entries;
}

struct pointer_set_entry *
_mesa_pointer_set_insert(struct pointer_set *set, const void *key);

struct pointer_set_entry *
_mesa_pointer_set_search(struct pointer_set *set, const void *key);

void _mesa_pointer_set_remove(struct pointer_set *set,
                             struct pointer_set_entry *entry);

struct pointer_set_entry *
_mesa_pointer_set_next_entry(struct pointer_set *set,
                             struct pointer_set_entry *entry);

/**
 * This foreach function is safe against deletion (which just replaces
 * an entry's data with the deleted marker), but not against insertion
 * (which may rehash the table, making entry a dangling pointer).
 */
#define _mesa_pointer_set_foreach(set, entry)                   \
   for (entry = _mesa_pointer_set_next_entry(set, NULL);  \
        entry != NULL;                                  \
        entry = _mesa_pointer_set_next_entry(set, entry))

#ifdef __cplusplus
} /* extern C */
#endif

#endif /* _POINTER_SET_H */
