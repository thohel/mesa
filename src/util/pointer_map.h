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

#ifndef _POINTER_MAP_H
#define _POINTER_MAP_H

#include <stdlib.h>
#include <inttypes.h>
#include <stdbool.h>
#include "c99_compat.h"
#include "macros.h"

#ifdef __cplusplus
extern "C" {
#endif

struct map_entry {
   const void *key;
   void *data;
};

struct pointer_map {
   struct map_entry *map;
   uint8_t *metadata;

   const void *deleted_key;

   uint32_t size;
   uint32_t max_entries;
   uint32_t entries;
   uint32_t deleted_entries;
};

struct pointer_map *
_mesa_pointer_map_create(void *mem_ctx);

void _mesa_pointer_map_destroy(struct pointer_map *map,
                               void (*delete_function)(struct map_entry *entry));

void _mesa_pointer_map_clear(struct pointer_map *map);

static inline uint32_t _mesa_pointer_map_num_entries(struct pointer_map *map)
{
   return map->entries;
}

struct map_entry *
_mesa_pointer_map_insert(struct pointer_map *map, const void *key, void *data);

struct map_entry *
_mesa_pointer_map_search(struct pointer_map *map, const void *key);

void _mesa_pointer_map_remove(struct pointer_map *map,
                             struct map_entry *entry);

struct map_entry *
_mesa_pointer_map_next_entry(struct pointer_map *map,
                             struct map_entry *entry);

/**
 * This foreach function is safe against deletion (which just replaces
 * an entry's data with the deleted marker), but not against insertion
 * (which may rehash the table, making entry a dangling pointer).
 */
#define _mesa_pointer_map_foreach(map, entry)                   \
   for (entry = _mesa_pointer_map_next_entry(map, NULL);  \
        entry != NULL;                                  \
        entry = _mesa_pointer_map_next_entry(map, entry))

static inline void
_mesa_pointer_map_call_foreach(struct pointer_map *pm,
                               void (*callback)(const void *key,
                                                void *data,
                                                void *closure),
                               void *closure)
{
   struct map_entry *entry;

   _mesa_pointer_map_foreach(pm, entry)
      callback(entry->key, entry->data, closure);
}

#ifdef __cplusplus
} /* extern C */
#endif

#endif /* _POINTER_MAP_H */
