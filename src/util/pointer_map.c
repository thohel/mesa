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

/**
 * Implements a linear probing hash table specifically for pointer keys.
 * It uses a separate metadata array for good cache locality when searching.
 * The metadata array is an array of bytes, where the seven LSB stores a hash,
 * and the first bit stores whether the entry is free. An important detail is
 * that the bit being
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>

#include "pointer_map.h"
#include "ralloc.h"
#include "macros.h"

static const uint32_t deleted_key_value;
static const void *deleted_key = &deleted_key_value;

static bool
entry_is_free(const struct map_entry *entry)
{
   return entry->key == NULL;
}

static bool
entry_is_deleted(const struct pointer_map *pm, struct map_entry *entry)
{
   return entry->key == pm->deleted_key;
}

static bool
entry_is_present(const struct pointer_map *pm, struct map_entry *entry)
{
   return entry->key != NULL && entry->key != pm->deleted_key;
}

static inline uint32_t
hash_pointer(const void *pointer)
{
   uintptr_t num = (uintptr_t) pointer;
   return (uint32_t) ((num >> 2) ^ (num >> 6) ^ (num >> 10) ^ (num >> 14));
}

struct pointer_map *
_mesa_pointer_map_create(void *mem_ctx)
{
   struct pointer_map *map;

   map = ralloc(mem_ctx, struct pointer_map);
   if (map == NULL)
      return NULL;

   map->size = 1 << 4;
   map->max_entries = map->size * 0.6;
   map->map = rzalloc_array(map, struct map_entry, map->size);
   map->entries = 0;
   map->deleted_entries = 0;
   map->deleted_key = deleted_key;

   if (map->map == NULL) {
      ralloc_free(map);
      return NULL;
   }

   return map;
}

/**
 * Frees the pointer map.
 */
void
_mesa_pointer_map_destroy(struct pointer_map *map,
                          void (*delete_function)(struct map_entry *entry))
{
   if (!map)
      return;

   if (delete_function) {
      struct map_entry *entry;

      _mesa_pointer_map_foreach(map, entry) {
         delete_function(entry);
      }
   }

   ralloc_free(map);
}

/**
 * Deletes all entries of the given pointer map without deleting the map
 * itself or changing its structure.
 */
void
_mesa_pointer_map_clear(struct pointer_map *map)
{
   memset(map->map, 0, sizeof(struct map_entry) * map->size);
   map->entries = 0;
   map->deleted_entries = 0;
}

/**
 * Finds a hash table entry with the given key and hash of that key.
 *
 * Returns NULL if no entry is found.  Note that the data pointer may be
 * modified by the user.
 */
struct map_entry *
_mesa_pointer_map_search(struct pointer_map *map, const void *key)
{
   uint32_t hash = hash_pointer(key);
   uint32_t start_hash_address = hash & (map->size - 1);
   uint32_t hash_address = start_hash_address;

   struct map_entry *entry = NULL;
   do {
      entry = map->map + hash_address;

      if (entry_is_free(entry)) {
         return NULL;
      } else if (entry->key == key) {
         return entry;
      }

      hash_address = (hash_address + 1) & (map->size - 1);
   } while (hash_address != start_hash_address);

   return NULL;
}

static void
_mesa_pointer_map_rehash(struct pointer_map *map, unsigned new_size)
{
   struct pointer_map old_map;
   struct map_entry *map_entries, *entry;

   old_map = *map;

   map->size = new_size;
   map->max_entries = map->size*0.6;
   
   map_entries = rzalloc_array(map, struct map_entry, map->size);
   if (map_entries == NULL)
      return;

   map->map = map_entries;
   map->entries = 0;
   map->deleted_entries = 0;

   _mesa_pointer_map_foreach(&old_map, entry) {
      _mesa_pointer_map_insert(map, entry->key, entry->data);
   }

   ralloc_free(old_map.map);
}

/**
 * Inserts the key into the table. Note that insertion may rearrange the
 * table on a resize or rehash, so previously found hash_entries are no
 * longer valid after this function.
 */
struct map_entry *
_mesa_pointer_map_insert(struct pointer_map *map, const void *key, void *data)
{
   uint32_t start_hash_address, hash_address, hash;
   struct map_entry *available_entry = NULL;
   assert(key != NULL);

   if (map->entries >= map->max_entries) {
      _mesa_pointer_map_rehash(map, map->size * 2);
   } else if (map->deleted_entries + map->entries >= map->max_entries) {
      _mesa_pointer_map_rehash(map, map->size);
   }

   hash = hash_pointer(key);
   start_hash_address = hash & (map->size - 1);
   hash_address = start_hash_address;

   struct map_entry *entry = NULL;

   do {
      entry = map->map + hash_address;

      if (!entry_is_present(map, entry)) {
         /* Stash the first available entry we find */
         if (available_entry == NULL)
            available_entry = entry;
         if (entry_is_free(entry))
            break;
      }

      /* Implement replacement when another insert happens
       * with a matching key.  This is a relatively common
       * feature of hash tables, with the alternative
       * generally being "insert the new value as well, and
       * return it first when the key is searched for".
       *
       * Note that the pointer map doesn't have a delete
       * callback.  If freeing of old data pointers is
       * required to avoid memory leaks, perform a search
       * before inserting.
       */
      if (!entry_is_deleted(map, entry) && key == entry->key) {
         entry->data = data;
         return entry;
      }

      hash_address = (hash_address + 1) & (map->size - 1);
   } while (hash_address != start_hash_address);

   if (available_entry) {
      if (entry_is_deleted(map, available_entry))
         map->deleted_entries--;
      available_entry->key = key;
      available_entry->data = data;
      map->entries++;
      return available_entry;
   }

   /* We could hit here if a required resize failed. An unchecked-malloc
    * application could ignore this result.
    */
   return NULL;
}

/**
 * This function deletes the given pointer map entry.
 *
 * Note that deletion doesn't otherwise modify the table, so an iteration over
 * the table deleting entries is safe.
 */
void
_mesa_pointer_map_remove(struct pointer_map *map,
                        struct map_entry *entry)
{
   if (!entry)
      return;

   entry->key = NULL;
   entry->key = map->deleted_key;
   map->entries--;
   map->deleted_entries++;
}

/**
 * This function is an iterator over the pointer map.
 *
 * Pass in NULL for the first entry, as in the start of a for loop.  Note that
 * an iteration over the map is O(table_size) not O(entries).
 */
struct map_entry *
_mesa_pointer_map_next_entry(struct pointer_map *map,
                             struct map_entry *entry)
{
   if (entry == NULL)
      entry = map->map;
   else
      entry = entry + 1;

   for (; entry != map->map + map->size; entry++) {
      if (entry->key) {
         return entry;
      }
   }

   return NULL;
}
