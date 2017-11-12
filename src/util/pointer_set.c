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
 * Implements a linear probing set specifically for pointer keys.
 * It does not store the hash, effectively cutting the size of the set in two.
 * Some of the spared space is used to reduce load factor to 50%. It uses
 * linear probing for good cache locality.
 */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>

#include "pointer_set.h"
#include "ralloc.h"
#include "macros.h"

static const uint32_t deleted_key_value;
static const void *deleted_key = &deleted_key_value;

static inline bool
entry_is_free(struct pointer_set_entry *entry)
{
   return entry->key == NULL;
}

static inline uint32_t
hash_pointer(const void *pointer)
{
   uintptr_t num = (uintptr_t) pointer;
   return (uint32_t) ((num >> 2) ^ (num >> 6) ^ (num >> 10) ^ (num >> 14));
}

static inline bool
entry_is_deleted(struct pointer_set_entry *entry)
{
   return entry->key == deleted_key;
}

static inline bool
entry_is_present(struct pointer_set_entry *entry)
{
   return entry->key != NULL && entry->key != deleted_key;
}

struct pointer_set *
_mesa_pointer_set_create(void *mem_ctx)
{
   struct pointer_set *set;

   set = ralloc(mem_ctx, struct pointer_set);
   if (set == NULL)
      return NULL;

   set->size = 1 << 4;
   set->max_entries = set->size / 2;
   set->keys = rzalloc_array(set, struct pointer_set_entry, set->size);
   set->entries = 0;
   set->deleted_entries = 0;

   if (set->keys == NULL) {
      ralloc_free(set);
      return NULL;
   }

   return set;
}

/**
 * Frees the pointer set.
 */
void
_mesa_pointer_set_destroy(struct pointer_set* set,
      void (*delete_function)(struct pointer_set_entry *entry))
{
   if (!set)
      return;

   if (delete_function) {
      struct pointer_set_entry *entry;

      _mesa_pointer_set_foreach(set, entry) {
         delete_function(entry);
      }
   }

   ralloc_free(set);
}

/**
 * Finds a set entry with the given key.
 *
 * Returns NULL if no entry is found.  Note that the data pointer may be
 * modified by the user.
 */
struct pointer_set_entry *
_mesa_pointer_set_search(struct pointer_set *set, const void *key)
{
   uint32_t hash = hash_pointer(key);
   uint32_t start_hash_address = hash & (set->size - 1);
   uint32_t hash_address = start_hash_address;

   do {
      struct pointer_set_entry *entry = set->keys + hash_address;

      if (entry_is_free(entry)) {
         return NULL;
      } else if (entry->key == key) {
         return entry;
      }

      hash_address = (hash_address + 1) & (set->size - 1);
   } while (hash_address != start_hash_address);

   return NULL;
}

static void
_mesa_pointer_set_rehash(struct pointer_set *set, unsigned new_size)
{
   struct pointer_set old_set;
   struct pointer_set_entry *set_entries, *entry;

   old_set = *set;

   set->size = new_size;
   set->max_entries = set->size / 2;
   
   set_entries = rzalloc_array(set, struct pointer_set_entry, set->size);
   if (set_entries == NULL)
      return;

   set->keys = set_entries;
   set->entries = 0;
   set->deleted_entries = 0;

   _mesa_pointer_set_foreach(&old_set, entry) {
      _mesa_pointer_set_insert(set, entry->key);
   }

   ralloc_free(old_set.keys);
}

/**
 * Inserts the key with the given hash into the table.
 *
 * Note that insertion may rearrange the table on a resize or rehash,
 * so previously found hash_entries are no longer valid after this function.
 */
struct pointer_set_entry *
_mesa_pointer_set_insert(struct pointer_set *set, const void *key)
{
   uint32_t start_hash_address, hash_address, hash;
   struct pointer_set_entry *available_entry = NULL;

   assert(key != NULL);

   if (set->entries >= set->max_entries) {
      _mesa_pointer_set_rehash(set, set->size * 2);
   } else if (set->deleted_entries + set->entries >= set->max_entries) {
      _mesa_pointer_set_rehash(set, set->size);
   }

   hash = hash_pointer(key);
   start_hash_address = hash & (set->size - 1);
   hash_address = start_hash_address;

   do {
      struct pointer_set_entry *entry = set->keys + hash_address;

      if (!entry_is_present(entry)) {
         /* Stash the first available entry we find */
         if (available_entry == NULL)
            available_entry = entry;

         /* If the entry is free, that means we are at the end of a group.
          * Break from the loop, as we will not be finding a duplicate.
          */
         if (entry_is_free(entry))
            break;
      }

      if (entry->key == key)
         return entry;

      hash_address = (hash_address + 1) & (set->size - 1);
   } while (hash_address != start_hash_address);

   if (available_entry) {
      if (entry_is_deleted(available_entry))
         set->deleted_entries--;
      available_entry->key = key;
      set->entries++;
      return available_entry;
   }

   /* We could hit here if a required resize failed. An unchecked-malloc
    * application could ignore this result.
    */
   return NULL;
}

/**
 * This function deletes the given pointer set entry.
 *
 * Note that deletion doesn't otherwise modify the table, so an iteration over
 * the table deleting entries is safe.
 */
void
_mesa_pointer_set_remove(struct pointer_set *set,
                         struct pointer_set_entry *entry)
{
   if (!entry)
      return;

   entry->key = deleted_key;
   set->entries--;
   set->deleted_entries++;
}

/**
 * This function is an iterator over the pointer set.
 *
 * Pass in NULL for the first entry, as in the start of a for loop.  Note that
 * an iteration over the map is O(table_size) not O(entries).
 */
struct pointer_set_entry *
_mesa_pointer_set_next_entry(struct pointer_set *set,
                             struct pointer_set_entry *entry)
{
   if (entry == NULL)
      entry = set->keys;
   else
      entry = entry + 1;

   for (; entry != set->keys + set->size; entry++) {
      if (entry_is_present(entry)) {
         return entry;
      }
   }

   return NULL;
}
