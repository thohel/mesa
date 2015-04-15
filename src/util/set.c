/*
 * Copyright © 2009-2012 Intel Corporation
 * Copyright © 1988-2004 Keith Packard and Bart Massey.
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
 * Except as contained in this notice, the names of the authors
 * or their institutions shall not be used in advertising or
 * otherwise to promote the sale, use or other dealings in this
 * Software without prior written authorization from the
 * authors.
 *
 * Authors:
 *    Eric Anholt <eric@anholt.net>
 *    Keith Packard <keithp@keithp.com>
 */

/**
 * Implements an open-addressing, quadratic probing hash-set.
 *
 * We choose set sizes that's a power of two.
 * This is computationally less expensive than primes.
 * As a bonus the size and free space can be calculated instead of looked up.
 * FNV-1a has good avalanche properties, so collision is not an issue.
 * These sets are sized to have an extra 10% free to avoid
 * exponential performance degradation as the set fills.
 */

#include <stdlib.h>
#include <assert.h>

#include "macros.h"
#include "ralloc.h"
#include "set.h"

uint32_t deleted_key_value;
const void *deleted_key = &deleted_key_value;

static int
entry_is_free(struct set_entry *entry)
{
   return entry->key == NULL;
}

static int
entry_is_deleted(struct set_entry *entry)
{
   return entry->key == deleted_key;
}

static int
entry_is_present(struct set_entry *entry)
{
   return entry->key != NULL && entry->key != deleted_key;
}

struct set *
_mesa_set_create(void *mem_ctx,
                 uint32_t (*key_hash_function)(const void *key),
                 bool (*key_equals_function)(const void *a,
                                             const void *b))
{
   struct set *ht;

   ht = ralloc(mem_ctx, struct set);
   if (ht == NULL)
      return NULL;

   ht->size_iteration = 2;
   ht->size = 1 << ht->size_iteration;
   ht->max_entries = ht->size * 0.9;
   ht->key_hash_function = key_hash_function;
   ht->key_equals_function = key_equals_function;
   ht->table = rzalloc_array(ht, struct set_entry, ht->size);
   ht->entries = 0;
   ht->deleted_entries = 0;

   if (ht->table == NULL) {
      ralloc_free(ht);
      return NULL;
   }

   return ht;
}

/**
 * Frees the given set.
 *
 * If delete_function is passed, it gets called on each entry present before
 * freeing.
 */
void
_mesa_set_destroy(struct set *ht, void (*delete_function)(struct set_entry *entry))
{
   if (!ht)
      return;

   if (delete_function) {
      struct set_entry *entry;

      set_foreach (ht, entry) {
         delete_function(entry);
      }
   }
   ralloc_free(ht->table);
   ralloc_free(ht);
}

/**
 * Finds a set entry with the given key and hash of that key.
 *
 * Returns NULL if no entry is found.
 */
static struct set_entry *
set_search(const struct set *ht, uint32_t hash, const void *key)
{
   uint32_t start_hash_address = hash & (ht->size - 1);
   uint32_t hash_address = start_hash_address;
   uint32_t quad_hash = 1;

   do {
      struct set_entry *entry = ht->table + hash_address;

      if (entry_is_free(entry)) {
         return NULL;
      } else if (entry_is_present(entry) && entry->hash == hash) {
         if (ht->key_equals_function(key, entry->key)) {
            return entry;
         }
      }

      hash_address = (start_hash_address +
                (quad_hash + (quad_hash * quad_hash)) / 2) & (ht->size - 1);
      quad_hash++;
   } while (hash_address != start_hash_address);

   return NULL;
}

struct set_entry *
_mesa_set_search(const struct set *set, const void *key)
{
   assert(set->key_hash_function);
   return set_search(set, set->key_hash_function(key), key);
}

struct set_entry *
_mesa_set_search_pre_hashed(const struct set *set, uint32_t hash,
                            const void *key)
{
   assert(set->key_hash_function == NULL ||
          hash == set->key_hash_function(key));
   return set_search(set, hash, key);
}

static struct set_entry *
set_add(struct set *ht, uint32_t hash, const void *key);

static void
set_rehash(struct set *ht, uint32_t new_size_iteration)
{
   struct set old_ht;
   struct set_entry *table, *entry;

   if (new_size_iteration >= 31)
      return;

   table = rzalloc_array(ht, struct set_entry,
                         1 << new_size_iteration);
   if (table == NULL)
      return;

   old_ht = *ht;

   ht->table = table;
   ht->size_iteration = new_size_iteration;
   ht->size = 1 << new_size_iteration;
   ht->max_entries = ht->size * 0.7;
   ht->entries = 0;
   ht->deleted_entries = 0;

   set_foreach(&old_ht, entry) {
      set_add(ht, entry->hash, entry->key);
   }

   ralloc_free(old_ht.table);
}

/**
 * Inserts the key with the given hash into the table.
 *
 * Note that insertion may rearrange the table on a resize or rehash,
 * so previously found hash_entries are no longer valid after this function.
 */
static struct set_entry *
set_add(struct set *ht, uint32_t hash, const void *key)
{
   uint32_t start_hash_address, hash_address;
   uint32_t quad_hash = 1;
   struct set_entry *available_entry = NULL;

   if (ht->entries >= ht->max_entries) {
      set_rehash(ht, ht->size_iteration + 1);
   } else if (ht->deleted_entries + ht->entries >= ht->max_entries) {
      set_rehash(ht, ht->size_iteration);
   }

   start_hash_address = hash & (ht->size - 1);
   hash_address = start_hash_address;

   do {
      struct set_entry *entry = ht->table + hash_address;

      if (!entry_is_present(entry)) {
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
       * Note that the hash table doesn't have a delete callback.
       * If freeing of old keys is required to avoid memory leaks,
       * perform a search before inserting.
       */
      if (!entry_is_deleted(entry) &&
          entry->hash == hash &&
          ht->key_equals_function(key, entry->key)) {
         entry->key = key;
         return entry;
      }

      hash_address = (start_hash_address +
                (quad_hash + (quad_hash * quad_hash)) / 2) & (ht->size - 1);
      quad_hash++;
   } while (hash_address != start_hash_address);


   if (available_entry) {
      if (entry_is_deleted(available_entry))
         ht->deleted_entries--;
      available_entry->hash = hash;
      available_entry->key = key;
      ht->entries++;
      return available_entry;
   }

   /* We could hit here if a required resize failed. An unchecked-malloc
    * application could ignore this result.
    */
   unreachable("Failed to insert entry in hash set");
   return NULL;
}

struct set_entry *
_mesa_set_add(struct set *set, const void *key)
{
   assert(set->key_hash_function);
   return set_add(set, set->key_hash_function(key), key);
}

struct set_entry *
_mesa_set_add_pre_hashed(struct set *set, uint32_t hash, const void *key)
{
   assert(set->key_hash_function == NULL ||
          hash == set->key_hash_function(key));
   return set_add(set, hash, key);
}

/**
 * This function deletes the given hash table entry.
 *
 * Note that deletion doesn't otherwise modify the table, so an iteration over
 * the table deleting entries is safe.
 */
void
_mesa_set_remove(struct set *ht, struct set_entry *entry)
{
   if (!entry)
      return;

   entry->key = deleted_key;
   ht->entries--;
   ht->deleted_entries++;
}

/**
 * This function is an iterator over the hash table.
 *
 * Pass in NULL for the first entry, as in the start of a for loop.  Note that
 * an iteration over the table is O(table_size) not O(entries).
 */
struct set_entry *
_mesa_set_next_entry(const struct set *ht, struct set_entry *entry)
{
   if (entry == NULL)
      entry = ht->table;
   else
      entry = entry + 1;

   for (; entry != ht->table + ht->size; entry++) {
      if (entry_is_present(entry)) {
         return entry;
      }
   }

   return NULL;
}

struct set_entry *
_mesa_set_random_entry(struct set *ht,
                       int (*predicate)(struct set_entry *entry))
{
   struct set_entry *entry;
   uint32_t i = rand() & (ht->size - 1);

   if (ht->entries == 0)
      return NULL;

   for (entry = ht->table + i; entry != ht->table + ht->size; entry++) {
      if (entry_is_present(entry) &&
          (!predicate || predicate(entry))) {
         return entry;
      }
   }

   for (entry = ht->table; entry != ht->table + i; entry++) {
      if (entry_is_present(entry) &&
          (!predicate || predicate(entry))) {
         return entry;
      }
   }

   return NULL;
}
