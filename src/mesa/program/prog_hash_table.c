/*
 * Copyright © 2008 Intel Corporation
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
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

/**
 * \file hash_table.c
 * \brief Implementation of a generic, opaque hash table data type.
 *
 * \author Ian Romanick <ian.d.romanick@intel.com>
 */

#include "main/imports.h"
#include "util/simple_list.h"
#include "hash_table.h"

unsigned
hash_table_string_hash(const void *key)
{
   const char *str = (const char *) key;
   uint32_t hash = _mesa_hash_string(str);
   return hash;
}

bool
hash_table_string_compare(const void *a, const void *b)
{
   return _mesa_key_string_equal(a, b);
}


unsigned
hash_table_pointer_hash(const void *key)
{
   return _mesa_hash_pointer(key);
}


bool
hash_table_pointer_compare(const void *key1, const void *key2)
{
   return _mesa_key_pointer_equal(key1, key2);
}
