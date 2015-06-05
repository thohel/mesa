/*
 * Copyright © 2014 Thomas Helland
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
 */

#include "nir_worklist.h"

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

typedef nir_worklist nir_loop_worklist;

static inline void
nir_loop_worklist_init(nir_loop_worklist *w, unsigned num_loops, void *mem_ctx)
{
   nir_worklist_init(w, num_loops, mem_ctx);
}

static inline void
nir_loop_worklist_fini(nir_loop_worklist *w)
{
   nir_worklist_fini(w);
}

static bool
loop_worklist_add_loop(nir_loop *loop, void *w)
{
   nir_worklist_push_tail((nir_worklist *)w, loop, 2); // XXX: There is a problem here: Loops have no index
   return true;
}

static inline void
nir_loop_worklist_add_all(nir_loop_worklist *w, nir_function_impl *impl)
{
   nir_cf_node *node = exec_node_data(nir_cf_node, exec_list_get_head(&impl->body), node);
   while (node != NULL) {
      if (node->type == nir_cf_node_loop)
         loop_worklist_add_loop(nir_cf_node_as_loop(node), w);
      node = nir_cf_node_next(node);
   }
}

static inline bool
nir_loop_worklist_is_empty(nir_loop_worklist *w)
{
   return nir_worklist_is_empty(w);
}

static inline void
nir_loop_worklist_push_head(nir_loop_worklist *w, nir_loop *loop)
{
   nir_worklist_push_head(w, loop, 2);               // XXX: There is a problem here: Loops have no index
}

static inline nir_loop *
nir_loop_worklist_peek_head(nir_loop_worklist *w)
{
   return (nir_loop *) nir_worklist_peek_head(w);
}

static inline nir_loop *
nir_loop_worklist_pop_head(nir_loop_worklist *w)
{
   nir_loop *loop = nir_loop_worklist_peek_head(w);
   nir_worklist_pop_head(w, 2);                      // XXX: There is a problem here: Loops have no index
   return loop;
}

static inline void
nir_loop_worklist_push_tail(nir_loop_worklist *w, nir_loop *loop)
{
   nir_worklist_push_tail(w, loop, 2);               // XXX: There is a problem here: Loops have no index
}

static inline nir_loop *
nir_loop_worklist_peek_tail(nir_loop_worklist *w)
{
   return (nir_loop *) nir_worklist_peek_tail(w);
}

static inline nir_loop *
nir_loop_worklist_pop_tail(nir_loop_worklist *w)
{
   nir_loop *loop = nir_loop_worklist_peek_tail(w);
   nir_worklist_pop_tail(w, 2);                      // XXX: There is a problem here: Loops have no index
   return loop;
}

#ifdef __cplusplus
}
#endif
