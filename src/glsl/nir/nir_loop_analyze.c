/*
 * Copyright © 2014 Intel Corporation
 *
 * XXX: Need to fix the copyright header
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

#include "nir.h"
#include "nir_loop_worklist.h"
typedef struct {
   /*
    * Something should probably go here.
    * I guess we want a list of all the loops
    * that we find in our initial round of looking for loops.
    */
   void *mem_ctx;
   nir_function_impl *impl;
   uint32_t num_loops_found;

   /*
    * This is based on using a loop worklist
    * We could instead do the trick done in nir_opt_dce and
    * wrap our own little list around exec_list.
    */
   nir_loop_worklist *loops;
} loop_analyze_state;





nir_loop_analyze_impl(nir_function_impl *impl)
{
   loop_analyze_state state;

   state.mem_ctx = ralloc_parent(impl);
   state.impl = impl;

   nir_loop_worklist_init(state.loops, 10, state.mem_ctx);

   nir_loop_worklist_add_all(state.loops, state.impl);
/*
   nir_cf_node *node = exec_node_data(nir_cf_node, exec_list_get_head(impl.body), node);
   while (node != NULL) {
      if (node->type == nir_cf_node_loop) {

      }
      node = nir_cf_node_next(node);
   }
*/

   if (state.num_loops_found != 0)
      nir_metadata_preserve(impl, nir_metadata_block_index |
                                  nir_metadata_dominance);

   return state.progress;
}

nir_loop_analyze(nir_shader *shader)
{
   bool progress = false;

   nir_foreach_overload(shader, overload) {
      if (overload->impl)
         progress |= nir_opt_constant_folding_impl(overload->impl);
   }

   return progress;
}






/** Propagates the live in of succ across the edge to the live out of pred
 *
 * Phi nodes exist "between" blocks and all the phi nodes at the start of a
 * block act "in parallel".  When we propagate from the live_in of one
 * block to the live out of the other, we have to kill any writes from phis
 * and make live any sources.
 *
 * Returns true if updating live out of pred added anything
 */
static bool
propagate_across_edge(nir_block *pred, nir_block *succ,
                      struct live_variables_state *state)
{
   NIR_VLA(BITSET_WORD, live, state->bitset_words);
   memcpy(live, succ->live_in, state->bitset_words * sizeof *live);

   nir_foreach_instr(succ, instr) {
      if (instr->type != nir_instr_type_phi)
         break;
      nir_phi_instr *phi = nir_instr_as_phi(instr);

      assert(phi->dest.is_ssa);
      set_ssa_def_dead(&phi->dest.ssa, live);
   }

   nir_foreach_instr(succ, instr) {
      if (instr->type != nir_instr_type_phi)
         break;
      nir_phi_instr *phi = nir_instr_as_phi(instr);

      nir_foreach_phi_src(phi, src) {
         if (src->pred == pred) {
            set_src_live(&src->src, live);
            break;
         }
      }
   }

   BITSET_WORD progress = 0;
   for (unsigned i = 0; i < state->bitset_words; ++i) {
      progress |= live[i] & ~pred->live_out[i];
      pred->live_out[i] |= live[i];
   }
   return progress != 0;
}

void
nir_live_variables_impl(nir_function_impl *impl)
{
   struct live_variables_state state;

   /* We start at 1 because we reserve the index value of 0 for ssa_undef
    * instructions.  Those are never live, so their liveness information
    * can be compacted into a single bit.
    */
   state.num_ssa_defs = 1;
   nir_foreach_block(impl, index_ssa_definitions_block, &state);

   nir_block_worklist_init(&state.worklist, impl->num_blocks, NULL);

   /* We now know how many unique ssa definitions we have and we can go
    * ahead and allocate live_in and live_out sets and add all of the
    * blocks to the worklist.
    */
   state.bitset_words = BITSET_WORDS(state.num_ssa_defs);
   nir_foreach_block(impl, init_liveness_block, &state);

   /* We're now ready to work through the worklist and update the liveness
    * sets of each of the blocks.  By the time we get to this point, every
    * block in the function implementation has been pushed onto the
    * worklist in reverse order.  As long as we keep the worklist
    * up-to-date as we go, everything will get covered.
    */
   while (!nir_block_worklist_is_empty(&state.worklist)) {
      /* We pop them off in the reverse order we pushed them on.  This way
       * the first walk of the instructions is backwards so we only walk
       * once in the case of no control flow.
       */
      nir_block *block = nir_block_worklist_pop_head(&state.worklist);

      memcpy(block->live_in, block->live_out,
             state.bitset_words * sizeof(BITSET_WORD));

      nir_if *following_if = nir_block_get_following_if(block);
      if (following_if)
         set_src_live(&following_if->condition, block->live_in);

      nir_foreach_instr_reverse(block, instr) {
         /* Phi nodes are handled seperately so we want to skip them.  Since
          * we are going backwards and they are at the beginning, we can just
          * break as soon as we see one.
          */
         if (instr->type == nir_instr_type_phi)
            break;

         nir_foreach_ssa_def(instr, set_ssa_def_dead, block->live_in);
         nir_foreach_src(instr, set_src_live, block->live_in);
      }

      /* Walk over all of the predecessors of the current block updating
       * their live in with the live out of this one.  If anything has
       * changed, add the predecessor to the work list so that we ensure
       * that the new information is used.
       */
      struct set_entry *entry;
      set_foreach(block->predecessors, entry) {
         nir_block *pred = (nir_block *)entry->key;
         if (propagate_across_edge(pred, block, &state))
            nir_block_worklist_push_tail(&state.worklist, pred);
      }
   }

   nir_block_worklist_fini(&state.worklist);
}

static bool
nir_opt_constant_folding_impl(nir_function_impl *impl)
{
   struct constant_fold_state state;

   state.mem_ctx = ralloc_parent(impl);
   state.impl = impl;
   state.progress = false;

   nir_foreach_block(impl, constant_fold_block, &state);

   if (state.progress)
      nir_metadata_preserve(impl, nir_metadata_block_index |
                                  nir_metadata_dominance);

   return state.progress;
}

bool
nir_opt_constant_folding(nir_shader *shader)
{
   bool progress = false;

   nir_foreach_overload(shader, overload) {
      if (overload->impl)
         progress |= nir_opt_constant_folding_impl(overload->impl);
   }

   return progress;
}
