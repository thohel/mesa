/*
 * Copyright © 2015 Thomas Helland (for Google's Summer of Code)
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

/*
 * This pass converts the ssa-graph into "Loop Closed SSA form". This is
 * done by placing phi nodes at the exits of the loop for all values
 * that are used outside the loop. The result is it transforms:
 *
 * loop {                    ->          loop {
 *    ssa2 = ....            ->          ssa2 = ...
 *    if (cond)              ->          if (cond)
 *       break;              ->             ssa5 = phi(ssa2)
 *    ssa3 = ssa2 * ssa4     ->             break;
 * }                         ->          ssa3 = ssa2 * ssa4
 * ssa6 = ssa2 + 4           ->          }
 *                                    ssa6 = ssa5 + 4
 *
 * This will make a lot of other passes like loop unrolling and LICM simpler.
 * It is also beneficial as it makes it trivial to keep control of which
 * ssa-defs are live across the loop-boundary. It will also simplify doing
 * loop-unswitching a lot, as one just needs to copy the conditional out of
 * the loop, put one copy of the loop into the then branch, and the other
 * into the else branch, set the condition true and false respectively in
 * these loops, and rewrite the LCSSA-phi's to have both the "true"-loop
 * and the "false"-loop versions of the ssa-def as source.
 *
 * XXX: The pass currently crashes in nir_validate. The reason is that we
 * insert a phi-node that has a predecessor that is not marked as having
 * that phi-node's block as a successor. The pattern that gets tested is:
 * Pick a block X.
 * Check the successor blocks of x.
 * For each instruction, if we find phi-nodes, check if their predecessor is x.
 * This fails because we insert phi-nodes in blocks that the control flow
 * can not actually exit from. A simple solution would be to have a
 * "is_lcssa_phi" flag for the lcssa nodes. Then we can skip the validation
 * of these. Or we can move the phi to the block where we actually exit.
 * But that would imply moves or some other trickery to get the "referred-to"
 * def to be inside the then-break block, which is unfortunate for ie loop
 * analysis and loop terminator detection.
 */

#include "nir.h"

typedef struct {
   /* The nir_shader we are transforming */
   nir_shader *shader;

   /* The loop we store information for */
   nir_loop *loop;

   /* Keep track of which defs are in the loop */
   BITSET_WORD *is_in_loop;

   /* General purpose bool */
   bool flag;
} lcssa_state;

static inline bool
mark_ssa_def_as_in_loop(nir_ssa_def *def, void *state)
{
   lcssa_state *state_cast = (lcssa_state *) state;
   BITSET_SET(state_cast->is_in_loop, def->index);
   return true;
}

static bool
mark_block_as_in_loop(nir_block *block, void *state)
{
   nir_foreach_instr(block, instr)
      nir_foreach_ssa_def(instr, mark_ssa_def_as_in_loop, state);
   return true;
}

static bool
is_outside_loop(nir_ssa_def *def, void *void_state)
{
   lcssa_state *state = void_state;
   if (!BITSET_TEST(state->is_in_loop, def->index))
      state->flag = true;
   return true;
}

static bool
convert_loop_exit_for_ssa(nir_ssa_def *def, void *void_state)
{
   lcssa_state *state = void_state;

   state->flag = false;

   nir_foreach_use_safe(def, src)
      nir_foreach_ssa_def(src->parent_instr, is_outside_loop, void_state);

   nir_foreach_if_use_safe(def, src) {
      /* XXX: If the def is used outside the loop in an if-condition then
       * we should detect that and insert a phi in between
       */
   }

   /* There where no sources that had defs outside the loop */
   if (!state->flag)
      return true;

   /* Initialize a phi-instruction */
   nir_phi_instr *phi = nir_phi_instr_create(state->shader);
   phi->instr.block =
         nir_cf_node_as_block(nir_cf_node_next(&state->loop->cf_node));
   nir_ssa_dest_init(&phi->instr, &phi->dest,
                     def->num_components, "LCSSA-phi");
   phi->is_lcssa_phi = true;

   /* Connect the ssa-def and the phi instruction */
   nir_phi_src *phi_src = ralloc(phi, nir_phi_src);
   phi_src->pred = def->parent_instr->block;
   phi_src->src = nir_src_for_ssa(def);

   exec_list_push_tail(&phi->srcs, &phi_src->node);

   nir_instr_insert_before_block(phi->instr.block, &phi->instr);

   /* Run through all uses and rewrite those outside the loop to point to
    * the phi instead of pointing to the ssa-def.
    */
   nir_foreach_use_safe(def, src) {
      state->flag = false;
      nir_foreach_ssa_def(src->parent_instr, is_outside_loop, state);

      if (!state->flag)
         continue;

      nir_instr_rewrite_src(src->parent_instr, src,
                            nir_src_for_ssa(&phi->dest.ssa));
   }

   nir_foreach_if_use_safe(def, src) {
      /* If the if is outside the loop then run the below */
      //nir_if_rewrite_condition(src->parent_if, nir_src_for_ssa(phi->dest.ssa));
   }
   return true;
}

static void
convert_to_lcssa(nir_cf_node *cf_node, lcssa_state *state)
{
   switch (cf_node->type) {
   case nir_cf_node_block: {
      nir_foreach_instr(nir_cf_node_as_block(cf_node), instr)
         nir_foreach_ssa_def(instr, convert_loop_exit_for_ssa, state);
      return;
   }
   case nir_cf_node_if: {
      nir_if *if_stmt = nir_cf_node_as_if(cf_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->then_list)
         convert_to_lcssa(nested_node, state);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->else_list)
         convert_to_lcssa(nested_node, state);
      return;
   }
   case nir_cf_node_loop:
      /* Since we are going depth first the innermost loop will already have
       * been rewritten, and so there should be no defs inside the inner loop
       * that are not already rewritten with LCSSA-phis in our current loop.
       */
      return;
   default:
      unreachable("unknown cf node type");
   }
}

static void
compute_lcssa(nir_cf_node *cf_node)
{
   switch (cf_node->type) {
   case nir_cf_node_block:
      return;
   case nir_cf_node_if: {
      nir_if *if_stmt = nir_cf_node_as_if(cf_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->then_list)
         compute_lcssa(nested_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->else_list)
         compute_lcssa(nested_node);
      return;
   }
   case nir_cf_node_loop: {
      nir_loop *loop = nir_cf_node_as_loop(cf_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &loop->body)
         compute_lcssa(nested_node);
      break;
   }
   default:
      unreachable("unknown cf node type");
   }

   nir_loop *loop = nir_cf_node_as_loop(cf_node);
   nir_function_impl *impl = nir_cf_node_get_function(cf_node);

   lcssa_state *state = rzalloc(NULL, lcssa_state);

   state->is_in_loop = rzalloc_array(state, BITSET_WORD,
                                      BITSET_WORDS(impl->ssa_alloc));

   state->loop = loop;

   nir_foreach_block_in_cf_node(cf_node, mark_block_as_in_loop, state);

   foreach_list_typed(nir_cf_node, node, node, &loop->body)
      convert_to_lcssa(node, state);
}

void
nir_form_LCSSA_impl(nir_function_impl *impl)
{
   foreach_list_typed(nir_cf_node, node, node, &impl->body)
      compute_lcssa(node);
}

void
nir_form_LCSSA(nir_shader *shader)
{
   nir_foreach_overload(shader, overload) {
      if (overload->impl)
         nir_form_LCSSA_impl(overload->impl);
   }
}
