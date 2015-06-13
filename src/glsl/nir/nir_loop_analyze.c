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
#include "nir_ssa_def_worklist.h"

typedef enum {
   unprocessed,
   undefined,
   invariant,
   basic_induction,
   derived_induction
} loop_variable_type;

typedef struct {
   loop_variable_type type;

   nir_ssa_def *ssa_def;

} loop_variable_entry;

typedef struct {
   /*
    * Something should probably go here.
    * I guess we want a list of all the loops
    * that we find in our initial round of looking for loops.
    */
   void *mem_ctx;
   nir_function_impl *impl;
   uint32_t num_loops_found;
   loop_variable_entry *entries;

   /*
    * This is based on using a loop worklist
    * We could instead do the trick done in nir_opt_dce and
    * wrap our own little list around exec_list.
    */
   nir_loop_worklist *loops;

   /*
    * Worklist of ssa-defs
    */
   nir_ssa_def_worklist *ssa_defs;
} loop_analyze_state;

/*
 * Gets the loop entry for the given ssa def
 */
static loop_variable_entry *
get_loop_entry(nir_ssa_def *value, loop_analyze_state *state)
{
   loop_variable_entry *entry = &state->entries[value->index];
   return entry;
}

static bool
is_alu_invariant(nir_alu_instr *alu, loop_analyze_state *state)
{
   loop_variable_entry *entry = get_lattice_entry(alu.dest.dest.ssa, state);
   loop_variable_entry *src;
   boolean all_constant = true;

   for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {
      src = get_lattice_entry(alu->src[i].src.ssa, state);

      /* Check if the instruction is from outside the loop
       * If it is it is invariant, and so we can mark continue
       * through and onto the next operand
       */
      if ();

      /*
       * we have two possibilities; optimistic or pessimistic
       * We can solve it mostly in the way it is solved for SCCP
       * or we can use a system of recursion
       */

      /*
       * Example of how it could work with recursion.
       * This is however a pessimistic approach, and so may not
       * detect all of the invariants that exist.
       */
      if (!is_loop_invariant(src->ssa_def, state))
         return false;
   }
}

static bool
is_phi_invariant(nir_phi_instr *phi, loop_analyze_state *state)
{
   loop_variable_entry *entry = get_lattice_entry(phi.dest.ssa, state);
   loop_variable_entry *src_entry;
   boolean all_constant = true;

   nir_foreach_phi_src(phi, src) {
      src_entry = get_loop_entry(src->src.ssa, state);

      if (src_entry->type == invariant)
         continue;

      if (!is_loop_invariant(src_entry->ssa_def, state))
         return false;
   }
}

static bool
is_reaching_definition_outside_loop(loop_variable_entry *entry, loop_analyze_state *state)
{
   loop_variable_entry *src_entry;

   switch (entry->ssa_def->parent_instr->type)
   case nir_alu_instr: {
      nir_alu_instr *instr = nir_instr_as_alu(entry.ssa_def.parent_instr);

      for (unsigned i = 0; i < nir_op_infos[instr->op].num_inputs; i++) {

         /* Check if the instruction is from outside the loop
          * If it is fall through to next operand
          * If it is not then return false
          */
         if ();
      }
      return true;
   }
   case nir_phi_instr: {
      nir_phi_instr *instr = nir_instr_as_phi(entry.ssa_def.parent_instr);

      nir_foreach_phi_src(instr, src) {
         /* Check if the instruction is from outside the loop
          * If it is fall through to next operand
          * If it is not then return false
          */
         if ();
      }
      return true;
   }
   default: {
      return false;
   }
}

static bool
is_loop_invariant(nir_ssa_def *def, loop_analyze_state *state)
{
   loop_variable_entry *entry = get_loop_entry(def, state);

   if(entry->type == invariant)
      return true;

   /*
    * If the variable is not in a loop it is loop invariant.
    * Mark it as such.
    */
   if (/*entry outside loop*/) {
      entry->type = invariant;
      return true;
   }

   if (entry->type != basic_induction && entry->type != derived_induction) {
      /*
       * Process value
       *
       * There are three rules to follow:
       *    Are all the operands from outside the loop?
       *    Are all the operands loop invariant?
       *    Or is it a combination of the two?
       *       Then it is loop invariant
       *    If one of the operands are induction variables
       *       Can not be loop invariant
       *
       * If it is found to be invariant then add all users to the ssa
       * worklist so that we can find out if it is now invariant.
       */
      entry->ssa_def = def;

      switch (def->parent_instr.type)
      case nir_instr_type_alu: {
         nir_alu_instr *alu = nir_instr_as_alu(def.parent_instr);
         return is_alu_invariant(alu, state);
      }
      case nir_instr_type_phi: {
         nir_phi_instr *phi = nir_instr_as_phi(def.parent_instr);
         return is_phi_invariant(phi, state);
      }
      case nir_instr_type_load_const: {
         entry->type = invariant; // Is this correct? Shouldn't it be?
         return true;
      }
      default: {
         entry->type = undefined;
         /*
          * XXX: we need to handle other users than alu's probably.
          * We can, for now, set that use as overdefined and bail.
          * Uniform loads may be of interest?
          */
         return false;
      }
   }

   /*
    * It is one of the other cases
    */
   return false;
}

/*
 * Coordinates finding the uses of the ssa_def corresponding
 * to the entry and sticking them in the ssa_worklist.
 * Should be run on every entry that we change the information of.
 */
static void
coordinate_uses(loop_variable_entry *entry, loop_analyze_state *state)
{
   struct set_entry *set_entry;
   set_foreach(entry->ssa_def->uses, entry) {
      nir_instr *instr = (nir_instr *)set_entry.key;
      nir_ssa_def_worklist_push_head(state->ssa_defs, entry->ssa_def);
   }
}

static void
initialize_entry(nir_ssa_def *def, loop_analyze_state *state)
{
   loop_variable_entry *entry = get_lattice_entry(def, state);

   entry->ssa_def = def;

   if (def->parent_instr->type == nir_instr_type_load_const) {
      entry->type = invariant;
      return;
   }

   if (is_reaching_definition_outside_loop(entry, state)) {
      entry->type = invariant;
      return;
   }

   entry->type = undefined;
}

static void
initialize_block_invariance(nir_block *block, void *state) {
   nir_foreach_instr(block, instr) {
      nir_foreach_ssa_def(instr, initialize_entry, block);
   }
}

nir_loop_analyze_impl(nir_function_impl *impl)
{
   loop_analyze_state state;

   state.mem_ctx = ralloc_parent(impl);
   state.impl = impl;

   state.entries = rzalloc_array(state.mem_ctx, struct loop_variable_entry,
                                 impl.ssa_alloc);

   nir_loop_worklist_init(state.loops, 10, state.mem_ctx);

   nir_loop_worklist_add_all(state.loops, state.impl);

   /*
    * How detecting loop invariant code works.
    *    Make invariant all those operations who are
    *       Constant or
    *       Reaching definition is outside loop
    *    While (changes has occured)
    *       mark invariant all those operations whose operands are
    *          constant
    *          reaching definition outisde loop
    *          has a single reaching definition in loop that is invariant
    *             (in practice a phi with one loop variable and one from outside)
    */
   nir_foreach_block(impl, initialize_block_invariance, state);

   while (state.ssa_defs->count > 0) {
      /*
       * All instructions in the list are here because
       * we got new information about an operand.
       */
      nir_ssa_def *def;
      nir_ssa_def_worklist_pop_head(state.ssa_defs, def);

      /*
       * We need to process the value, and check it if has changed state
       */
      loop_variable_entry *entry = get_loop_entry(def, state);
      loop_variable_type old = entry->type;
      is_loop_invariant(def, state);

      if (old == entry->type) {
         /*
          * No change in value, so we don't need to do anything
          */
         continue;
      } else {
         /*
          * There was a change in value, so we should add all the users
          * to the worklist, as they will need to be checked again.
          */
         coordinate_uses(entry, state);
      }
   }

   while (!nir_loop_worklist_is_empty(state.loops)) {

   }

   // This is not correct, but just left here as a reminder
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











/*
 * This is most likely not useful at all
 * We probably want to solve this in some other kind of way
 */
static void
evaluate_invariants_for_block(nir_block *block, loop_analyze_state *state)
{
   nir_instr *instr;
   nir_foreach_instr_safe(block, instr) {

      switch (instr.type)
      case nir_instr_type_alu: {
         nir_alu_instr *alu = nir_instr_as_alu(instr);
         evaluate_alu_instr(alu, state);
      }
      case nir_instr_type_phi: {
         nir_phi_instr *phi = nir_instr_as_phi(instr);
         evaluate_phi_instr(phi, state);
      }
      case nir_instr_type_load_const: {
         nir_load_const_instr *lc = nir_instr_as_load_const(instr);
         evaluate_load_const_instr(lc, state);
      }
      default: {
         /*
          * XXX: we need to handle other users than alu's probably.
          * We can, for now, set that use as overdefined and bail.
          * Uniform loads may be of interest?
          */
      }
   }
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
