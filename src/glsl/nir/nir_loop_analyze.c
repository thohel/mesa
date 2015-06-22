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



   /*
    * basic induction variable:
    *    i = i + c
    *    i = i - c
    *    i = i * c
    *    i = i / c
    *    where c is loop invariant or constant
    *    defined only once in a loop
    * derived induction variable
    *    j = i * c1 + c2
    *    j = i / c1 + c2
    *    j = i * c1 - c2
    *    j = i / c1 - c2
    *    where c1 and c2 are loop invariant or constant
    *    defined only once in a loop
    *
    *    triple(i, c1, c2) where i = basic induction variable, c1 and c2 invariant.
    *    ^^ XXX: This has not been explored, but may proce usefull.
    *
    * Family of induction variable B is the set of induction
    * variables A that are a linear function of B
    */


#include "nir.h"
#include "util/list.h"

typedef struct {
   /*
    * Something should probably go here.
    * I guess we want a list of all the loops
    * that we find in our initial round of looking for loops.
    */
   void *mem_ctx;
   nir_function_impl *impl;
   uint32_t num_loops_found;
   loop_variable *vars;

   // A list of the loop_entries in the function
   struct list_head loops;

   loop_entry *current_entry;
   uint32_t number_of_loops;

   /*
    * Worklist of ssa-defs
    */
   nir_ssa_def_worklist *ssa_defs;
} loop_analyze_state;

/*
 * Snipped from Connors Dead Control Flow Removal Series.
 * Located in nir.c / nir.h
 */
static bool
nir_foreach_block_in_cf_node(nir_cf_node *node, nir_foreach_block_cb cb,
                             void *state)
{
   return foreach_cf_node(node, cb, false, state);
}

/*
 * Coordinates finding the uses of the ssa_def corresponding
 * to the entry and sticking them in the ssa_worklist.
 * Should be run on every entry that we change the information of.
 */
static void
coordinate_uses(loop_variable *var, loop_analyze_state *state)
{
   struct set_entry *set_entry;
   set_foreach(var->ssa_def->uses, var) {
      nir_instr *instr = (nir_instr *)set_entry.key;
      nir_ssa_def_worklist_push_head(state->ssa_defs, var->ssa_def);
   }
}

static bool
nir_cf_node_contains(nir_cf_node *container, nir_cf_node *content)
{
   if (foreach_cf_node(container, does_cf_node_match, false, content))
      return true;

   return false;
}

static bool
does_cf_node_match(nir_cf_node *a, nir_cf_node *b)
{
   return a == b;
}

static loop_entry
get_loops_ordered(nir_function_impl *impl, void *mem_ctx)
{
   loop_entry *head = ralloc(mem_ctx, struct loop_entry);
   LIST_INITHEAD(head);

   bool loop_found = false;
   /*
    * Find all loops and add them to the list
    */
   foreach_list_typed(nir_cf_node, cur, node, impl->body) {
      if (cur->type == nir_cf_node_loop) {
         nir_loop *loop = nir_cf_node_as_loop(cur);
         loop_entry *entry = ralloc(mem_ctx, struct loop_entry);
         entry->loop = loop;
         LIST_ADD(entry->loop_link, head);
         loop_found = true;
      }
   }

   if (!loop_found)
      return NULL;

   /*
    * Walk through the list and shuffle loops around until we get
    * a list of loops where the deepest loops are first.
    */
   bool changed = true;
   while (changed) {
      list_for_each_entry_safe(loop_entry, a, head, a.loop_link) {
         list_for_each_entry_from_safe(loop_entry, b, a, head, b.loop_link) {
            if (nir_cf_node_contains(a, b)) {
               /*
                * The loop b was nested inside loop a
                * Move loop b to the front of the list.
                */
               LIST_DEL(b);
               LIST_ADD(b, head);
               changed = true;
            }
         }
      }
   }

   return head;
}

static void
find_loops(nir_function_impl *impl, loop_analyze_state *state)
{
   /*
    * Walk through al cf_nodes to find loops
    * Add them in the smart order
    * Inner loops should go first in list.
    * Probably benefitial to add from the outer to the inner,
    * and apped to the front of the list. Should make the inner loop the
    * first to be processed.
    */
   foreach_list_typed(nir_cf_node, cur, node, impl->body) {
      if (cur->type == nir_cf_node_loop) {
         nir_loop *loop = nir_cf_node_as_loop(cur);
         loop_entry *entry = ralloc(state.mem_ctx, struct loop_entry);
         entry->loop = loop;
         LIST_ADD(entry->loop_list, state->loops);
      }
   }

   list_for_each_entry() {
      list_for_each_entry_from() {
         if nir_cf_node_contains(nir_cf_node *container, nir_cf_node *content)
            // take the cf node out of the list and add to list before this entry
            /*
             * May instead want to find loop depth, and sort the list by that instead.
             *
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











typedef enum {
   unprocessed,
   undefined,
   invariant,
   basic_induction,
   derived_induction
} nir_loop_variable_type;

typedef struct {
   /* The ssa_def assosiated with this info */
   nir_ssa_def *def;

   /* The type of this ssa_def */
   nir_loop_variable_type *type;
} nir_loop_ssa_def_info;

typedef struct {
   /* The loop we store information for */
   nir_loop *loop;

   /* Array of info's for each def in loop */
   nir_loop_ssa_def_info *def_infos;

   uint32_t num_ssa_defs_in_loop;

   /* In the case of a nested loop this stores the surrounding loop */
   nir_loop *parent_loop;

   /* The nesting depth of this loop. We start at 1 (blocks in main loop are 0 */
   uint32_t nest_depth;

   // A list of the loop_vars to process
   struct list_head invariant_list;

   /* The ssa_defs that are invariant */
//   nir_loop_ssa_def_info *invariants;

   /* The ssa_defs that are induction variables */
   nir_loop_ssa_def_info *inductions;
} nir_loop_info;

typedef struct {
   nir_loop_ssa_def_info *info;
   struct list_head process_link;
   struct list_head loop_link;
   struct list_head invariant_link;
   boolean in_loop;
} loop_variable;

typedef struct {
   nir_loop_info *info;

   // Loop_variable for all ssa_defs in function
   loop_variable *all_vars;

   // A list of the loop_vars in the loop
   struct list_head loop_vars;

   // A list of the loop_vars to process
   struct list_head process_list;
} nir_loop_info_state;

/*
 * Gets the loop entry for the given ssa def
 */
static loop_variable *
get_loop_var(nir_ssa_def *value, nir_loop_info_state *state)
{
   loop_variable *var = &state->info.def_infos[value->index];
   return var;
}

static inline void
add_ssa_def_to_process_list(nir_ssa_def *def, nir_loop_info_state *state)
{
   loop_variable *var = get_loop_var(def, state);
   LIST_ADD(var->process_link, state->process_list);
}

static inline void
add_ssa_defs_in_block_to_process_list(nir_block *block, nir_loop_info_state *state)
{
   nir_foreach_instr(block, instr)
      nir_foreach_ssa_def(instr, add_ssa_def_to_process_list, state);
}

static inline void
foreach_block_in_loop_outer_layer(nir_loop *loop, nir_foreach_block_cb cb, void *state)
{
      foreach_list_typed_safe(nir_cf_node, node, node, &loop->body) {
         if (node->type == nir_cf_node_block)
            cb(nir_cf_node_as_block(node), state);
      }
}

static inline bool
is_ssa_def_invariant(loop_variable *var, nir_loop_info_state *state)
{

   if (var->info->type == invariant)
      return true;

   if (var->in_loop == false) {
      var->info->type = invariant;
      return true;
   }

   assert(var->info->type != basic_induction && var->info->type != derived_induction);

   /*
    * Process value
    *
    * There are three rules to follow:
    *    Are all the operands from outside the loop?
    *    Are all the operands loop invariant?
    *    Or is it a combination of the two?
    *       Then it is loop invariant
    *       (The "combination of the two" part is solved by marking all
    *        variables that are outside the loop as invariant)
    *    If one of the operands are induction variables
    *       Can not be loop invariant (But we don't know this yet, so it only
    *       makes sense as some king of test / validation)
    *
    * An expression is invariant in a loop L iff:
    *  (base cases)
    *    – it’s a constant
    *    – it’s a variable use, all of whose single defs are outside of L
    *  (inductive cases)
    *    – it’s a pure computation all of whose args are loopinvariant
    *    – it’s a variable use whose single reaching def, and the
    *          rhs of that def is loop-invariant
    *    - Phi-functions are not pure, so they can "fuck things up"
    */

   nir_ssa_def *def = var->info->def;

   switch (def->parent_instr.type)
   case nir_instr_type_alu: {
      nir_alu_instr *alu = nir_instr_as_alu(def.parent_instr);
      loop_variable *src;

      for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {
         src = get_loop_var(alu->src[i].src.ssa, state);
         /*
          * We have two possibilities; optimistic or pessimistic
          * We can solve it mostly in the way it is solved for SCCP
          * or we can use a system of recursion. This is recursive as is.
          * One problem is that this is pessimistic, and so we may not
          * detect all the possible loop invariants.
          */
         if (!is_ssa_def_invariant(src, state))
            return false;
      }
      var->info->type = invariant;
      return true;
   }

   /*
    * Phis shouldn't really be invariant except if they are pointless
    * (One operand is invariant, the other is the phi itself)
    * I think these types of phi's are removed already though, so
    * there is no point in checking for that.
    */
   case nir_instr_type_phi:
//         nir_phi_instr *phi = nir_instr_as_phi(def.parent_instr);
//         return is_phi_invariant(phi, state);
      return false;

   case nir_instr_type_load_const:
      var->info->type = invariant;
      return true;

   default:
      var->info->type = undefined;
      /*
       * XXX: we need to handle other users than alu's probably.
       * Uniform loads may be of interest?
       */
      return false;
}

static void
compute_invariance_information(nir_loop_info_state *state)
{
   /*
    * Add all entries in the outermost part of the loop
    * to the processing_list.
    */
   foreach_block_in_loop_outer_layer(state->info->loop,
                                     add_ssa_defs_in_block_to_process_list,
                                     state);

   /*
    * do {
    *    change = false;
    *    for_each_in_list(process_list) {
    *       if (operand = const || !in_loop || invariant) {
    *          add to invariant list
    *          remove from process list
    *          if (conditional)
    *             add then and else branch instructions to process list
    *             (but not nested ones, as we don't know if the conditions
    *              inside the branches are invariant)
    *          changes = true;
    *       }
    *    }
    * } while changes
    *
    * Phi nodes are not invariant (well, they can be if only one
    * of the branches it is merging is executed in the loop;
    * The condition for the divergence is invariant)
    *
    * This algorithm is kinda slow as it retries all the variables
    * upon each run of the pass. That's not cool. Could make it demand driven
    * and use a worklist similar to the way done in SCCP.
    *
    * XXX: We might just say that "anything that does not have a phi is invariant" ?
    *
    */

   boolean changes;
   loop_variable *var;

   do {
      changes = false;
      LIST_FOR_EACH_ENTRY(var, state->process_list, info->process_link) {
         if (is_ssa_def_invariant(var, state)) {
            LIST_ADD(var->invariant_link, state->info->invariant_list);
            LIST_DEL(var->process_link);
            if (var->info->def->if_uses) {
               /*
                * We can possibly add the then and else branch to the list
                * of variables to be processed. It should be noted that
                * we should not add conditionals inside this block for the
                * same reason we did not initially add this block.
                * This will recurse, and so if there are conditionals inside
                * this if that we resolve then that conditional will hit
                * this path, and so those blocks will also be added.
                */
            }

            changes = true;
         }
      }
   } while (changes);
}

static inline nir_loop_variable_type
get_ssa_def_variable_type(nir_ssa_def *def, nir_loop_info_state *state)
{
   return get_loop_var(def, state)->info->type;
}

static inline bool
is_ssa_def_basic_induction_var(nir_ssa_def *def, nir_loop_info_state *state)
{
   return (get_ssa_def_variable_type(def, state) == basic_induction);
}

static inline bool
is_ssa_def_derived_induction_var(nir_ssa_def *def, nir_loop_info_state *state)
{
   return (get_ssa_def_variable_type(def, state) == derived_induction);
}

static inline bool
is_ssa_def_invariant(nir_ssa_def *def, nir_loop_info_state *state)
{
   return (get_ssa_def_variable_type(def, state) == invariant);
}

static inline bool
is_var_alu(loop_variable *var)
{
   return (var->info->def->parent_instr->type == nir_instr_type_alu);
}

static inline bool
is_var_phi(loop_variable *var)
{
   return (var->info->def->parent_instr->type == nir_instr_type_phi);
}

static inline bool
is_var_basic_induction_var(loop_variable *var, nir_loop_info_state *state)
{
   nir_alu_instr *instr;
   nir_ssa_def *def;

   if (var->info->type == basic_induction)
      return true;

   if (var->info->type == derived_induction || var->info->type == invariant)
      return false;

   /*
    * This might not be the best way to go about it. Might instead
    * want to check if it is phi-instruction, and if it is check if
    * it is an induction variable. Or we can use both. Who knows?
    */

   /*
    * Don't need to check if it is phi, as that is the way we decide what
    * type of induction variable we want to check for.
    */
//   if (var->info->def->parent_instr->type == nir_instr_type_phi) { // This line can be removed since we know it is a phi. This is of course only if we decide on detection basic induction variables only on the phi instruction
      nir_phi_instr *phi = nir_instr_as_phi(var->info->def->parent_instr);
      boolean recursive_assignment = false;
      boolean invariant_operand = false;
      boolean valid_operation = false;
      boolean phi_src_outside_loop = false;
      nir_foreach_phi_src(phi, src) {
         loop_variable *src_var = get_loop_var(src->src.ssa, state);
         if (src_var->in_loop == false)
            phi_src_outside_loop = true;

         if (is_var_alu(src_var)) {
            nir_alu_instr *alu = nir_instr_as_alu(src_var->info->def->parent_instr);
            if (alu->op == nir_op_fadd || alu->op == nir_op_iadd ||
                alu->op == nir_op_fsub || alu->op == nir_op_isub ||
                alu->op == nir_op_fmul || alu->op == nir_op_imul ||
                alu->op == nir_op_fdiv || alu->op == nir_op_idiv) {
               valid_operation = true;
               if (is_ssa_def_invariant(alu->src[0].src.ssa) ||
                   is_ssa_def_invariant(alu->src[1].src.ssa))
                  invariant_operand = true;
               if (alu->src[0].src.ssa->index == src->src.ssa->index ||
                   alu->src[1].src.ssa->index == src->src.ssa->index)
                  recursive_assignment = true;
            }
         }
      }
      return recursive_assignment && invariant_operand && valid_operation && phi_src_outside_loop;
//   }
//   return false;
}

static inline bool
is_var_derived_induction_var(loop_variable *var, nir_loop_info_state *state)
{

   if (var->info->type == derived_induction)
      return true;

   if (var->info->type == basic_induction || var->info->type == invariant)
      return false;

   /*
    * Basic overview:
    * Check if outer operation is add or sub.
    *    check if one of the operands is invariant.
    *    check if other operand is basic induction variable (chatches the j = i + c case)
    *    or if it is an operation of mul or div
    *       check if one operand is basic induction variable and the other invariant. (catches the j = c1 * i + c2 case)
    *  Check if outer operations mul or div
    *     check if one operand is basic induction variable and the other invariant. (catches the j = c1 * i case)
    */

   /*
    * We want to keep track of this, at least for now, until we figure out
    * if we want to track the families of basic induction variables.
    */
   loop_variable *basic_ind;
   boolean is_derived = false;
   nir_alu_instr *alu = nir_instr_as_alu(var->info->def->parent_instr);

   switch (alu->op) {
   case nir_op_iadd:
   case nir_op_fadd:
   case nir_op_isub:
   case nir_op_fsub:
   case nir_op_imul:
   case nir_op_fmul:
   case nir_op_idiv:
   case nir_op_fdiv:
      int j;
      for (int i = 0; i < 2; i++) {
         j = 1 - i;
         /* We need an invariant operand to have a derived induction variable */
         if (is_ssa_def_invariant(alu->src[i].src.ssa)) {

            /* If the other variable is basic induction variable we have
             * ourselves a derived induction variable */
            if (is_ssa_def_basic_induction_var(alu->src[j].src.ssa)) {
               is_derived = true;
               basic_ind = get_loop_var(alu->src[j].src.ssa, state);
               break;
            }

            /*
             * Check if the other operand is a multiply or divide that
             * consist of a basic induction variable and an invariant
             */
            if (alu->src[j].src.parent_instr->type == nir_instr_type_alu) {
               nir_alu_instr *inner_alu = nir_instr_as_alu(alu.src[j].src.parent_instr);
               switch (inner_alu->op) {
               /*
                * We could have probably also added add and sub to this
                * list, as an addition of two invariants and a basic induction
                * variable is still a derived induction variable. Another
                * possibility is to transform this into a recursive function.
                * This can allow us to get n'th order polynomials.
                */
               case nir_op_imul:
               case nir_op_fmul:
               case nir_op_idiv:
               case nir_op_fdiv:
                  int m;
                  for (int n = 0; n < 2; n++) {
                     m = 1 - i;
                     if (is_ssa_def_invariant(inner_alu->src[n].src.ssa) &&
                         is_ssa_def_basic_induction_var(inner_alu->src[m].src.ssa)) {
                        is_derived = true;
                        basic_ind = get_loop_var(inner_alu->src[m].src.ssa);
                        break;
                     }
                  }
               }
            }
         }
      }
      break;
   case nir_op_ffma:
      if (!is_ssa_def_invariant(alu->src[2].src.ssa, state))
         break;
      if (is_ssa_def_basic_induction_var(alu->src[0].src.ssa, state) &&
          is_ssa_def_invariant(alu->src[1].src.ssa, state)) {
         basic_ind = get_loop_var(alu->src[0].src.ssa, state);
         is_derived = true;
         break;
      }
      if (is_ssa_def_basic_induction_var(alu->src[1].src.ssa, state) &&
          is_ssa_def_invariant(alu->src[0].src.ssa, state)) {
         basic_ind = get_loop_var(alu->src[1].src.ssa, state);
         is_derived = true;
         break;
      }
      break;
   }

   if (is_derived)
      return true;

   return false;
}

static void
compute_induction_information(nir_loop_info_state *state)
{
   /*
    * Add all entries in the outermost part of the loop
    * to the processing_list.
    */
   foreach_block_in_loop_outer_layer(state->info->loop,
                                     add_ssa_defs_in_block_to_process_list,
                                     state);
   /*
    * Here we should probably also run through all instructions in the list
    * once to check if any of them are invariant conditionals for an if.
    * Then we can add the branches to the analysis, as they are invariant.
    */

   /*
    * Start running the induction variable routine.
    */
   boolean changes;
   loop_variable *var;

   do {
      changes = false;
      LIST_FOR_EACH_ENTRY(var, state->process_list, info->process_link) {

         /*
          * It can't be an induction variable if it is invariant,
          * so there is no point in checking. Remove it from the list
          * so we avoid checking it once more later on.
          */
         if (var->info->type == invariant) {
            LIST_DEL(var->process_link);
            continue;
         }

         if (is_var_phi(var)) {
            /*
             * We are really only interested in checking phi's for the
             * basic induction variable case as that is simple to detect
             */
            if (is_var_basic_induction_var(var, state)) {
               // Add to a induction-variable-list?
               LIST_DEL(var->process_link);
               changes = true;
            }
         }
         if (is_var_alu(var)) {
            /*
             * Derived induction variables are linear, and so must be alu's.
             */
            if (is_var_derived_induction_var(var, state)) {
               // Add to a induction-variable-list?
               LIST_DEL(var->process_link);
               changes = true;
            }
         }
      }
   } while (changes);
}

static void
mark_ssa_def_as_in_loop(nir_ssa_def *def, nir_loop_info_state *state)
{
   loop_variable *var = get_loop_var(def, state);
   var->in_loop = true;
}

static void
mark_block_as_in_loop(nir_block *block, nir_loop_info_state *state)
{
   nir_foreach_instr(block, instr)
      nir_foreach_ssa_def(instr, mark_ssa_def_as_in_loop, state);
}

static void
initialize_ssa_def(nir_ssa_def *def, nir_loop_info_state *state)
{
   loop_variable *var = get_loop_var(def, state);

   var->in_loop = false;
   var->info->def = def;

   if (def->parent_instr->type == nir_instr_type_load_const) {
      var->info->type = invariant;
   } else {
      var->info->type = undefined;
   }
}

static void
initialize_block(nir_block *block, nir_loop_info_state *state) {
   nir_foreach_instr(block, instr) {
      nir_foreach_ssa_def(instr, initialize_ssa_def, block);
   }
}

static nir_loop_info
get_loop_info(nir_function_impl *impl, nir_loop *loop)
{
   void *mem_ctx;

   nir_loop_info info;
   nir_loop_info_state state;
   state->info = &info;

  /* Set up an array of all ssa-values and corresponding loop
   * information variables. This is used to hold useful information.
   */
   loop_variable *all_vars;
   state->all_vars = all_vars;
   all_vars = rzalloc_array(mem_ctx, struct loop_variable,
                                 impl.ssa_alloc);

   // A list of the loop_vars in the loop
   struct list_head loop_vars;
   LIST_INITHEAD(loop_vars);
   state->loop_vars = loop_vars;

   // A list of the loop_vars to process
   struct list_head process_list;
   LIST_INITHEAD(process_list);
   state->process_list = process_list;

   /*
    * Initialize all variables to "outside_loop".
    */
   nir_foreach_block(impl, initialize_block, state);

   /*
    * Marking all instructions in the loop as in_loop.
    * This simplifies checking if instructions are in the loop.
    */
   nir_foreach_block_in_cf_node(loop->cf_node, mark_block_as_in_loop, state);

   /*
    * Need to compute invariance information before induction
    * as the induction analysis relies on invariance information
    */
   compute_invariance_information(state);

   /*
    * We may now have filled the process_list with instructions from inside
    * the nested blocks in the loop. Remove all instructions from the list
    * before we start computing induction information. We can probably just
    * do LIST_INIT and leave all as we will not be referencing them until
    * we add them to the list again.
    */
   LIST_INIT(process_list);

   /*
    * We have the invariance information, and so we can compute the
    * state of, and detect, different induction variables.
    */
   compute_induction_information(state);

   return info;
}

nir_loop_analyze_impl(nir_function_impl *impl)
{
   loop_analyze_state state;

   state.mem_ctx = ralloc_parent(impl);
   state.impl = impl;

   /*
    * To analyze function
    *    add loops to loop_list
    *       start with the inner-upper-most loop
    *    while loops in loop_list
    *       pick loop of loop_list
    *       run analyze-loop
    */
   state.vars = rzalloc_array(state.mem_ctx, struct loop_variable_entry,
                                 impl.ssa_alloc);


   // XXX: Probably removable
   nir_foreach_block(impl, initialize_block, state);

   /*
    * Run a snippet to find loops and add them to the list
    * The inner-most loop should be first in the list so we can process
    * that first afterwards.
    */
   state.loops = get_loops_ordered(impl, state.mem_ctx);

   /*
    * We can now probably take one loop from the list and initialize it.
    * We should have already initialized all the values to "outside_loop"
    * and then we set those values that are inside the loop to "inside_loop".
    *
    * We run through all of the variables inside the loop to check if they
    * are used outside the loop. If they are we insert an intermediate phi
    * just outside the loop. Inserting phi's should be safe to do without
    * regenerating all our information. However, we end up messing up
    * our array of loop_variables, as there our now more variables
    * outside the loop. These are however not "sources" in our loop, and so
    * we do not need their information to calculate invariance information.
    * We can therefore safely proceed with calculating invariance information.
    *
    * We can possibly also calculate the induction variable information.
    * When this is done we should repopulate our lists of variables. There are
    * some important things that need to be considered.
    *
    * This can now be an "outer loop" in a loop nest. We should not add the
    * instructions in the inner loop(s) to our list of values to process.
    * If we do we will get the wrong information for them (they will be marked
    * invariant). We might want some kind of cool variable to tell us that
    * this is inside a nested loop, so that we can skip it easily. The reason
    * being it might end up being a src for something in the later part of the,
    * and so we can wrongly assume it is invariant, even though that is only the
    * case for the inner-most loop.
    *
    * We may consider using the growing array Jason started to implement. That
    * way we can retain all our information and at the same time just add the
    * new phi's we just inserted to the array and get an array of all values.
    */


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



/* -
 * block block_4:
   /* preds: block_3
   vec1 ssa_11 = fmov -ssa_715.yyzw
   /* succs: block_5
   loop {
      block block_5:
      /* preds: block_4 block_8
      vec1 ssa_699 = phi block_4: ssa_686, block_8: ssa_57
      vec1 ssa_228 = phi block_4: ssa_11, block_8: ssa_76
      vec1 ssa_15 = flt ssa_715.yyzw, ssa_228.xxxx
      /* succs: block_6 block_7
      if ssa_15 {
         block block_6:
         /* preds: block_5
         break
         /* succs: block_9
      } else {
         block block_7:
         /* preds: block_5
         /* succs: block_8
      }
      block block_8:
      /* preds: block_7

      vec1 ssa_76 = fadd ssa_228.xxxx, ssa_210.xxxx
      /* succs: block_5
   }
 */



/*
 * Add outer block instructions to processing_list.
 *
 * For each block in loop
 *    for each ssa-def in block
 *       add ssa-def to processing_list
 *       mark as in_loop
 *
 * This is fine enough. But to actually calculate invariance information
 * we need to be a bit smarter. We need to check the conditional of any
 * diverging control flow inside the loop. If the conditional is invariant
 * then we can add the defs in the then and else branch to the list of
 * functions that we want to analyze. This can, in practice, be done by
 * checking each instruction we set to invariant if it is a condition
 * for a conditional or not. I'm not actually sure though if this is
 * necessary. It is freakin' hard to find good papers on how to find
 * loop invariants, and what to mark.
 *
 * For the time being I see no reason why this shouldn't work.
 * I'll need to play around with it some though, both in my head and code.
 */
