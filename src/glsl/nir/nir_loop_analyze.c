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
 * basic induction variable:
 *    i = i + c
 *    i = i - c
 *    i = i * c        XXX: Need to figure out if this is actually legal
 *    i = i / c
 *    where c is loop invariant or constant
 *    defined only once in a loop
 *
 * derived induction variable
 *    j = i * c1 + c2
 *    j = i / c1 + c2
 *    j = i * c1 - c2
 *    j = i / c1 - c2
 *    where c1 and c2 are loop invariant or constant
 *    defined only once in a loop
 *    i is basic induction variable
 *
 *    triple(i, c1, c2) where i = basic induction variable, c1 and c2 invariant.
 *    ^^ XXX: This has not been explored, but may prove usefull.
 *
 * Family of induction variable B is the set of induction
 * variables A that are a linear function of B
 *
 * This implementation is kinda slow as it retries all variables in the loop
 * each time it has progressed (for invariant and induction detection).
 * Could make it demand driven and use a worklist. However, the process
 * of getting the users of each ssa-def might prove to be just as expensive as
 * the few extra variables checked, as there are usually few instructions in
 * the loops we encounter. Therefore the KISS method has been chosen as for now.
 *
 * If one of the operands is an induction variable
 *   --> Can not be loop invariant.
 * Can be used as a validation after the pass has run.
 *
 * We can check the conditional of any diverging control flow in the loop.
 * If the conditional is invariant then we can add the defs in the
 * then and else branch to the list of defs to analyze.
 * This can, in practice, be done by checking each def we set to invariant
 * if it is a condition for an if.
 * This may be unnecessary if we implement loop unswitching.
 * Then we will split the loop in two and remove the conditional in the loop.
 */

/*
 * Example of loop in NIR-ssa
 *
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


#include "nir.h"
#include "util/list.h"

typedef enum {
   undefined,
   invariant,
   basic_induction,
   derived_induction,
   canonical_induction // XXX: This may not be wanted? Not used as of yet
} nir_loop_variable_type;

/*
 * XXX: This whole struct may actually be dropped, but it may prove useful
 * to have easy access to the ssa-def it represents.
 */
typedef struct {
   /* The ssa_def associated with this info */
   nir_ssa_def *def;

   /* The type of this ssa_def */
   nir_loop_variable_type *type;
} nir_loop_ssa_def_info;

typedef struct {
   /* The loop we store information for */
   nir_loop *loop;

   /* Array of info's for each def in loop
    * XXX: We probably want to change to a list.
    * We should figure out if we actually want to keep this or if
    * we want to store something else like the whole loop-variable.
    * Or maybe we want to split some of that info into the ssa-def-info
    * and have some in the loop-variable. The thought is to have an info-struct
    * that holds the "public" information, and a struct wrapping it that is used
    * in the analysis and holds the information only this pass cares about.
    */
   nir_loop_ssa_def_info *def_infos;
   /* XXX: Might not be needed if we go the list-way */
   uint32_t num_ssa_defs_in_loop;

   /* In the case of a nested loop this stores the surrounding loop */
   nir_loop *parent_loop;

   /* The nesting depth of this loop. Starts at 1 (blocks in main() are 0) */
   uint32_t nest_depth;

   /* How many times the loop is run (if known) */
   uint32_t trip_count;
   boolean is_trip_count_known;

   /* The ssa_defs that are invariant */
   struct list_head invariant_list;

   /* The ssa_defs that are induction variables */
   struct list_head induction_list;
} nir_loop_info;

typedef struct {
   nir_loop_ssa_def_info *info;
   struct list_head process_link;
   struct list_head loop_link;
   struct list_head invariant_link;
   struct list_head induction_link;
   boolean in_loop;
   boolean in_conditional_block;
   boolean in_nested_loop;
} loop_variable;

typedef struct {
   nir_if *nif;
   /*
    * Some more suitable fields like maybe indicated trip-count?
    */
   loop_variable *condition_var;
} nir_loop_terminator;

typedef struct {
   nir_loop_info *info;

   // Loop_variable for all ssa_defs in function
   loop_variable *all_vars;

   /*
    * A list of the loop_vars in the loop
    * XXX: This is not used as of now and can probably be dropped.
    * We already have the list of induction variables, so might be "double info".
    * Should at least be moved into nir_loop_info
    */
   struct list_head loop_vars;

   // A list of the loop_vars to process
   struct list_head process_list;

   struct list_head loop_states_link;
} nir_loop_info_state;

typedef struct {
   void *mem_ctx;
   nir_function_impl *impl;
   uint32_t max_nesting_depth;    // XXX: This is not used either

   // A list of the loops in the function
   struct list_head loop_states;
} nir_loop_info_pass_state;

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

mark_block_as_in_conditional_block(nir_block *block, nir_loop_info_state *state)
{
   nir_foreach_instr(block, instr)
      nir_foreach_ssa_def(instr, mark_ssa_def_as_in_conditional_block, state);
}

mark_block_as_nested(nir_block *block, nir_loop_info_state *state)
{
   nir_foreach_instr(block, instr)
      nir_foreach_ssa_def(instr, mark_ssa_def_as_nested, state);
}

static void
mark_ssa_def_as_in_loop(nir_ssa_def *def, nir_loop_info_state *state)
{
   loop_variable *var = get_loop_var(def, state);
   var->in_loop = true;
}

static void
mark_ssa_def_as_nested(nir_ssa_def *def, nir_loop_info_state *state)
{
   loop_variable *var = get_loop_var(def, state);
   var->in_nested_loop = true;

}

static void
mark_ssa_def_as_in_conditional_block(nir_ssa_def *def, nir_loop_info_state *state)
{
   loop_variable *var = get_loop_var(def, state);
   var->in_conditional_block = true;

}

static void
initialize_loop(nir_loop_info_state *state)
{
   foreach_list_typed_safe(nir_cf_node, node, node, state->info->loop->body) {
      switch (node->type) {
      case nir_cf_node_block:
         nir_foreach_instr(nir_cf_node_as_block(node), instr) {
            nir_foreach_ssa_def(instr, add_ssa_def_to_process_list, state);
            nir_foreach_ssa_def(instr, mark_ssa_def_as_in_loop, state);
         }
         break;
      case nir_cf_node_if:
         nir_foreach_block_in_cf_node(node, mark_block_as_in_conditional_block, false, state);
         break;
      case nir_cf_node_loop:
         nir_foreach_block_in_cf_node(node, mark_block_as_nested, false, state);
         break;
      }
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
    * There are three rules to follow:
    *    Are all the operands from outside the loop?
    *    Are all the operands loop invariant?
    *    Or is it a combination of the two?
    *       Then it is loop invariant
    *       (The "combination of the two" part is solved by marking all
    *        variables that are outside the loop as invariant)
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
          *
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
      /* XXX: we need to handle other users than alu's probably. */
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

   boolean changes;
   loop_variable *var;

   do {
      changes = false;
      list_for_each_entry_safe(loop_variable, var, state->process_list, process_link) {

         if (var->in_conditional_block || var->in_nested_loop)
            continue;

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
                * this that we resolve then that conditional will hit
                * this path, and so those blocks will also be analyzed.
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

   nir_phi_instr *phi = nir_instr_as_phi(var->info->def->parent_instr);

   boolean recursive_assignment = false;
   boolean invariant_operand = false;
   boolean valid_operation = false;
   boolean phi_src_outside_loop = false;

   nir_foreach_phi_src(phi, src) {
      loop_variable *src_var = get_loop_var(src->src.ssa, state);

      // If one of the sources is in a conditional or nested then panick
      if (src_var->in_conditional_block || src_var->in_nested_loop)
         return false;

      if (src_var->in_loop == false)
         phi_src_outside_loop = true;

      if (is_var_alu(src_var)) {
         nir_alu_instr *alu = nir_instr_as_alu(src_var->info->def->parent_instr);
         if (alu->op == nir_op_fadd || alu->op == nir_op_iadd ||
             alu->op == nir_op_fsub || alu->op == nir_op_isub ||
             alu->op == nir_op_fmul || alu->op == nir_op_imul ||
             alu->op == nir_op_fdiv || alu->op == nir_op_idiv) {
            /* XXX: Needs to figure out if mul and div should he included */
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
   return recursive_assignment && invariant_operand &&
          valid_operation && phi_src_outside_loop;
}

static inline bool
is_var_derived_induction_var(loop_variable *var, nir_loop_info_state *state)
{

   if (var->info->type == derived_induction)
      return true;

   if (var->info->type == basic_induction || var->info->type == invariant)
      return false;

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
    * Add all entries in the outermost part of the loop to the processing list
    * Mark the entries in conditionals or in nested loops accordingly.
    */
   initialize_loop(state);

   /*
    * Here we should probably also run through all instructions in the list
    * once to check if any of them are invariant conditionals for an if.
    * Then we can add the branches to the analysis, as they are invariant.
    * Might not be usefull if we decide to add loop unswitching
    */

   boolean changes;
   loop_variable *var;

   do {
      changes = false;
      list_for_each_entry_safe(loop_variable, var, state->process_list, process_link) {
         /*
          * It can't be an induction variable if it is invariant,
          * so there is no point in checking. Remove it from the list
          * so we avoid checking it again. Also we don't want to deal
          * with things in nested loops or conditionals.
          */
         if (var->info->type == invariant || var->in_conditional_block || var->in_nested_loop) {
            LIST_DEL(var->process_link);
            continue;
         }

         if (is_var_phi(var)) {
            /*
             * We are really only interested in checking phi's for the
             * basic induction variable case as that is simple to detect.
             * All basic induction variables needs to have a phi node.
             * XXX: Is this assumption 100% correct?
             */
            if (is_var_basic_induction_var(var, state)) {
               /* We also need to follow the phi to the alu_op
                * or we can do this in the pass where we find it is induction
                */
               LIST_DEL(var->process_link);
               LIST_ADD(var->induction_link, state->info->induction_list);
               changes = true;
            }
         }

         if (is_var_alu(var)) {
            /*
             * Derived induction variables are linear, and so must be alu's.
             */
            if (is_var_derived_induction_var(var, state)) {
               /* We also need to follow the phi to the alu_op
                * or we can do this in the pass where we find it is induction
                */
               LIST_DEL(var->process_link);
               LIST_ADD(var->induction_link, state->info->induction_list);
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
   nir_foreach_instr(block, instr) {
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

static bool
is_loop_terminator(nir_if *nif)
{
   /*
    * If there is stuff in the else-block that means that this is not
    * a simple break on true if-statement and so we bail.
    * XXX: This is strictly copied from the glsl loop analysis pass,
    * but the assumption should probably still be valid.
    */
   if (!exec_list_is_empty(nif->else_list))
      return false; // There is stuff in the then-list. Therefore not a simple conditional break.

   nir_cf_node *first_then = nir_if_first_then_node(nif);

   nir_block *first_then_block = nir_cf_node_as_block(first_then);

   nir_instr *first_instr = nir_block_first_instr(first_then_block);

   if (first_instr->type == nir_jump_instr) {
      nir_jump_instr *jump = nir_instr_as_jump(first_instr);
      if (jump->type == nir_jump_break)
         return true;
   }

   return false;
}

static void
get_loop_terminators(nir_loop_info_state *state)
{
   foreach_list_typed_safe(nir_cf_node, node, node, state->info->loop->body) {
      if (node->type == nir_cf_node_if) {
         if (is_loop_terminator(nir_cf_node_as_if(node))) {
            /*
             * ralloc a nir_loop_terminator
             * Attach it to the list of terminators
             * Get the loop_var for the conditional and set it in the struct XXX: Might prove to be unnecessary
             */
         }
      }
   }
}

static void
get_loop_info(nir_loop_info_state *state, nir_function_impl *impl)
{
   /*
    * Initialize all variables to "outside_loop".
    */
   nir_foreach_block(impl, initialize_block, state);

   /*
    * Marking all instructions in the loop as in_loop.
    * This simplifies checking if instructions are in the loop.
    */
   nir_foreach_block_in_cf_node(state->info->loop->cf_node,
                                mark_block_as_in_loop, state);

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
   LIST_INIT(state->process_list);

   /*
    * We have the invariance information, and so we can compute the
    * state of, and detect, different induction variables.
    */
   compute_induction_information(state);

   /*
    * We should now gather a list of the loop's terminators.
    * This just writes to the state (eventually)
    * Might want to rename the function for clarity
    */
   get_loop_terminators(state);

   /*
    * We can now run through each of the terminators of the loop
    * and try to infer a possible trip-count.
    * We need to check them all, and set the lowest trip-count as
    * the trip-count of our loop as that is always the place it breaks.
    * If one of the terminators has an undecidable trip-count then we
    * can not safely assume anything about the duration of the loop.
    * We can therefore not do much interesting.
    * There are possibilities for doing some kind of unrolling even if
    * one does not have a set unroll-count. This involves a switch-statement
    * that has the same amount of cases as the unroll-factor, a so called
    * "Duff's Device".
    */
}

static nir_loop_info_state *
initialize_loop_info_state(nir_loop *loop, void *mem_ctx, nir_function_impl *impl)
{
   nir_loop_info *info;
   nir_loop_info_state *state;
   loop_variable *loop_vars;
   nir_loop_ssa_def_info *ssa_infos;
   info = ralloc(mem_ctx, struct nir_loop_info);
   state = ralloc(mem_ctx, struct nir_loop_info_state);
   loop_vars = rzalloc_array(mem_ctx, struct loop_variable, impl->ssa_alloc);
   ssa_infos = rzalloc_array(mem_ctx, struct nir_loop_ssa_def_info, impl->ssa_alloc);
   state->loop_vars = loop_vars;
   state->info = info;
   state->info->def_infos = ssa_infos;

   for (int i = 0; i < impl->ssa_alloc; i++)
      loop_vars[i].info = ssa_infos[i];

   LIST_INITHEAD(state->process_list);

   return state;
}

/*
 * XXX: This does a lot of list traversal after the initial collection
 * of loops from the blocks. However, this is probably not an issue as
 * we don't expect to see a lot of loops in our shaders, and so this is
 * not really a dominant part of this pass's cpu-time.
 */
static struct list_head *
get_loops_ordered(nir_function_impl *impl, void *mem_ctx)
{
   //nir_loop_info_state *head = ralloc(mem_ctx, struct nir_loop_info_state);
   struct list_head *head;
   LIST_INITHEAD(head);

   bool loop_found = false;
   /*
    * Find all loops and add them to the list
    */
   foreach_list_typed(nir_cf_node, cur, node, impl->body) {
      if (cur->type == nir_cf_node_loop) {
         nir_loop *loop = nir_cf_node_as_loop(cur);
         nir_loop_info_state *loop_state = initialize_loop_info_state(loop, mem_ctx, impl);
         loop_state->info->loop = loop;
         LIST_ADD(loop_state->loop_states_link, head);
         loop_found = true;
      }
   }

   if (!loop_found)
      return NULL;

   /*
    * Collect information about which loops have another loop as its parent
    */
   nir_loop_info_state *state;
   nir_cf_node *node;
   list_for_each_entry_safe(nir_loop_info_state, state, head, loop_states_link) {
      node = state->info->loop->cf_node;
      while (!nir_cf_node_is_first(node->parent)) {
         if (node->type == nir_cf_node_loop) {
            state->info->parent_loop = nir_cf_node_as_loop(node);
         }
         node = node->parent;
      }
   }

   /*
    * Calculate the nesting depth of all loops based
    * on the information we gathered about the loops' parents
    */
   list_for_each_entry_safe(nir_loop_info_state, state, head, loop_states_link) {
      nir_loop_info_state *copy_state = state;
      int i = 1;
      /* If we have a parent then iterate depth, and "recurse" */
      while (copy_state->info->parent_loop != NULL) {
         copy_state = copy_state->info->parent_loop;
         i++;
      }
      state->info->nest_depth = i;
   }

   /*
    * Since we now have the loop depth it is trivial to sort the list
    * according to the loop depth. This will let us get the list ordered
    * from innermost to outermost loop.
    */
   boolean changes;
   do {
      changes = false;
      list_for_each_entry_safe(nir_loop_info_state, cur, head, loop_states_link) {
         nir_loop_info_state *next = LIST_ENTRY(nir_loop_info_state, cur->loop_states_link.next, loop_states_link); // XXX: This use of the list getter is porbably wrong on so many levels.
         if (cur->info->nest_depth < next->info->nest_depth) {
            LIST_DEL(next);
            LIST_ADD(next, head);
            changes = true;
         }
      }
   } while (changes);

   return head;
}

/*
 * Gets loop info for all loops in a nir_function_impl
 */
bool
nir_loop_analyze_impl(nir_function_impl *impl)
{
   nir_loop_info_pass_state state;

   state.mem_ctx = ralloc_parent(impl);
   state.impl = impl;

   /*
    * Run a snippet to find loops and add them to the list
    * The inner-most loop should be first in the list so we can process
    * that first afterwards.
    */
   state.loop_states = get_loops_ordered(impl, state.mem_ctx);
   if (!state.loop_states)
      return false;

   /*
    * Method for getting LCSSA:
    *
    * Take one loop from the list and initialize it.
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
    * We may consider using the growing array Jason started to implement. That
    * way we can retain all our information and at the same time just add the
    * new phi's we just inserted to the array and get an array of all values.
    */

   nir_loop_info_state *loop_state;
   list_for_each_entry(nir_loop_info_state, loop_state, state.loop_states, loop_states_link) {
      get_loop_info(loop_state, impl);
   }

   return true;;
}

/*
 * Function for getting loop information for a complete shader.
 * This depends on how we want to use the pass.
 * Might want it to be a utility instead of saving stuff in the
 * metadata as we will be constantly invalidating the metadata during opt.
 */
bool
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
ir_rvalue *
get_basic_induction_increment(ir_assignment *ir, hash_table *var_hash)
{
   /* The RHS must be a binary expression.
    *
   ir_expression *const rhs = ir->rhs->as_expression();
   if ((rhs == NULL)
       || ((rhs->operation != ir_binop_add)
      && (rhs->operation != ir_binop_sub)))
      return NULL;

   /* One of the of operands of the expression must be the variable assigned.
    * If the operation is subtraction, the variable in question must be the
    * "left" operand.
    *
   ir_variable *const var = ir->lhs->variable_referenced();

   ir_variable *const op0 = rhs->operands[0]->variable_referenced();
   ir_variable *const op1 = rhs->operands[1]->variable_referenced();

   if (((op0 != var) && (op1 != var))
       || ((op1 == var) && (rhs->operation == ir_binop_sub)))
      return NULL;

   ir_rvalue *inc = (op0 == var) ? rhs->operands[1] : rhs->operands[0];

   if (inc->as_constant() == NULL) {
      ir_variable *const inc_var = inc->variable_referenced();
      if (inc_var != NULL) {
    loop_variable *lv =
       (loop_variable *) hash_table_find(var_hash, inc_var);

         if (lv == NULL || !lv->is_loop_constant()) {
            assert(lv != NULL);
            inc = NULL;
         }
      } else
    inc = NULL;
   }

   if ((inc != NULL) && (rhs->operation == ir_binop_sub)) {
      void *mem_ctx = ralloc_parent(ir);

      inc = new(mem_ctx) ir_expression(ir_unop_neg,
                   inc->type,
                   inc->clone(mem_ctx, NULL),
                   NULL);
   }

   return inc;
}

*/
