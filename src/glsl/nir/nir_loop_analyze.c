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

/* If one of the operands is an induction variable
 *   --> Can not be loop invariant.
 * Can be used as a validation after the pass has run.
 *
 * We don't do anything about invariants in conditional branches yet. We can
 * check for invariance in conditional blocks if the condition itself is
 * invariant. If we implement loop unswitching this will not be necessary,
 * as the unswitching will eliminate the conditional check and leave us with
 * only the then- or else-branch inlined in the loop.
 */
#include "nir.h"

typedef struct {
   /* A link for the work list */
   struct list_head process_link;

   bool in_loop;

   nir_loop_variable *nir_loop_var;
} loop_variable;

typedef struct {

   /* The loop we store information for */
   nir_loop *loop;

   /* Loop_variable for all ssa_defs in function */
   loop_variable *loop_vars;

   /* Loop_variable for all ssa_defs in function */
   nir_loop_variable *nir_loop_vars;

   /* A list of the loop_vars to analyze */
   struct list_head process_list;

   nir_loop_info *info;
} loop_info_state;

static loop_variable *
get_loop_var(nir_ssa_def *value, loop_info_state *state)
{
   return &(state->loop_vars[value->index]);
}

static nir_loop_variable *
get_nir_loop_var(nir_ssa_def *value, loop_info_state *state)
{
   return &(state->nir_loop_vars[value->index]);
}

typedef struct {
  loop_info_state *state;
  bool mark_nested;
  bool mark_in_conditional;
} init_loop_state;

static bool
init_loop_def(nir_ssa_def *def, void *void_init_loop_state)
{
   init_loop_state *loop_init_state = void_init_loop_state;
   loop_variable *var = get_loop_var(def, loop_init_state->state);

   /* Add to the tail of the list. That way we start at the beginning of the
    * defs in the loop instead of the end when walking the list. This means
    * less recursive calls. Only add defs that are not in nested loops or
    * conditional blocks.
    */
   if (!(loop_init_state->mark_in_conditional ||
         loop_init_state->mark_nested))
      LIST_ADDTAIL(&(var->process_link),
                   &(loop_init_state->state->process_list));

   if (loop_init_state->mark_in_conditional)
      var->nir_loop_var->in_conditional_block = true;

   if (loop_init_state->mark_nested)
      var->nir_loop_var->in_nested_loop = true;

   var->in_loop = true;

   return true;
}

static bool
init_loop_block(nir_block *block, void *void_init_loop_state)
{
   init_loop_state *loop_init_state = void_init_loop_state;

   nir_foreach_instr(block, instr)
      nir_foreach_ssa_def(instr, init_loop_def, loop_init_state);

   return true;
}

static inline bool
is_var_alu(loop_variable *var)
{
   return (var->nir_loop_var->def->parent_instr->type == nir_instr_type_alu);
}

static inline bool
is_var_phi(loop_variable *var)
{
   return (var->nir_loop_var->def->parent_instr->type == nir_instr_type_phi);
}

static inline bool
is_ssa_def_invariant(nir_ssa_def *def, loop_info_state *state)
{
   loop_variable *var = get_loop_var(def, state);

   if (var->nir_loop_var->type == invariant)
      return true;

   if (!var->in_loop) {
      var->nir_loop_var->type = invariant;
      return true;
   }

   if (var->nir_loop_var->type == basic_induction)
      return false;

   if (is_var_alu(var)) {
      nir_alu_instr *alu = nir_instr_as_alu(def->parent_instr);

      for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {
         if (!is_ssa_def_invariant(alu->src[i].src.ssa, state))
            return false;
      }
      var->nir_loop_var->type = invariant;
      return true;
   }

   /* Phis shouldn't be invariant except if one operand is invariant, and the
    * other is the phi itself. These should be removed by opt_remove_phis.
    * load_consts are already set to invariant and constant in the
    * initialization. Skip both of these, and the rest of the operations.
    */
   var->nir_loop_var->type = undefined;
   return false;
}

static void
compute_invariance_information(loop_info_state *state)
{
   /* An expression is invariant in a loop L if:
    *  (base cases)
    *    – it’s a constant
    *    – it’s a variable use, all of whose single defs are outside of L
    *  (inductive cases)
    *    – it’s a pure computation all of whose args are loop invariant
    *    – it’s a variable use whose single reaching def, and the
    *      rhs of that def is loop-invariant
    */
   bool changes;

   do {
      changes = false;
      list_for_each_entry_safe(loop_variable, var,
                               &state->process_list, process_link) {

         if (var->nir_loop_var->in_conditional_block ||
             var->nir_loop_var->in_nested_loop) {
            LIST_DEL(&var->process_link);
            continue;
         }

         if (is_ssa_def_invariant(var->nir_loop_var->def, state)) {
            LIST_DEL(&var->process_link);
            changes = true;
         }
      }
   } while (changes);
}

static inline bool
is_var_basic_induction_var(loop_variable *var, loop_info_state *state)
{
   if (var->nir_loop_var->type == basic_induction)
      return true;

   /* We are only interested in checking phi's for the basic induction
    * variable case as its simple to detect. All basic induction variables
    * have a phi node
    */
   if (!is_var_phi(var))
      return false;

   nir_phi_instr *phi = nir_instr_as_phi(var->nir_loop_var->def->parent_instr);

   nir_basic_induction_var *biv = rzalloc(NULL, nir_basic_induction_var);
   biv->phi = var->nir_loop_var;

   nir_foreach_phi_src(phi, src) {
      loop_variable *src_var = get_loop_var(src->src.ssa, state);

      /* If one of the sources is in a conditional or nested then panic */
      if (src_var->nir_loop_var->in_conditional_block ||
          src_var->nir_loop_var->in_nested_loop)
         break;

      if (!src_var->in_loop)
         biv->def_outside_loop = src_var->nir_loop_var;

      if (src_var->in_loop && is_var_alu(src_var) &&
          !src_var->nir_loop_var->in_nested_loop &&
          !src_var->nir_loop_var->in_conditional_block) {

         nir_alu_instr *alu =
               nir_instr_as_alu(src_var->nir_loop_var->def->parent_instr);

         switch (alu->op) {
         case nir_op_fadd:
         case nir_op_iadd:
         case nir_op_uadd_carry:
         case nir_op_fsub:
         case nir_op_isub:
         case nir_op_usub_borrow:
         case nir_op_fmul:
         case nir_op_imul:
         case nir_op_umul_high:
         case nir_op_fdiv:
         case nir_op_idiv:
         case nir_op_udiv:
            biv->alu_def = src_var->nir_loop_var;

            for (unsigned i = 0; i < 2; i++) {
               /* Is one of the operands invariant, and the other the phi? */
               if (is_ssa_def_invariant(alu->src[i].src.ssa, state) &&
                   alu->src[1-i].src.ssa->index == phi->dest.ssa.index)
                  biv->invariant = get_nir_loop_var(alu->src[i].src.ssa,
                                                    state);
            }
            biv->alu_op = alu->op;
            break;

         default:
            break;
         }
      }
   }

   if (biv->alu_def && biv->def_outside_loop && biv->invariant && biv->phi) {
      biv->alu_def->type = basic_induction;
      biv->phi->type = basic_induction;
      _mesa_hash_table_insert(state->info->var_to_basic_ind, biv->alu_def, biv);
      _mesa_hash_table_insert(state->info->var_to_basic_ind, biv->phi, biv);
      ralloc_adopt(state, NULL);
      return true;
   }

   /* The requirements for a basic induction variable are not fulfilled */
   ralloc_free(biv);
   return false;
}

static bool
compute_induction_information(loop_info_state *state)
{
   bool changes;
   bool found_induction_var = false;

   do {
      changes = false;
      list_for_each_entry_safe(loop_variable, var,
                               &state->process_list, process_link) {

         /* It can't be an induction variable if it is invariant. We don't
          * want to deal with things in nested loops or conditionals.
          */
         if (var->nir_loop_var->type == invariant ||
             var->nir_loop_var->in_conditional_block ||
             var->nir_loop_var->in_nested_loop) {
            LIST_DEL(&(var->process_link));
            continue;
         }

         if (is_var_basic_induction_var(var, state)) {
            /* If a phi is marked basic_ind we also mark the alu_def basic_ind
             * at the same time. It will then be detected as basic_ind here,
             * on the second passing, and be removed from the list.
             */
            LIST_DEL(&(var->process_link));
            changes = true;
            found_induction_var = true;
         }
      }
   } while (changes);
   return found_induction_var;
}

static bool
initialize_ssa_def(nir_ssa_def *def, void *void_state)
{
   loop_info_state *state = void_state;
   loop_variable *var = get_loop_var(def, state);

   var->nir_loop_var = get_nir_loop_var(def, state);

   var->in_loop = false;
   var->nir_loop_var->def = def;

   if (def->parent_instr->type == nir_instr_type_load_const) {
      var->nir_loop_var->type = invariant;
      var->nir_loop_var->is_constant = true;
   } else {
      var->nir_loop_var->type = undefined;
   }
   return true;
}

static bool
initialize_block(nir_block *block, void *void_state)
{
   nir_foreach_instr(block, instr)
      nir_foreach_ssa_def(instr, initialize_ssa_def, void_state);
   return true;
}

static bool
block_has_break_instr(nir_block *block, void *void_state)
{
   bool *found_break = void_state;
   nir_foreach_instr(block, instr) {
      if (instr->type == nir_instr_type_jump &&
          nir_instr_as_jump(instr)->type == nir_jump_break) {

         *found_break = true;
         return true;
      }
   }
   return true;
}

static bool
foreach_cf_node_ex_loop(nir_cf_node *node, nir_foreach_block_cb cb,
                        void *state)
{
   switch (node->type) {
   case nir_cf_node_block:
      return cb(nir_cf_node_as_block(node), state);

   case nir_cf_node_if: {
      nir_if *if_stmt = nir_cf_node_as_if(node);

      foreach_list_typed_safe(nir_cf_node, node, node, &if_stmt->then_list)
         if (!foreach_cf_node_ex_loop(node, cb, state))
            return false;

      foreach_list_typed_safe(nir_cf_node, node, node, &if_stmt->else_list)
         if (!foreach_cf_node_ex_loop(node, cb, state))
            return false;

      break;
   }

   default:
      break;
   }

   return false;
}

static bool
is_trivial_loop_terminator(nir_if *nif)
{
   /* If there is stuff in the else-block that means that this is not a
    * simple break on true if-statement and so we bail
    */
   foreach_list_typed_safe(nir_cf_node, node, node, &nif->else_list)
      if (node->type == nir_cf_node_block)
         nir_foreach_instr(nir_cf_node_as_block(node), instr)
            return false;

   nir_cf_node *first_then = nir_if_first_then_node(nif);
   nir_block *first_then_block = nir_cf_node_as_block(first_then);
   nir_instr *first_instr = nir_block_first_instr(first_then_block);

   if (first_instr && first_instr->type == nir_instr_type_jump &&
       nir_instr_as_jump(first_instr)->type == nir_jump_break)
      return true;

   return false;
}

static bool
find_loop_terminators(loop_info_state *state)
{
   bool success = false;
   foreach_list_typed_safe(nir_cf_node, node, node, &state->loop->body) {
      if (node->type == nir_cf_node_if) {
         nir_if *nif = nir_cf_node_as_if(node);

         /* Don't check the nested loops if there are breaks */
         bool found_break = false;
         foreach_cf_node_ex_loop(&nif->cf_node, block_has_break_instr, &found_break);

         if (!found_break)
            continue;

         /* If there is a break then we should find a terminator. If we can
          * not find a loop terminator, but there is a break-statement then
          * we should return false so that we do not try to find trip-count
          */
         if (!is_trivial_loop_terminator(nif))
            return false;

         nir_loop_terminator *terminator = rzalloc(state, nir_loop_terminator);

         list_add(&terminator->loop_terminator_link,
                  &state->info->loop_terminator_list);

         terminator->nif = nif;

         terminator->conditional_instr = nif->condition.ssa->parent_instr;
         success = true;
      }
   }
   return success;
}

static nir_basic_induction_var *
get_basic_ind_var_for_loop_var(loop_variable *var, loop_info_state *state)
{
   assert(var->nir_loop_var->type == basic_induction);

   struct hash_entry *entry =
         _mesa_hash_table_search(state->info->var_to_basic_ind,
                                var->nir_loop_var);

   return entry->data;
}

/* This function is mostly a direct port of the same functionality
 * in the GLSL compiler loop analsis pass.
 *
 * XXX: There is a major failure here. We do not handle the swizzle!
 */
static int
calculate_iterations(nir_const_value *initial, nir_const_value *step,
                     nir_const_value *limit, nir_op cond_op, nir_loop_variable *alu_def, nir_alu_instr *cond_alu)
{
   /* Superfluous assert */
   assert(initial != NULL && step != NULL && limit != NULL);

   nir_alu_instr *alu = nir_instr_as_alu(alu_def->def->parent_instr);

   /* Check both sources for the alu-op. Find which is which and
    * safe the swizzle we want to use for each of them. Do the same
    * for the comparison instruction. This means that cond_op needs
    * to be replaced with the nir_loop_variable or ssa_def equivalent.
    */

   int iter_int = 0;

   /* Unsupported alu operation */
   if (!(alu->op == nir_op_iadd || alu->op == nir_op_isub))
      return -1;

   int span = limit->i[0] - initial->i[0];
   iter_int = span / step->i[0];

   /* An explanation from the GLSL unrolling pass:
    *
    * Make sure that the calculated number of iterations satisfies the exit
    * condition.  This is needed to catch off-by-one errors and some types of
    * ill-formed loops.  For example, we need to detect that the following
    * loop does not have a maximum iteration count.
    *
    *    for (float x = 0.0; x != 0.9; x += 0.2);
    */
   const int bias[] = { -1, 0, 1 };
   bool valid_loop = false;

   for (unsigned i = 0; i < ARRAY_SIZE(bias); i++) {
      if (valid_loop)
         continue;

      switch (cond_op) {
      case nir_op_ieq:
      case nir_op_ige:
      case nir_op_ilt:
      case nir_op_ine: {
         int temp_iterations = iter_int + bias[i];
         int mul = temp_iterations * step->i[0];
         int add = mul + initial->i[0];
         bool cmp = false;

         if (cond_op == nir_op_ieq)
            cmp = (add == limit->i[0]);

         if (cond_op == nir_op_ige)
            cmp = (add >= limit->i[0]);

         if (cond_op == nir_op_ilt)
            cmp = (add < limit->i[0]);

         if (cond_op == nir_op_ine)
            cmp = (add != limit->i[0]);

         if (cmp) {
            iter_int = temp_iterations;

            valid_loop = true;
         }
         break;
      }
      default:
         return -1;
      }
   }

   return (valid_loop) ? iter_int : -1;
}

static void
find_trip_count(loop_info_state *state)
{
   /* We can now run through each of the terminators of the loop and try to
    * infer a possible trip-count. We need to check them all, and set the
    * lowest trip-count as the trip-count of our loop. If one of the
    * terminators has an undecidable trip-count we can not safely assume
    * anything about the duration of the loop.
    */

   state->info->is_trip_count_known = false;
   nir_loop_terminator *limiting_terminator = NULL;
   int min_trip_count = -2;

   list_for_each_entry(nir_loop_terminator, terminator,
                       &state->info->loop_terminator_list, loop_terminator_link) {

      assert(terminator->conditional_instr->type == nir_instr_type_alu);

      nir_alu_instr *alu = nir_instr_as_alu(terminator->conditional_instr);

      loop_variable *basic_ind = NULL;
      loop_variable *limit = NULL;

      nir_op cond_op;

      switch (alu->op) {
      case nir_op_uge:
      case nir_op_ult:
      case nir_op_feq:
      case nir_op_fge:
      case nir_op_flt:
      case nir_op_fne:
      case nir_op_ieq:
      case nir_op_ige:
      case nir_op_ilt:
      case nir_op_ine:
         /* We assume that the limit is the "right" operand */
         basic_ind = get_loop_var(alu->src[0].src.ssa, state);
         limit = get_loop_var(alu->src[1].src.ssa, state);
         cond_op = alu->op;

         if (basic_ind->nir_loop_var->type != basic_induction) {

            /* We had it the wrong way, flip things around */
            basic_ind = get_loop_var(alu->src[1].src.ssa, state);
            limit = get_loop_var(alu->src[0].src.ssa, state);

            switch (cond_op) {
               case nir_op_uge: cond_op = nir_op_ult; break;
               case nir_op_ult: cond_op = nir_op_uge; break;
               case nir_op_fge: cond_op = nir_op_flt; break;
               case nir_op_flt: cond_op = nir_op_fge; break;
               case nir_op_ige: cond_op = nir_op_ilt; break;
               case nir_op_ilt: cond_op = nir_op_ige; break;
               case nir_op_feq: break;
               case nir_op_ieq: break;
               case nir_op_fne: break;
               case nir_op_ine: break;
               default: unreachable("Should not get here");
            }
         }

         /* The comparison has to have a basic induction variable
          * and a constant for us to be able to find trip counts
          */
         if (basic_ind->nir_loop_var->type != basic_induction ||
             !limit->nir_loop_var->is_constant)
            return;

         nir_basic_induction_var *ind =
               get_basic_ind_var_for_loop_var(basic_ind, state);

         if (!ind->def_outside_loop->is_constant ||
             !ind->invariant->is_constant)
            return;

         /* We have determined that we have the following constants:
          * (With the typical int i = 0; i < x; i++; as an example)
          *    - Upper limit.
          *    - Starting value
          *    - Step / iteration size
          * Thats all thats needed to calculate the trip-count
          */

         nir_load_const_instr *initial_instr =
               nir_instr_as_load_const(
                     ind->def_outside_loop->def->parent_instr);

         nir_const_value initial_val = initial_instr->value;

         nir_load_const_instr *step_instr =
               nir_instr_as_load_const(
                     ind->invariant->def->parent_instr);

         nir_const_value step_val = step_instr->value;

         nir_load_const_instr *limit_instr =
               nir_instr_as_load_const(
                     limit->nir_loop_var->def->parent_instr);

         nir_const_value limit_val = limit_instr->value;

         int iterations = calculate_iterations(&initial_val, &step_val,
                                               &limit_val, cond_op,
                                               ind->alu_def, alu);

         /* If this is the first run then overwrite the value */
         if (min_trip_count == -2)
            min_trip_count = iterations;

         /* Where we not able to calculate the iterations? */
         if (iterations == -1)
            return;

         /* If we have found a smaller amount of iterations than previously
          * that means we have identified a more limiting terminator
          */
         if (iterations < min_trip_count) {
            min_trip_count = iterations;
            limiting_terminator = terminator;
         }
         break;

      default:
         return;
      }
   }

   state->info->is_trip_count_known = true;
   state->info->trip_count = min_trip_count;
   state->info->limiting_terminator = limiting_terminator;
}

static void
get_loop_info(loop_info_state *state, nir_function_impl *impl)
{
   /* Initialize all variables to "outside_loop". This also marks defs
    * invariant and constant if they are nir_instr_type_load_const's
    */
   nir_foreach_block(impl, initialize_block, state);

   init_loop_state init_state = {.mark_in_conditional = false,
                                 .mark_nested = false, .state = state };

   /* Add all entries in the outermost part of the loop to the processing list
    * Mark the entries in conditionals or in nested loops accordingly
    */
   foreach_list_typed_safe(nir_cf_node, node, node, &state->loop->body) {
      switch (node->type) {

      case nir_cf_node_block:
         init_state.mark_in_conditional = false;
         init_state.mark_nested = false;
         init_loop_block(nir_cf_node_as_block(node), &init_state);
         break;

      case nir_cf_node_if:
         init_state.mark_in_conditional = true;
         init_state.mark_nested = false;
         nir_foreach_block_in_cf_node(node, init_loop_block, &init_state);
         break;

      case nir_cf_node_loop:
         init_state.mark_in_conditional = false;
         init_state.mark_nested = true;
         nir_foreach_block_in_cf_node(node, init_loop_block, &init_state);
         break;

      case nir_cf_node_function:
         break;
      }
   }

   /* Induction analysis needs invariance information so get that first */
   compute_invariance_information(state);

   /* We may now have filled the process_list with instructions from inside
    * the nested blocks in the loop. Remove all instructions from the list
    * before we start computing induction information.
    */
   list_inithead(&state->process_list);

   /* Add all entries in the outermost part of the loop to the processing list.
    * Don't include defs inn nested loops or in conditionals.
    */
   init_state.mark_in_conditional = false;
   init_state.mark_nested = false;

   foreach_list_typed_safe(nir_cf_node, node, node, &state->loop->body)
      if (node->type == nir_cf_node_block)
         init_loop_block(nir_cf_node_as_block(node), &init_state);

   /* We have invariance information so try to find induction variables */
   if (!compute_induction_information(state))
      return;

   /* Try to find all simple terminators of the loop. If we can't find any,
    * or we find possible terminators that have side effects then bail.
    */
   if (!find_loop_terminators(state))
      return;

   /* Run through each of the terminators and try to compute a trip-count */
   find_trip_count(state);
}

static loop_info_state *
initialize_loop_info_state(nir_loop *loop, void *mem_ctx, nir_function_impl *impl)
{
   loop_info_state *state = rzalloc(mem_ctx, loop_info_state);
   state->loop_vars = rzalloc_array(mem_ctx, loop_variable, impl->ssa_alloc);
   state->loop = loop;
   state->nir_loop_vars = rzalloc_array(NULL, nir_loop_variable,
                                        impl->ssa_alloc);

   LIST_INITHEAD(&state->process_list);

   state->info = rzalloc(loop, nir_loop_info);

   LIST_INITHEAD(&state->info->loop_terminator_list);
   LIST_INITHEAD(&state->info->loop_vars_list);

   state->info->var_to_basic_ind =
         _mesa_hash_table_create(state->info, _mesa_hash_pointer,
                                 _mesa_key_pointer_equal);

   return state;
}

static void
process_loops(nir_cf_node *cf_node)
{
   switch (cf_node->type) {
   case nir_cf_node_block:
      return;
   case nir_cf_node_if: {
      nir_if *if_stmt = nir_cf_node_as_if(cf_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->then_list)
         process_loops(nested_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->else_list)
         process_loops(nested_node);
      return;
   }
   case nir_cf_node_loop: {
      nir_loop *loop = nir_cf_node_as_loop(cf_node);
      foreach_list_typed(nir_cf_node, nested_node, node, &loop->body)
         process_loops(nested_node);
      break;
   }
   default:
      unreachable("unknown cf node type");
   }

   nir_loop *loop = nir_cf_node_as_loop(cf_node);
   nir_function_impl *impl = nir_cf_node_get_function(cf_node);
   void *mem_ctx = ralloc_context(NULL);

   loop_info_state *state = initialize_loop_info_state(loop, mem_ctx, impl);

   get_loop_info(state, impl);

   loop->info = state->info;

   for (int i = 0; i < impl->ssa_alloc; i++) {
      loop_variable *var = &state->loop_vars[i];
      list_add(&var->nir_loop_var->loop_vars_link, &loop->info->loop_vars_list);
   }

   ralloc_free(mem_ctx);
}

void
nir_loop_analyze_impl(nir_function_impl *impl)
{
   nir_index_ssa_defs(impl);
   foreach_list_typed(nir_cf_node, node, node, &impl->body)
      process_loops(node);
}

void
nir_loop_analyze(nir_shader *shader)
{
   nir_foreach_overload(shader, overload) {
      if (overload->impl)
         nir_loop_analyze_impl(overload->impl);
   }
}
