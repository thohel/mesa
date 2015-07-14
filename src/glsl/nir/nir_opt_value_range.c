/*
 * Copyright © 2015 Thomas Helland
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
#include "nir_ssa_def_worklist.h"
#include "nir_block_worklist.h"
#include "nir_constant_expressions.h"

/* This pass implements an extension of
 * "Constant Propagation with Conditional Branches" by Wegman and Zadeck
 * that also handles value ranges. This is useful as a lot of shaders have
 * min/max expressions that can be eliminated, or conditionals that we can
 * prove to be false or true due to previously applied restrictions on range.
 * Value range propagation is a superset of tracking constant values, so this
 * pass eliminates the need for a separate constant propagation pass. The
 * pass is optimistic, meaning we assume all variables are constant (or have
 * restricted range) and disprove it. A pessimistic algorithm would assume
 * all values where undeterminable, and then propagate expressions we know
 * to be constant through the program. An optimistic algorithm gets better
 * results than a pessimistic, with the downside that it can not be aborted
 * halfway through as the information gathered may be wrong.
 *
 * The lattice types are:
 * undefined: Variable may be constant or range-restricted
 *             (We have not yet gotten to them in the pass)
 * constant: Value is determined to be constant
 * range: Value is determined to be range-restricted
 * overdefined: We cannot guarantee the value is constant or range-restricted
 *
 * The rules are as follows:
 *
 * undefined join undefined = undefined
 * undefined join overdefined = overdefined
 * overdefined join overdefined = overdefined
 * [low, high] join overdefined = overdefined
 * [low, high] join undefined = [low, high]
 * [low1, high1] join [low2, high2] = [min(low1, low2), max(high1, high2)]
 *
 * These rules are general pessimistic rules. There may be situations where
 * we can still determine parts of the range of the variable, even though it
 * has an overdefined input (i.e. max, min, sat, abs). This is also true for
 * boolean operations like AND and OR. These can be determined even if we
 * know only one of the operators.
 *
 * When the pass is done all "undefined" values should be determined as
 * either const, range, or overdefined. (Except for in blocks that are
 * marked as unreachable, as they may have not been processed)
 */

/* XXX: Review feedback from Matt
 * Food for thought: a range isn't really what you want for bools. Maybe we
 * can think about extending this analysis to know about disjount ranges,
 * or maybe even just a flag to say "it's either high or low".
 */

/* XXX:
 * Integers are not dealt with much as of now. We need a mechanism to detect
 * overflow, or else the pass may do very wrong stuff.
 */

#define IS_FLOAT_CONSTANT(const_value, operator, operand, num_components)    \
   ((num_components >= 1) ?                                                  \
      const_value.f[0] operator operand &&                                   \
      ((num_components >= 2) ?                                               \
         const_value.f[1] operator operand &&                                \
         ((num_components >= 3) ?                                            \
            const_value.f[2] operator operand &&                             \
            ((num_components == 4) ?                                         \
               const_value.f[3] operator operand :                           \
               true) :                                                       \
            true) :                                                          \
         true) :                                                             \
      false)

#define IS_INT_CONSTANT(const_value, operator, operand, num_components)      \
   ((num_components >= 1) ?                                                  \
      const_value.i[0] operator operand &&                                   \
      ((num_components >= 2) ?                                               \
         const_value.i[1] operator operand &&                                \
         ((num_components >= 3) ?                                            \
            const_value.i[2] operator operand &&                             \
            ((num_components == 4) ?                                         \
               const_value.i[3] operator operand :                           \
               true) :                                                       \
            true) :                                                          \
         true) :                                                             \
      false)

#define IS_UNSIGNED_CONSTANT(const_value, operator, operand, num_components) \
   ((num_components >= 1) ?                                                  \
      const_value.u[0] operator operand &&                                   \
      ((num_components >= 2) ?                                               \
         const_value.u[1] operator operand &&                                \
         ((num_components >= 3) ?                                            \
            const_value.u[2] operator operand &&                             \
            ((num_components == 4) ?                                         \
               const_value.u[3] operator operand :                           \
               true) :                                                       \
            true) :                                                          \
         true) :                                                             \
      false)

/* The forced_constant enum is used to indicate that we have forced the pass
 * to pick the both branches on an if for analysis. This is needed to prevent
 * looping infinitely when we have an if that has an "undef" value as an if-
 * condition. This also means that we process all blocks in the case of an
 * infinite loop (?)
 */
typedef enum {
   undefined,
   range,
   constant,
   overdefined,
   forced_constant
} lattice_type;

typedef enum {
   low,
   high,
   both
} range_to_set;

typedef struct {
   /* Is this entry float, unsigned or something else? */
   nir_alu_type range_type;

   nir_const_value lo;
   nir_const_value hi;

   /* What type of lattice is this */
   lattice_type type;

   nir_ssa_def *ssa_def;
   bool in_loop;
} lattice_entry;

typedef struct {
   /* Corresponds to SSA Work in the original paper */
   nir_ssa_def_worklist ssa_worklist;

   /* Work list of blocks, corresponding to the papers Flow work list */
   nir_block_worklist block_worklist;

   /* Keep track of which blocks are reachable */
   BITSET_WORD *reachable_blocks;

   /* Keep track of which blocks are in loops */
   BITSET_WORD *blocks_in_loop;

   /* An array of lattice_antries for all the ssa_defs */
   lattice_entry *entries;
} value_range_state;

static lattice_entry *
get_lattice_entry(nir_ssa_def *def, value_range_state *state)
{
   lattice_entry *entry = &state->entries[def->index];

   /* On the first run of this function the def may not have been added to
    * the lattice_entry, so do that here.
    */
   if (!entry->ssa_def)
      entry->ssa_def = def;

   return entry;
}

static bool
entry_has_nan(lattice_entry *entry, nir_alu_type type)
{
   if (type == nir_type_float) {
      for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {

         if (entry->hi.f[i] != entry->hi.f[i])
            return true;

         if (entry->lo.f[i] != entry->lo.f[i])
            return true;
      }
   }
   return false;
}

static bool
entry_has_inf(lattice_entry *entry, nir_alu_type type)
{
   if (type == nir_type_float) {
      for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {

         if (entry->hi.f[i] ==  INFINITY || entry->lo.f[i] == -INFINITY)
            return true;
      }
   }
   return false;
}

static nir_alu_type
get_alu_type_from_users(nir_alu_instr *alu)
{
   nir_alu_type type = nir_type_invalid;

   /* XXX: There are probably more operations than these that we want to
    * check the users of to determine their type.
    */
   switch (alu->op) {
   case nir_op_bcsel:
   case nir_op_fcsel:
   case nir_op_vec2:
   case nir_op_vec3:
   case nir_op_vec4:
      break;
   default:
      return nir_op_infos[alu->op].input_types[0];
   }

   bool first_set = false;
   nir_foreach_use_safe(&alu->dest.dest.ssa, src) {

      if (src->parent_instr->type != nir_instr_type_alu)
         continue;

      nir_alu_instr *src_alu = nir_instr_as_alu(src->parent_instr);

      if (!first_set) {
         first_set = true;
         type = get_alu_type_from_users(src_alu);
      } else {
         nir_alu_type temp = get_alu_type_from_users(src_alu);
         if (type != temp)
            return nir_type_invalid;
      }
   }
   return type;
}

static nir_alu_type
get_alu_type_from_sources(nir_alu_instr *alu)
{
   nir_alu_type type = nir_type_invalid;
   bool first_set = false;

   for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {

      if (alu->src[i].src.parent_instr != nir_instr_type_alu)
         return nir_type_invalid;

      nir_alu_instr *src_alu = nir_instr_as_alu(alu->src[i].src.parent_instr);

      if (!first_set) {
         first_set = true;
         type = nir_op_infos[src_alu->op].output_type;
      } else {
         nir_alu_type temp = nir_op_infos[src_alu->op].output_type;
         if (type != temp)
            return nir_type_invalid;
      }
   }
   return type;
}

/* Returns true if this is a change in status of the entry. This simplifies
 * checking if users of this entry should be added to the worklist.
 */
static bool
set_as_overdefined(lattice_entry *entry, nir_alu_type type)
{
   if (entry->type == overdefined && entry->range_type == type)
      return false;

   entry->type = overdefined;
   entry->range_type = type;

   for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {
      switch (type) {
      case nir_type_float:
         entry->hi.f[i] = INFINITY;
         entry->lo.f[i] = -INFINITY;
         break;

      case nir_type_int:
         entry->hi.i[i] = INT32_MAX;
         entry->lo.i[i] = INT32_MIN;
         break;

      case nir_type_bool:
      case nir_type_unsigned:
         entry->hi.u[i] = UINT32_MAX;
         entry->lo.u[i] = 0;
         break;
      case nir_type_invalid:
         break;
      }
   }

   return true;
}

static inline void
set_range_float(lattice_entry *entry, range_to_set to_set, float_t value)
{
   for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {

      if (to_set == low || to_set == both)
         entry->lo.f[i] = value;

      if (to_set == high || to_set == both)
         entry->hi.f[i] = value;

      if (to_set == both)
         entry->type = constant;
      else
         entry->type = range;
   }
}

static inline void
set_range_int(lattice_entry *entry, range_to_set to_set, int32_t value)
{
   for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {

      if (to_set == low || to_set == both)
         entry->lo.i[i] = value;

      if (to_set == high || to_set == both)
         entry->hi.i[i] = value;

      if (to_set == both)
         entry->type = constant;
      else
         entry->type = range;
   }
}

static inline void
set_range_uint(lattice_entry *entry, range_to_set to_set, uint32_t value)
{
   for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {

      if (to_set == low || to_set == both)
         entry->lo.u[i] = value;

      if (to_set == high || to_set == both)
         entry->hi.u[i] = value;

      if (to_set == both)
         entry->type = constant;
      else
         entry->type = range;
   }
}

static bool
is_type_max(nir_const_value *value, nir_alu_type type,
            unsigned num_components)
{
   for (unsigned i = 0; i < num_components; i++) {
      switch (type) {
      case nir_type_float:
         if (value->f[i] != INFINITY)
            return false;
         break;

      case nir_type_int:
         if (value->i[i] != INT32_MAX)
            return false;
         break;

      case nir_type_bool:
      case nir_type_unsigned:
         if (value->u[i] != UINT32_MAX)
            return false;
         break;

      case nir_type_invalid:
         unreachable("not reached");
      }
   }

   return true;
}

static bool
is_type_min(nir_const_value *value, nir_alu_type type,
            unsigned num_components)
{
   for (unsigned i = 0; i < num_components; i++) {
      switch (type) {
      case nir_type_float:
         if (value->f[i] != -INFINITY)
            return false;
         break;

      case nir_type_int:
         if (value->i[i] != INT32_MIN)
            return false;
         break;

      case nir_type_bool:
      case nir_type_unsigned:
         if (value->u[i] != 0)
            return false;
         break;

      case nir_type_invalid:
         unreachable("not reached");
      }
   }

   return true;
}

static nir_const_value
per_component_max(nir_const_value src0, nir_const_value src1,
                  nir_alu_type type, unsigned num_components)
{
   nir_const_value value;
   for (unsigned i = 0; i < num_components; i++) {
      switch (type) {
      case nir_type_float:
         value.f[i] = MAX2(src0.f[i], src1.f[i]);
         break;
      case nir_type_int:
         value.i[i] = MAX2(src0.i[i], src1.i[i]);
         break;
      case nir_type_bool:
      case nir_type_unsigned:
         value.u[i] = MAX2(src0.u[i], src1.u[i]);
         break;
      case nir_type_invalid:
         unreachable("not reached");
      }
   }

   return value;
}

static nir_const_value
per_component_min(nir_const_value src0, nir_const_value src1,
                  nir_alu_type type, unsigned num_components)
{
   nir_const_value value;
   for (unsigned i = 0; i < num_components; i++) {
      switch (type) {
      case nir_type_float:
         value.f[i] = MIN2(src0.f[i], src1.f[i]);
         break;
      case nir_type_int:
         value.i[i] = MIN2(src0.i[i], src1.i[i]);
         break;
      case nir_type_bool:
      case nir_type_unsigned:
         value.u[i] = MIN2(src0.u[i], src1.u[i]);
         break;
      case nir_type_invalid:
         unreachable("not reached");
      }
   }

   return value;
}

typedef enum {
   LESS,
   LESS_EQUAL,
   GREATER_EQUAL,
   EQUAL,
   GREATER,
   COMPARE_FAIL
} compare_range;

static compare_range
compare_entries(nir_alu_src *a, nir_alu_src *b, nir_alu_type type,
                unsigned num_components, value_range_state *state)
{
   lattice_entry *entry_a = get_lattice_entry(a->src.ssa, state);
   lattice_entry *entry_b = get_lattice_entry(b->src.ssa, state);

   bool foundless = true;
   bool found_low_equal = true;
   bool found_high_equal = true;
   bool foundgreater = true;

   for (unsigned i = 0; i < num_components; i++) {
      switch (type) {
      case nir_type_float:
         if (entry_a->hi.f[a->swizzle[i]] >= entry_b->lo.f[b->swizzle[i]])
            foundless = false;

         if (entry_a->hi.f[a->swizzle[i]] > entry_b->lo.f[b->swizzle[i]])
            found_low_equal = false;

         if (entry_a->lo.f[a->swizzle[i]] <= entry_b->hi.f[b->swizzle[i]])
            foundgreater = false;

         if (entry_a->lo.f[a->swizzle[i]] < entry_b->hi.f[b->swizzle[i]])
            found_high_equal = false;
         break;

      case nir_type_int:
         if (entry_a->hi.i[a->swizzle[i]] >= entry_b->lo.i[b->swizzle[i]])
            foundless = false;

         if (entry_a->hi.i[a->swizzle[i]] > entry_b->lo.i[b->swizzle[i]])
            found_low_equal = false;

         if (entry_a->lo.i[a->swizzle[i]] <= entry_b->hi.i[b->swizzle[i]])
            foundgreater = false;

         if (entry_a->lo.i[a->swizzle[i]] < entry_b->hi.i[b->swizzle[i]])
            found_high_equal = false;
         break;

      case nir_type_unsigned:
      case nir_type_bool:
         if (entry_a->hi.u[a->swizzle[i]] >= entry_b->lo.u[b->swizzle[i]])
            foundless = false;

         if (entry_a->hi.u[a->swizzle[i]] > entry_b->lo.u[b->swizzle[i]])
            found_low_equal = false;

         if (entry_a->lo.u[a->swizzle[i]] <= entry_b->hi.u[b->swizzle[i]])
            foundgreater = false;

         if (entry_a->lo.u[a->swizzle[i]] < entry_b->hi.u[b->swizzle[i]])
            found_high_equal = false;
         break;
      default:
         return COMPARE_FAIL;
      }
   }

   if (foundless)
      return LESS;
   if (found_high_equal && found_low_equal)
      return EQUAL;
   if (found_low_equal)
      return LESS_EQUAL;
   if (found_high_equal)
      return GREATER_EQUAL;
   if (foundgreater)
      return GREATER;

   return COMPARE_FAIL;
}

static bool
is_entry_overdefined(lattice_entry *entry)
{
   if (entry->type == overdefined)
      return true;

   if (entry->type == constant)
      return false;

   if (entry->type == undefined)
      return false;

   if (entry->range_type == nir_type_invalid)
      return true;

   /* This checks high and low to find out if the range is indeeed maximum
    * and mininum of the type, and therefore is overdefined. This can happen
    * in cases like max(a, b) where a = abs(x) and b = neg(abs(y)) and we
    * don't know the range of either x or y.
    */
   if (is_type_max(&entry->hi, entry->range_type,
                   entry->ssa_def->num_components) &&
       is_type_min(&entry->lo, entry->range_type,
                   entry->ssa_def->num_components))
      return true;

   return false;
}

static bool
is_component_false(lattice_entry *entry, unsigned component)
{
   /* This can be simplified to check for 0x00000000 */
   return entry->lo.i[component] == 0x00000000 &&
          entry->hi.i[component] == 0x00000000; //XXX: This is not correct. Floats also have negative zero. Is this also false?
/*
   switch (entry->range_type) {
   case nir_type_int:
      return entry->lo.i[component] == 0 &&
             entry->hi.i[component] == 0;
   case nir_type_unsigned:
   case nir_type_bool:
      return entry->lo.u[component] == 0 &&
             entry->hi.u[component] == 0;
   case nir_type_float:
      return entry->lo.f[component] == 0.0f &&
             entry->hi.f[component] == 0.0f;
   case nir_type_invalid:
      unreachable("not reached");
   }
*/
   return false;
}

static bool
is_entry_false(lattice_entry *entry)
{
   bool is_false = true;

   if (is_entry_overdefined(entry))
         return false;

   for (uint8_t i = 0; i < entry->ssa_def->num_components; i++)
      is_false = is_false && is_component_false(entry, i);

   return is_false;
}

static bool
is_component_true(lattice_entry *entry, unsigned component)
{
   switch (entry->range_type) {
   case nir_type_int:
      return entry->lo.i[component] > 0 ||
             entry->hi.i[component] < 0;
   case nir_type_unsigned:
   case nir_type_bool:
      return entry->lo.u[component] > 0;
   case nir_type_float:
      return entry->lo.f[component] > 0.0f ||
             entry->hi.f[component] < 0.0f;
   case nir_type_invalid:
      return false;
   }

   return false;
}

static bool
is_entry_true(lattice_entry *entry)
{
   bool is_true = true;

   if (is_entry_overdefined(entry))
      return false;

   for (uint8_t i = 0; i < entry->ssa_def->num_components; i++)
      is_true = is_true && is_component_true(entry, i);

   return is_true;
}

static bool
is_entry_constant(lattice_entry *entry, unsigned num_components)
{
   if (entry->type == constant)
      return true;

   if (entry->type == overdefined)
      return false;

   /* If the parent instruction is not an alu then we don't really know
    * anything about whether or not it is constant.
    */
   if (entry->ssa_def->parent_instr != nir_instr_type_alu)
      return false;

   for (uint8_t i = 0; i < num_components; i++) {
      if (entry->lo.u[i] != entry->hi.u[i])
         return false;
   }

   entry->type = constant;
   return true;
}

static void
mark_block_reachable(nir_block *block, value_range_state *state)
{
   BITSET_SET(state->reachable_blocks, block->index);
}

static bool
is_block_reachable(nir_block *block, value_range_state *state)
{
   return BITSET_TEST(state->reachable_blocks, block->index);
}

static bool
special_case_alu(nir_ssa_def *def, value_range_state *state)
{
   lattice_entry *entry = get_lattice_entry(def, state);

   switch(nir_instr_as_alu(def->parent_instr)->op) {
   case nir_op_fsat:
      set_range_float(entry, low, 0.0f);
      set_range_float(entry, high, 1.0f);
      return true;
   case nir_op_fsin:
   case nir_op_fcos:
   case nir_op_fsign:
      set_range_float(entry, low, -1.0f);
      set_range_float(entry, high, 1.0f);
      return true;
   case nir_op_fabs:
   case nir_op_fexp2:
   case nir_op_fpow:
   case nir_op_frsq:
   case nir_op_fsqrt:
      set_range_float(entry, low, 0.0f);
      set_range_float(entry, high, INFINITY);
      return true;
   case nir_op_iabs:
      set_range_int(entry, low, 0);
      set_range_int(entry, high, INT32_MAX);
      return true;
   case nir_op_isign:
      set_range_int(entry, low, -1);
      set_range_int(entry, high, 1);
      return true;
   default:
      return false;
   }
}

static bool
is_trivially_computable(nir_alu_instr *alu, value_range_state *state)
{
   switch (alu->op) {

   /* These just extract values, so are safe to compute */
   case nir_op_fmax:    case nir_op_imax:    case nir_op_umax:
   case nir_op_fmin:    case nir_op_imin:    case nir_op_umin:

   /* We can have the following situation:
    *
    *  vec4 ssa_59 = txl ssa_58 (coord), ssa_0 (lod), sampler0 (sampler)
    *  vec1 ssa_60 = imov ssa_59
    *  vec1 ssa_63 = fmul ssa_59.y, ssa_7
    *
    *  We don't know the type of the txl operation, but we know that imow
    *  is an integer operation, and so we set ssa_59 and ssa_60 to
    *  [i_min, i_max]. That is not correct however, as we find out in ssa_63.
    *  The values are instead floats. So we convert the range of ssa_62 to
    *  float-min and max, as we know it is overdefined, and so it works out.
    *  This is a bit fragile, but should work.
    */
   case nir_op_fmov:    case nir_op_imov:

   /* These just limit the range, or flip it, and so are safe to compute */
   case nir_op_fsign:   case nir_op_isign:   case nir_op_fsat:

   /* These are not safe, as you can have a case where the input is
    * [-inf, inf] which becomes [inf, inf] which is clearly wrong. This
    * is dealt with in a special-casing in the compute-range section.
    */
   case nir_op_fabs:    case nir_op_iabs:
      return true;

   /* We need to check if the source is overdefined, or else we may just
    * do a signswap, and in such case integer false ends up as true.
    */
   case nir_op_fneg:    case nir_op_ineg:
      if (is_entry_overdefined(get_lattice_entry(alu->src[0].src.ssa, state)))
         return false;
      break;

   /* These are safe as long as there are not inf upper or lower ranges */
   case nir_op_fadd:    case nir_op_fmul:   case nir_op_ffma:
   case nir_op_flrp:    case nir_op_fsub:   case nir_op_frcp:
   case nir_op_fexp2: {
      for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {
         lattice_entry *src = get_lattice_entry(alu->src[i].src.ssa, state);

         if (entry_has_inf(src, nir_type_float) || is_entry_overdefined(src))
            return false;
      }
      return true;
   }

   case nir_op_frsq:    case nir_op_flog2:  case nir_op_fsqrt: {
      lattice_entry *src = get_lattice_entry(alu->src[0].src.ssa, state);

      if (entry_has_inf(src, nir_type_float) || is_entry_overdefined(src))
         return false;

      if (IS_FLOAT_CONSTANT(src->hi, <, 0.0f, src->ssa_def->num_components))
         /* XXX: Undefined behavior */

      if (IS_FLOAT_CONSTANT(src->lo, <, 0.0f, src->ssa_def->num_components))
         return false;

      return true;
   }

   case nir_op_fpow: {
      lattice_entry *src0 = get_lattice_entry(alu->src[0].src.ssa, state);
      lattice_entry *src1 = get_lattice_entry(alu->src[1].src.ssa, state);

      if (entry_has_inf(src0, nir_type_float) || is_entry_overdefined(src0) ||
          entry_has_inf(src1, nir_type_float) || is_entry_overdefined(src1))
         return false;

      if (IS_FLOAT_CONSTANT(src0->lo, <, 0.0f, src0->ssa_def->num_components))
         /* XXX: Undefined behavior */

      if (IS_FLOAT_CONSTANT(src0->hi, ==, 0.0f, src0->ssa_def->num_components) &&
          IS_FLOAT_CONSTANT(src1->lo, <=, 0.0f, src1->ssa_def->num_components))
         /* XXX: Undefined behavior */

      return true;
   }

   /* We can also do a similar calculation for iadd. We check if the value of
    * sources is less than IMAX/2 and larger than IMIN/2. Then we know we
    * can not overflow. This is simple, but should do the job as integers
    * are probably seldom used with large values, so if we know something
    * about the range of the integer then it is likely that it is "small".
    */
   case nir_op_iadd: {
      lattice_entry *src0 = get_lattice_entry(alu->src[0].src.ssa, state);
      lattice_entry *src1 = get_lattice_entry(alu->src[1].src.ssa, state);

      if (is_entry_overdefined(src0) || is_entry_overdefined(src1))
         return false;

      int32_t max = INT32_MAX/2;
      int32_t min = INT32_MIN/2;
      if (IS_INT_CONSTANT(src0->hi, <, max, 4) &&
          IS_INT_CONSTANT(src1->hi, <, max, 4) &&
          IS_INT_CONSTANT(src0->lo, >, min, 4) &&
          IS_INT_CONSTANT(src1->lo, <, min, 4))
         return true;

      return false;
   }

   default:
      return false;
   }
   return false;
}

static void
evaluate_alu_instr(nir_alu_instr *alu, value_range_state *state)
{
   lattice_entry *entry = get_lattice_entry(&alu->dest.dest.ssa, state);
   lattice_entry *src[4];
   bool all_constant = true;

   /* Early return if we have undefined sources */
   for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {
      src[i] = get_lattice_entry(alu->src[i].src.ssa, state);
      if (src[i]->type == undefined)
         return;
   }

   for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {

      src[i] = get_lattice_entry(alu->src[i].src.ssa, state);

      /* Check if any of the sources are overdefined. If one of them are then
       * the result of this entry will also be overdefined.
       *
       * We may however have cases where we only select one of the
       * operands(max), or we are limiting the range of the operand.
       * These can still be safely computed, as we wont get undefined results.
       *
       * We want to skip csel, as it is special in the regards that only the
       * two last operands actually define the range. Therefore it does not
       * matter if the first operand is overdefined.
       */
      if (is_entry_overdefined(src[i]) &&
          !is_trivially_computable(alu, state) &&
          !(alu->op == nir_op_bcsel || alu->op == nir_op_fcsel) &&
          !(alu->op == nir_op_vec2 || alu->op == nir_op_vec3 || alu->op == nir_op_vec4)) {

         if (!special_case_alu(entry->ssa_def, state))
            set_as_overdefined(entry, nir_op_infos[alu->op].output_type);

         return;
      }

      unsigned num_components = nir_op_infos[alu->op].input_sizes[i];

      if (num_components == 0)
         num_components = alu->dest.dest.ssa.num_components;

      all_constant = all_constant && is_entry_constant(src[i], num_components);
   }

   /* XXX: We handle swizzles at least partly correct now. However, we do not
    * deal with writemasks yet, and so we are probably doing wrong things here.
    */

   if (all_constant) {
      nir_const_value const_src[4];

      for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {
         for (unsigned j = 0; j < entry->ssa_def->num_components; j++) {
            const_src[i].f[j] = src[i]->lo.f[alu->src[i].swizzle[j]];
         }
      }

      nir_const_value dest =
               nir_eval_const_opcode(alu->op,
                                     alu->dest.dest.ssa.num_components,
                                     const_src);

      entry->type = constant;
      entry->lo = dest;
      entry->hi = dest;
      entry->range_type = nir_op_infos[alu->op].output_type;
      return;
   }

   /* Check if the ssa-def is in a loop */
   if (BITSET_TEST(state->blocks_in_loop,
                   entry->ssa_def->parent_instr->block->index)) {

      /* We have for the first time detected that the ssa-def is in a loop.
       * Initialize to the best of our knowledge
       */
      if (!special_case_alu(entry->ssa_def, state))
         set_as_overdefined(entry, nir_op_infos[alu->op].output_type);

      /* Mark it so that we don't visit it anymore */
      entry->in_loop = true;
      return;
   }

   /* If all inputs are of range or constant type we can calculate the range
    * of the operation instead of hand-rolling this ourselves. We can only
    * do this for a select amount of operations. (Basically those that only
    * select/filter the operands, or that restricts the range). In cases
    * like mul, add, etc we can not compute the range trivially, as we can
    * get situations where we multiply -inf and inf, or we overflow integers.
    *
    * This will allow things like sat to possibly give us constants. It will
    * calculate the constant corresponding to the upper and lower value. If
    * these are found to be the same in the "is-def-constant" function then
    * it will get marked as constant, so there is no need to "special-case"
    * things like sat(a) where a < 0.0
    */
   if (is_trivially_computable(alu, state)) {
      nir_const_value lo_consts[4];
      nir_const_value hi_consts[4];

      for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {

         /* We may have set one of the operands to overdefined without knowing
          * what type it was going to be. Now we know that the operand is used
          * in an operation with a give alu-type, and so we can set the
          * operand as overdef again, but with the right alu-type.
          */
         if (is_entry_overdefined(src[i]) &&
             src[i]->range_type != nir_op_infos[alu->op].input_types[i])
            set_as_overdefined(src[i], nir_op_infos[alu->op].input_types[i]);

         for (unsigned j = 0; j < entry->ssa_def->num_components; j++) {
            lo_consts[i].f[j] = src[i]->lo.f[alu->src[i].swizzle[j]];
            hi_consts[i].f[j] = src[i]->hi.f[alu->src[i].swizzle[j]];
         }
      }

      bool first = true;
      nir_const_value temp_const[4];
      nir_const_value computed_low;
      nir_const_value computed_high;

      /* Possible combinations we can make with high and low for num_inputs */
      unsigned combinations = 1 << nir_op_infos[alu->op].num_inputs;

      for (unsigned i = 0; i < combinations; i++) {

         /* Do a copy of low or high values according to mask */
         for (unsigned j = 0; j < nir_op_infos[alu->op].num_inputs; j++)
            temp_const[j] = i & (1 << j) ? hi_consts[j] : lo_consts[j];

         nir_const_value temp =
               nir_eval_const_opcode(alu->op,
                                     alu->dest.dest.ssa.num_components,
                                     temp_const);

         if (first) {
            /* If this is the first run then set an initial value */
            computed_low = computed_high = temp;
            first = false;
         } else {
            /* Do a per_component min/max to get the worst case scenario */
            computed_low = per_component_min(computed_low, temp,
                                             nir_op_infos[alu->op].output_type,
                                             entry->ssa_def->num_components);
            computed_high = per_component_max(computed_high, temp,
                                              nir_op_infos[alu->op].output_type,
                                              entry->ssa_def->num_components);
         }
      }

      /* If the operation was an abs-operation we will have wrongly computed
       * the lower value for the abs. Take a component-wise min of the lower
       * ranges of both operands. If that is larger than zero then set that
       * as the lower range, if not, set zero as lower range.
       */
      if (alu->op == nir_op_fabs) {
         nir_const_value temp =
               per_component_min(lo_consts[0], lo_consts[1],
                                 nir_type_float,
                                 entry->ssa_def->num_components);

         if (IS_FLOAT_CONSTANT(temp, >, 0.0f,
                               entry->ssa_def->num_components)) {
            computed_low = temp;
         } else {
            computed_low.f[0] = 0.0f;    computed_low.f[1] = 0.0f;
            computed_low.f[2] = 0.0f;    computed_low.f[3] = 0.0f;
         }
      }

      if (alu->op == nir_op_iabs) {
         nir_const_value temp =
               per_component_min(lo_consts[0], lo_consts[1],
                                 nir_type_int,
                                 entry->ssa_def->num_components);

         if (IS_INT_CONSTANT(temp, >, 0,
                             entry->ssa_def->num_components)) {
            computed_low = temp;
         } else {
            computed_low.i[0] = 0;    computed_low.i[1] = 0;
            computed_low.i[2] = 0;    computed_low.i[3] = 0;
         }
      }

      entry->type = range;
      entry->lo = computed_low;
      entry->hi = computed_high;
      entry->range_type = nir_op_infos[alu->op].output_type;
      return;
   }

   switch (alu->op) {
   case nir_op_bcsel:
   case nir_op_fcsel: {
      nir_alu_type type = get_alu_type_from_users(alu);

      /* We need to check here if source 1 and 2 are overdefined (which they
       * may be if the instruction it comes from is unsupported) as we skip
       * the csel case earlier on.
       */
      if (type == nir_type_invalid || is_entry_overdefined(src[1]) ||
          is_entry_overdefined(src[2])) {
         set_as_overdefined(entry, type);
         return;
      }

      nir_const_value temp_const_1;
      nir_const_value temp_const_2;

      for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {
         temp_const_1.f[i] = src[1]->lo.f[alu->src[1].swizzle[i]];
         temp_const_2.f[i] = src[2]->lo.f[alu->src[2].swizzle[i]];
      }

      entry->lo = per_component_min(temp_const_1, temp_const_2, type,
                                    entry->ssa_def->num_components);

      for (unsigned i = 0; i < entry->ssa_def->num_components; i++) {
         temp_const_1.f[i] = src[1]->hi.f[alu->src[1].swizzle[i]];
         temp_const_2.f[i] = src[2]->hi.f[alu->src[2].swizzle[i]];
      }

      entry->hi = per_component_max(temp_const_1, temp_const_2, type,
                                    entry->ssa_def->num_components);

      entry->type = range;
      entry->range_type = type;
      return;
   }

   case nir_op_vec4:
   case nir_op_vec3:
   case nir_op_vec2: {
      nir_alu_type type = get_alu_type_from_users(alu);

      if (type == nir_type_invalid) {
         type = get_alu_type_from_sources(alu);

         if (type == nir_type_invalid) {
            set_as_overdefined(entry, nir_type_invalid);
            // XXX: This fails every single time, for some reason
            return;
         }
      }

      for (unsigned i = 0; i < nir_op_infos[alu->op].num_inputs; i++) {
         entry->lo.f[i] = src[i]->lo.f[alu->src[i].swizzle[0]];
         entry->hi.f[i] = src[i]->hi.f[alu->src[i].swizzle[0]];
      }

      entry->type = range;
      entry->range_type = type;
      return;
   }

   default:
      break;
   }

   set_as_overdefined(entry, nir_op_infos[alu->op].output_type);
   return;
}

static bool
evaluate_entry(lattice_entry *entry, value_range_state *state)
{
   lattice_type old_type = entry->type;
   nir_const_value old_hi;
   nir_const_value old_lo;

   /* If it is already overdefined then that can not change */
   if (entry->type == overdefined)
      return false;

   for (unsigned i = 0; i < 4; i++) {
      old_hi.f[i] = entry->hi.f[i];
      old_lo.f[i] = entry->lo.f[i];
   }

   switch (entry->ssa_def->parent_instr->type) {
   case nir_instr_type_load_const: {
      /* First time we encounter a load_const, mark as constant */
      nir_load_const_instr *instr =
         nir_instr_as_load_const(entry->ssa_def->parent_instr);
      entry->type = constant;
      entry->lo = instr->value;
      entry->hi = instr->value;
      entry->range_type = nir_type_invalid;
      break;
   }

   case nir_instr_type_alu: {
      nir_alu_instr *alu = nir_instr_as_alu(entry->ssa_def->parent_instr);
      evaluate_alu_instr(alu, state);

      /* If we, for some reason have a nan as range in any of the components
       * of the high or low range then we should pessimize, or else we badly
       * break the whole pass by generating loads of false information.
       */
      if (entry_has_nan(entry, entry->range_type)) {
         set_as_overdefined(entry, entry->range_type);
         return true;
      }

      break;
   }

   default:
      return set_as_overdefined(entry, nir_type_invalid);
   }

   /* If we find that the entry has become overdefined without marking it as
    * such that means we have calculated the range to +/- inf. We have then
    * changed the status of the entry, so return true
    */
   if (is_entry_overdefined(entry)) {
      set_as_overdefined(entry, entry->range_type);
      return true;
   }

   /* Now we check if the information for the instruction has changed.
    * If it has then we return true, so that we can evaluate the users.
    */
   if (entry->type != old_type)
      return true;

   for (unsigned i = 0; i < 4; i++) {
      if (old_hi.f[i] != entry->hi.f[i] ||
          old_lo.f[i] != entry->lo.f[i])
      return true;
   }

   return false;
}

/* Coordinates finding the uses of the ssa_def corresponding to the entry
 * and adding them to the ssa_worklist. Should be run on every lattice_entry
 * that we change the information of.
 */
static void
coordinate_uses(lattice_entry *entry, value_range_state *state)
{
   nir_foreach_use_safe(entry->ssa_def, src) {
      nir_instr *user = src->parent_instr;
      nir_ssa_def *def;

      /* No point in checking the use if it is not yet found reachable */
      if (!is_block_reachable(user->block, state))
         continue;

      if (user->type != nir_instr_type_alu)
         continue;

      def = &nir_instr_as_alu(user)->dest.dest.ssa;

      /* If the entry is overdefined we want to push it to head of the list.
       * That will cause the def's that will end up overdefined because of
       * overdefined sources to be "finished" as fast as possible, instead of
       * possibly calculating a range and then finding it would end up as
       * overdefined all along.
       */
      if (is_entry_overdefined(entry)) {
         nir_ssa_def_worklist_push_head(&state->ssa_worklist, def);
      } else {
         nir_ssa_def_worklist_push_tail(&state->ssa_worklist, def);
      }
   }

   nir_foreach_if_use_safe(entry->ssa_def, src) {
      /* We want to add the branch according to the entry being true or
       * false, so that we process only the reachable parts of the shader.
       */
      nir_if *if_statement = src->parent_if;

      nir_cf_node *then_node = nir_if_first_then_node(if_statement);
      nir_cf_node *else_node = nir_if_first_else_node(if_statement);

      nir_block *then_block = nir_cf_node_as_block(then_node);
      nir_block *else_block = nir_cf_node_as_block(else_node);

      if (is_entry_true(entry)) {
         nir_block_worklist_push_tail(&state->block_worklist, then_block);
         continue;
      }

      if (is_entry_false(entry)) {
         nir_block_worklist_push_tail(&state->block_worklist, else_block);
         continue;
      }

      if (entry->type == undefined)
         continue;

      nir_block_worklist_push_tail(&state->block_worklist, then_block);
      nir_block_worklist_push_tail(&state->block_worklist, else_block);
   }
}

static bool
handle_unsupported_def(nir_ssa_def *def, void *void_state)
{
   value_range_state *state = void_state;
   lattice_entry *entry = get_lattice_entry(def, state);
   set_as_overdefined(entry, nir_type_invalid);
   coordinate_uses(entry, state);
   return true;
}

/* On the first run of a block we want to always check all the uses
 * of the instructions that we process.
 */
static void
evaluate_block(nir_block *block, value_range_state *state)
{
   nir_foreach_instr_safe(block, instr) {

      nir_ssa_def *def;

      if (instr->type == nir_instr_type_alu) {
         def = &nir_instr_as_alu(instr)->dest.dest.ssa;
      } else if (instr->type == nir_instr_type_load_const) {
         def = &nir_instr_as_load_const(instr)->def;
      } else {
         nir_foreach_ssa_def(instr, handle_unsupported_def, state);
         continue;
      }

      lattice_entry *entry = get_lattice_entry(def, state);

      evaluate_entry(entry, state);
      coordinate_uses(entry, state);
   }
}

static void
mark_cf_node_loop(nir_cf_node *node, value_range_state *state, bool in_loop)
{
   switch (node->type) {
   case nir_cf_node_block:

      if (in_loop)
         BITSET_SET(state->blocks_in_loop, nir_cf_node_as_block(node)->index);

      return;
   case nir_cf_node_if: {
      nir_if *if_stmt = nir_cf_node_as_if(node);

      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->then_list)
         mark_cf_node_loop(nested_node, state, in_loop);

      foreach_list_typed(nir_cf_node, nested_node, node, &if_stmt->else_list)
         mark_cf_node_loop(nested_node, state, in_loop);

      return;
   }
   case nir_cf_node_loop: {
      nir_loop *loop = nir_cf_node_as_loop(node);

      foreach_list_typed(nir_cf_node, nested_node, node, &loop->body)
         mark_cf_node_loop(nested_node, state, true);

      break;
   }
   default:
      unreachable("unknown cf node type");
   }
}

static bool
resolve_undefs_in(nir_cf_node *node, value_range_state *state)
{
   bool found_undefs = false;

   switch (node->type) {
   case nir_cf_node_block:
      break;
   case nir_cf_node_if: {
      nir_if *if_stmt = nir_cf_node_as_if(node);
      lattice_entry *entry = get_lattice_entry(if_stmt->condition.ssa,
                                               state);

      if (entry->type == undefined) {
         nir_cf_node *then_node = nir_if_first_then_node(if_stmt);
         nir_cf_node *else_node = nir_if_first_else_node(if_stmt);

         nir_block *then_block = nir_cf_node_as_block(then_node);
         nir_block *else_block = nir_cf_node_as_block(else_node);

         nir_block_worklist_push_tail(&state->block_worklist, then_block);
         nir_block_worklist_push_tail(&state->block_worklist, else_block);
         found_undefs = true;
         entry->type = forced_constant;
      }
      break;
   }
   case nir_cf_node_loop: {
      nir_loop *loop = nir_cf_node_as_loop(node);
      foreach_list_typed(nir_cf_node, nested_node, node, &loop->body)
         if (resolve_undefs_in(nested_node, state))
            found_undefs = true;
      break;
   }
   default:
      unreachable("unknown cf node type");
   }
   return found_undefs;
}

static bool
nir_opt_value_range_impl(nir_function_impl *impl)
{
   /* TODO: We want to run a pass to insert "pi-nodes" into the ssa-tree
    * before running the pass. This is essentially just a mov x2 = x1 that
    * we use to "store" the range implied by things like if's.
    *
    * This will also lead to a need of inserting more phi-nodes, as one gets
    * variables that diverge and then converge.
    *
    * x1 = ....; [-unlimited, unlimited]
    * if (x1 < 7)
    *    x2 = x1; [-unlimited, 7]
    *    |
    *    |
    * else
    *    x3 = x1; [7, unlimited]
    *    |
    *    |
    * x4 = phi(x2, x3);
    */

   /* We want to recalculate the ssa-indexes first, to reduce our memory
    * consumption and amount of "empty" value-range-variables
    */
   nir_index_ssa_defs(impl);
   nir_index_blocks(impl);

   /* No use in running the pass if there are one or less ssa-defs */
   if (impl->ssa_alloc <= 1)
      return false;

   bool progress = false;
   void *mem_ctx = ralloc_context(NULL);
   value_range_state state;

   state.entries = rzalloc_array(mem_ctx, lattice_entry,
                                 impl->ssa_alloc);

   nir_block_worklist_init(&state.block_worklist, impl->num_blocks,
                           mem_ctx);

   nir_ssa_def_worklist_init(&state.ssa_worklist, impl->ssa_alloc,
                             mem_ctx);

   state.reachable_blocks = rzalloc_array(mem_ctx, BITSET_WORD,
                                          BITSET_WORDS(impl->num_blocks));

   state.blocks_in_loop = rzalloc_array(mem_ctx, BITSET_WORD,
                                        BITSET_WORDS(impl->num_blocks));

   /* Mark the blocks that are inside a loop so we can avoid them */
   foreach_list_typed(nir_cf_node, node, node, &impl->body) {
      if (node->type == nir_cf_node_loop)
         mark_cf_node_loop(node, &state, true);
      else
         mark_cf_node_loop(node, &state, false);
   }

   nir_block_worklist_push_head(&state.block_worklist, impl->start_block);

   bool analysis_done = false;

   /* Process the work lists until they are empty, and until we have no cases
    * of undefined conditionals for if's */
   while (!analysis_done) {

      /* Process the basic block work list */
      while (state.block_worklist.count > 0) {
         nir_block *block = nir_block_worklist_pop_head(&state.block_worklist);

         /* Since we have our "coordinate_uses" function that also handles
          * phi nodes we can skip the block if it is already set reachable,
          * as the phi's will get automagically added to the ssa-worklist as
          * they are users of the defs.
          */
         if (is_block_reachable(block, &state))
            continue;

         /* Block has been determined to be reachable, mark it */
         mark_block_reachable(block, &state);

         /* Evaluate all phi's and expressions of the block. */
         evaluate_block(block, &state);

         /* If the block has only one successor then add it to the worklist */
         if ((block->successors[0] != NULL) &&
             (block->successors[1] == NULL)) {
            nir_block_worklist_push_tail(&state.block_worklist,
                                         block->successors[0]);
            continue;
         }
      }

      /* Process the SSA worklist.  This does not work exactly like the paper.
       * Instead of adding to the list all def's that have changed, and
       * checking each user in the main loop, we are instead adding to the
       * list all the users of def's that have changed. In practice there is
       * no difference, but it allows us to extract the logic of walking the
       * users and running the pass on them to a separate function.
       */
      while (state.ssa_worklist.count > 0) {
         /* All instructions in the list are here because we got new
          * information about the range of an operand.
          */
         nir_ssa_def *def = nir_ssa_def_worklist_pop_head(&state.ssa_worklist);
         lattice_entry *entry = get_lattice_entry(def, &state);

         /* If the def is in a loop we don't want to do anything.
          * (The instruction is initialized as best we can when we mark it.)
          * When the block it's in is added to the worklist the entry will
          * get processed, and so we will evaluate its users.
          */
         if (entry->in_loop)
            continue;

         /* Evaluate the ssa_def. If it has changed then add users to list */
         if (evaluate_entry(entry, &state))
            coordinate_uses(entry, &state);
      }

      /* If both lists are empty that means we are done. However, we assume
       * branches on undef values can not reach any of their successors.
       * This is not a safe assumption, and can lead to eliminating things
       * we shouldn't. Do a trip over all if's to find unresolved branches.
       * If one is found then add both branches to the block worklist. This
       * will slightly pessimize the analysis results, but it will prevent
       * failure. One could also add only the "then"-branch (this is what
       * LLVM does), but most likely this case is so rare that it shouldn't
       * cause us to much loss.
       *
       * TODO: It might be of interest to also check the what operations
       * use undefined values as sources, and resolve those. Some operations
       * should return undef when there's a undef operand, while others
       * should return i.e. 0 to be conservative.
       */
      if (state.block_worklist.count == 0 &&
          state.ssa_worklist.count == 0) {

         analysis_done = true;

         /* Check if there are if's that have undefined inputs */
         foreach_list_typed(nir_cf_node, node, node, &impl->body)
             if (resolve_undefs_in(node, &state))
                analysis_done = false;
      }
   }

   /* For now we want to leave the unreachable blocks in place, as when the
    * conditional for the if is set constant the dead control flow removal
    * pass will come along and clean up the blocks that can not be reached.
    */

   /* Check for all values that are proved to be constant, and replace them
    * with their constant instruction counterpart. We need to do a "backup"
    * of the current amount of ssa-defs, as when we replace an instruction
    * we will bump the ssa_alloc number, and so we will try to access
    * non-existent lattice-entries.
    */
   unsigned num_defs = impl->ssa_alloc - 1;

   for (unsigned i = 0; i < num_defs; i++) {
      lattice_entry *entry = &(state.entries[i]);

      /* Don't try to deal with entries that have not been processed to the
       * state that we have not even set a ssa-def for them. That is a
       * surefire way to segfault. This might happen if we have found a
       * branch that can be predetermined. The dead block will not have
       * been processed at all.
       */
      if (!entry->ssa_def)
         continue;

      /* If it's a constant thats not a load_const then make a load_const
       * instruction and replace the uses of the old instr with that.
       */
      if (is_entry_constant(entry, entry->ssa_def->num_components) &&
          (entry->ssa_def->parent_instr->type != nir_instr_type_load_const)) {

         nir_load_const_instr *new_instr =
               nir_load_const_instr_create(impl->overload->function->shader,
                                           entry->ssa_def->num_components);

         new_instr->value = entry->hi;

         nir_instr_insert_before(entry->ssa_def->parent_instr,
                                 &new_instr->instr);

         nir_ssa_def_rewrite_uses(entry->ssa_def,
                                  nir_src_for_ssa(&new_instr->def),
                                  impl->overload->function->shader);

         nir_instr_remove(entry->ssa_def->parent_instr);
         ralloc_free(entry->ssa_def->parent_instr);
         continue;
      }

      if (entry->ssa_def->parent_instr->type != nir_instr_type_alu)
         continue;

      nir_alu_instr *alu = nir_instr_as_alu(entry->ssa_def->parent_instr);

      if (nir_op_infos[alu->op].num_inputs == 2 &&
          !(is_entry_overdefined(get_lattice_entry(alu->src[0].src.ssa, &state)) ||
            is_entry_overdefined(get_lattice_entry(alu->src[1].src.ssa, &state)))) {

         compare_range result = COMPARE_FAIL;

         switch (alu->op) {
         case nir_op_fmax:   case nir_op_fmin:
         case nir_op_imax:   case nir_op_imin:
         case nir_op_umax:   case nir_op_umin:

            result = compare_entries(&alu->src[0], &alu->src[1],
                                     nir_op_infos[alu->op].output_type,
                                     entry->ssa_def->num_components, &state);
            break;
         default:
            break;
         }

         if (result == LESS || result == LESS_EQUAL) {
            if (alu->op == nir_op_fmax ||
                alu->op == nir_op_imax ||
                alu->op == nir_op_umax)
               nir_ssa_def_rewrite_uses(entry->ssa_def, alu->src[1].src, mem_ctx);
            else
               nir_ssa_def_rewrite_uses(entry->ssa_def, alu->src[0].src, mem_ctx);

            progress = true;
         }

         if (result == GREATER || result == GREATER_EQUAL) {
            if (alu->op == nir_op_fmax ||
                alu->op == nir_op_imax ||
                alu->op == nir_op_umax)
               nir_ssa_def_rewrite_uses(entry->ssa_def, alu->src[0].src, mem_ctx);
            else
               nir_ssa_def_rewrite_uses(entry->ssa_def, alu->src[1].src, mem_ctx);

            progress = true;
         }
         continue;
      }

      /* This removes a boatload of things like abs(sat)) and abs (max(x, 0)).
       * Both of these should be safe with NaN's. (?) If you remove the abs,
       * and then max instruction generates a NaN, you would end up with a
       * negative instead of positive NaN, but that shouldn't really make
       * any significant difference. (?)
       */
      if (alu->op == nir_op_fabs) {
         lattice_entry *src_entry =
               get_lattice_entry(alu->src[0].src.ssa, &state);
         if (is_entry_overdefined(entry))
            break;

         if (IS_FLOAT_CONSTANT(src_entry->lo, >=, 0.0f,
                               entry->ssa_def->num_components)) {

            nir_ssa_def_rewrite_uses(entry->ssa_def,
                                     alu->src[0].src, mem_ctx);
         }
         continue;
      }

      if (alu->op == nir_op_iabs) {
         lattice_entry *src_entry =
               get_lattice_entry(alu->src[0].src.ssa, &state);
         if (is_entry_overdefined(entry))
            break;

         if (IS_INT_CONSTANT(src_entry->lo, >=, 0,
                             entry->ssa_def->num_components)) {

            nir_ssa_def_rewrite_uses(entry->ssa_def,
                                     alu->src[0].src, mem_ctx);
         }
         continue;
      }

      bool set_true = false;
      bool set_false = false;
      /* Check if the result of a comparison can be determined */
      if (nir_op_infos[alu->op].num_inputs == 2 &&
          !(is_entry_overdefined(get_lattice_entry(alu->src[0].src.ssa, &state)) ||
            is_entry_overdefined(get_lattice_entry(alu->src[1].src.ssa, &state)))) {

         compare_range result = COMPARE_FAIL;

         switch (alu->op) {
         case nir_op_feq:  case nir_op_ieq:  case nir_op_seq:
         case nir_op_fge:  case nir_op_ige:  case nir_op_sge:  case nir_op_uge:
         case nir_op_flt:  case nir_op_ilt:  case nir_op_slt:  case nir_op_ult:
         case nir_op_fne:  case nir_op_ine:  case nir_op_sne:

            result = compare_entries(&alu->src[0], &alu->src[1],
                                     nir_op_infos[alu->op].input_types[0],
                                     entry->ssa_def->num_components, &state);
            break;
         default:
            break;
         }

         if (alu->op == nir_op_feq || alu->op == nir_op_ieq ||
             alu->op == nir_op_seq) {

            if (result == EQUAL)
               set_true = true;

            if (result == LESS || result == GREATER)
               set_false = true;
         }

         if (alu->op == nir_op_fne || alu->op == nir_op_ine ||
             alu->op == nir_op_sne) {

            if (result == EQUAL)
               set_false = true;

            if (result == LESS || result == GREATER)
               set_true = true;
         }

         if (alu->op == nir_op_flt || alu->op == nir_op_ilt ||
             alu->op == nir_op_slt || alu->op == nir_op_ult) {

            if (result == LESS)
               set_true = true;

            if (result == GREATER || result == GREATER_EQUAL ||
                result == EQUAL)
               set_false = true;
         }

         if (alu->op == nir_op_fge || alu->op == nir_op_ige ||
             alu->op == nir_op_sge || alu->op == nir_op_uge) {

            if (result == GREATER || result == GREATER_EQUAL ||
                result == EQUAL)
               set_true = true;

            if (result == LESS)
               set_false = true;
         }
      }

      /* Detect that "overdefined && false" == false */
      if (alu->op == nir_op_fand || alu->op == nir_op_iand) {
         for (int i = 0; i < 2; i++) {
            lattice_entry *e = get_lattice_entry(alu->src[i].src.ssa, &state);

            if (is_entry_false(e))
               set_false = true;
         }
      }

      /* Detect that "overdefined || true" == true */
      if (alu->op == nir_op_for || alu->op == nir_op_ior) {
         for (int i = 0; i < 2; i++) {
            lattice_entry *e = get_lattice_entry(alu->src[i].src.ssa, &state);

            if (is_entry_true(e))
               set_true = true;
         }
      }

      if (set_true || set_false) {
         nir_const_value dest;

         if (set_false)
            /* We can replace entry with "false". 0.0f == 0x00000000 which
             * should be the same as signed integer zero, so this is safe
             */
            dest.f[0] = dest.f[1] = dest.f[2] = dest.f[3] = 0.0f;

         if (set_true)
            /* We can replace entry with 1.0f which is also "true" for int */
            dest.f[0] = dest.f[1] = dest.f[2] = dest.f[3] = 1.0f;

         nir_load_const_instr *new_instr =
            nir_load_const_instr_create(impl->overload->function->shader,
                                        alu->dest.dest.ssa.num_components);

         new_instr->value = dest;

         nir_instr_insert_before(&alu->instr, &new_instr->instr);

         nir_ssa_def_rewrite_uses(&alu->dest.dest.ssa, nir_src_for_ssa(&new_instr->def),
                                  impl);

         nir_instr_remove(&alu->instr);
         ralloc_free(alu);
         progress = true;
         continue;
      }

   }

   ralloc_free(mem_ctx);

   return progress;
}

bool
nir_opt_value_range(nir_shader *shader)
{
   bool progress = false;

   nir_foreach_overload(shader, overload) {
      if (overload->impl && nir_opt_value_range_impl(overload->impl))
         progress = true;
   }

   return progress;
}
