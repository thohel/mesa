/*
 * Copyright © 2010 XXX: FIXUP
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

/*
 * A trick used in LLVM is that for loops that can possibly be completely
 * unrolled, it does an analysis to check if there is a chain of simplications
 * that can occur in such a case, and what the cost will be eventually. This
 * can be usefull as complete unrolling can lead to large simplifications
 * that are a lot less costly than one would expect from complete unrolling,
 * and so one might pessimise the effect of complete unrolling and end up with
 * a loop that is not actually wanted. This is of high importance for us as we
 * are dealing with hardware that is not all that happy about loops, and so the
 * effect of ridding of the loop completely might be very high.
 */

/*
 * We can possibly do a estimatedCompleteUnrollCost, estimatedPartialUnrollCost
 * and DynamicNonUnrolledCost and compare them to find a suitable unroll amount.
 *
 * Or we can use the cost functions from the nested-loops paper to do better at
 * loop unrolling nested loops.
 *
 * We can also set a certain "decreasedCostByCompleteUnrollingFactor" that
 * we use to give complete unrolling of the loop a slight advantage compared
 * to only partial unrolling.
 *
 * Can also do a trick by setting the non-unrolled loop as a cost of 100%
 * and then calculating how many percent is "loop-overhead" (which is saved
 * for each iteration we unroll) and use that to get an idea of the benefit.
 *
 * We can also check if we can find the largest modulo of the trip count that
 * is still within our limits of register pressure and I-cache size, and
 * unroll by that amount, and if it is prime we just bail. This is not the
 * most ideal solution, but it gets the job done. This lets us avoid having
 * a reminder-loop or a Duff's Device to capture the rest of the iterations.
 *
 * We probably want to run the loop unrolling pass only once at the beginning
 * of the optimization cycle and never again.
 *
 * Should figure out how we want to deal with perfectly nested loops.
 *
 *
 *
 *
 * The nested-loop papers considerations:
 * 1: Each unroll factor is between i and Umax where Umax is the largest (or a defined max unrolling)
 * 2: The unroll vector identifies a legal loop transformation
 * 3: The amortized number of register spills is not larger than in the non-unrolled loop
 * 4: The unrolled loop body fits in the instruction-cache
 * 5: The estimated cost of the unroll configuration is minimzed.
 *    The original paper chooses the unroll vector with the smallest
 *    product of unroll factors when there are multiple solutions with
 *    an estimated equal cost. I guess we want to also do this.
 *
 * To enforce Condition 2, we identify noninnermost loops
 * that cannot be permuted to the innermost position in the input loop nest
 * due to dependence constraints or constraints on loop bounds.(17) For each
 * such loop, i, we set umax i =1 to ensure that loop i is not unrolled.
 *
 * Condition 3 ensures that loop unrolling does not cause extra register spills, and Condition 4 ensures
 * that loop unrolling will (most likely) not lead to extra I-cache misses. Our
 * experience is that Condition 3 is usually more tightly binding than Condition 4, i.e.,
 * ensuring no increase in register spills is usually sufficient to ensure that there is no increase in I-cache misses.
 *
 * For simplicity, our solution to modeling Condition 3 is to ensure that the maximum numbers
 * of fixed-point and floating-pointing values in the unrolled loop that may be
 * simultaneously live are bounded by the numbers of available fixed-point
 * and floating-point registers respectively (see Section 2.3).
 *
 * Cost functions from the paper:
 * IR(u1 ,..., uk)=number of distinct Integer Register ( fixed-point) values in unrolled loop body.
 * FR(u1 ,..., uk)=number of distinct Floating-point Register values in unrolled loop body.
 *    IR and FR are computed by using the approach given by Sarkar(15) and Ferrante et al.
 *    of distinct array elements accessed in a loop nest. This approach avoids the expense
 *    of computing input dependences or of using a linear algebra framework to perform the estimation.
 * LS(u1 ,..., uk)=estimated number of cycles spent on Load and Store instructions in unrolled loop body.
 * CP(u1 ,..., uk)=estimated Critical Path length of unrolled loop body (in cycles).
 *    We assume zero cost for load/store instructions when estimating CP, because they
 *    are already accounted for in LS.
 * TCj(u1 ,..., uk)=estimated Total Cycles on class j of functional units required by unrolled loop body.
 *    We assume zero cost for load/store instructions when estimating TCj, because they are already
 *    accounted for in LS. Let NFj be the number of functional units of class j available in the machine.
 *
 *
 *
 * Get optimized unroll vector
 *    Input: Set of k perfectly nested loops with Umax
 *           Objective cost function
 *    Output: Uptimized unroll vector
 *
 *    Algorithm:
 *       1: EnumerateFeasibleVectors with unit vecor as input
 *       2: Initialize Uopt as identity
 *       3: for each vector
 *             if (Cost(new) < Cost(old) or (Cost is equal, but amortized unroll factor is lower)
 *                better unroll vector found.
 *                Set Uopt as current U.
 *             end if
 *          end for
 *       4: Return Uopt
 *
 * EnumerateFeasibleVectors
 *    Input: Index of current loop
 *           Ucur, (with unroll factors set for lops for i+1 -> k)
 *    Output: A set ut feasible unroll vectors
 *
 *    Algorithm:
 *       1: Initialize UV = empty set of unroll vectors
 *       2: for n = 1 to umax do
 *             Umax enforces condition 1 and 2
 *             a) update factor for loop i - Ucur = n
 *             b) If Ucur exceeds capacity constraint
 *                (register pressure or instruction cache)
 *                break for loop
 *             c) if n > 1 and F(Ucur) >= F(Uprev)
 *                (We can not get a better cost)
 *                break for loop
 *             d) if i = 1 (we are the outermost loop
 *                add Ucur to UV set of vectors
 *             e) else
 *                recursive call UV' = EnumerateFeasibleVectors(i-1)
 *                append UV' from recursive call to UV
 *           end for
 *        3: return UV
 *
 *
 *
 *
 *
 *
 *
 * We can possibly add a fallback:
 *    If we fail to find a good unroll vector then unroll the innermost
 *    loop a suitable amount of times.
 *
 *
 *
 *
 */

#include "nir.h"
#include "main/mtypes.h"

#define COMPLETE_UNROLL_BENEFIT_FACTOR 0.8f

typedef struct {
   /* Array of loops */
   nir_loop *loops;

   /* Array of unroll factors */
   int *factors;
} unroll_vector;

typedef struct {
   /* Array of loop infos for the loop nest */
   nir_loop_info *li;

   /* List of unroll vectors */
   struct list_head unroll_vectors;

   nir_shader_compiler_options *options;
} loop_unroll_state;

static bool
is_simple_for_loop(nir_loop_info *li)
{

}

static uint32_t
get_register_cost(nir_loop_info *li)
{

}

static uint32_t
get_cache_cost(nir_loop_info *li)
{

}

static uint32_t
get_load_store_cycles(nir_loop_info *li)
{

}

static uint32_t
get_critical_path_cycles(nir_loop_info *li)
{

}

static uint32_t
get_total_cycles(nir_loop_info *li)
{

}

/*
 * GCC's aproach to finding a constant loop unrolling count is to
 *    It does maxInstructionsInLoop/instructionsinloop to get the max unroll amount
 *    It also has a average case that does the same.
 *    One deals with the absolute max, and the other deals with, well, the average (takes into account diverging control flow)
 *    If the unroll amount it larger than the set maximum unroll amount then it limits it
 *    It skips big loops where we don't get unroll-amount > 1
 *      /* Success; now compute number of iterations to unroll.  We alter
     nunroll so that as few as possible copies of loop body are
     necessary, while still not decreasing the number of unrollings
     too much (at most by 1).
  best_copies = 2 * nunroll + 10;

  i = 2 * nunroll + 2;
  if (i - 1 >= desc->niter)
    i = desc->niter - 2;

  for (; i >= nunroll - 1; i--)
    {
      unsigned exit_mod = desc->niter % (i + 1);

      if (!loop_exit_at_end_p (loop))
   n_copies = exit_mod + i + 1;
      else if (exit_mod != (unsigned) i
          || desc->noloop_assumptions != NULL_RTX)
   n_copies = exit_mod + i + 2;
      else
   n_copies = i + 1;

      if (n_copies < best_copies)
   {
     best_copies = n_copies;
     best_unroll = i;
   }
    }

  loop->lpt_decision.decision = LPT_UNROLL_CONSTANT;
  loop->lpt_decision.times = best_unroll;

 *
 */

/*
 * Should probably have a get_num_instrs_in_loop function
 * to get the number of instructions in the loop. This can be
 * used to get a feeling of the size of the loop we are trying to unroll.
 */

/*
decide_unroll_constant_iterations (loop, flags);
decide_unroll_runtime_iterations (loop, flags);
decide_unroll_stupid (loop, flags);
unroll_loop_constant_iterations (loop);
unroll_loop_runtime_iterations (loop);
unroll_loop_stupid (loop);
*/


/*
 * li = the current loop in this recursive call
 */
static bool
get_feasible_unroll_vectors(loop_unroll_state *state, unroll_vector *current)
{

}
/*

static bool
unroll_loop(nir_loop_info *li, unroll_vector *UV)
{
   /*
   Start from outer and move to inner
      Expand loop body by unroll factor
      Adjust loop header. If larger than limiting execution number then replace
         header with a assignment of the index variable to to the lower bound expression.
         Otherwise adjust to C/U where C is iteration count and U is unroll factor
      Generate a reminder loop, if necessesary. Body of this is a single copy of the original loop.
         C mod U gives us necessary loop iterations of the reminder loop.

   Input: An array of perfectly nested loops
             i, lb, ub, inc are the loop variables
          An unroll vector for the loops
          An array of iterations exectued per loop

   Algorithm:
      1. Initialize nextParent = parent of loop[1]
      2. Detach subtree rooted at loop[1] from nextParent (use as soure for generating additional copies)
      3. Initialize unrolledBody = copy of body of innermost loop, loop[k]
      4. for j = 1 to k do
            a) currentparent = nextparent;
            b) Expand unrolledBody by factur u[j] for index ij
               for u = 1 to u[j] do
                  1. initialize onecopy = copy of unrolledBody and replace all occurences of (ij) in onecopy with (ij + incj*u)
                  2. Append onecopy to end of newUnrolledBody
               end for
               delete old unrolledBody
               initialize unrolledbody = newUnrolledBody
            c) Adjust header of unrolled loop j
               Construct remainder expression er = mod(C,u)
               if (C is cosntant and C == u)
                  loop should be completely unrolled
                  Construct the statement ij = lbj, call it nextparent, and make it the first child of currentparent
               else
                  make a copy of loop[j] statement, call it nextparent, change it to
                  do ij = lb, ubj-erj*incj, u[j]*incj and make it child of currentparent
               end if
            d) generate remained loop sub-nest, if necessary
               if erj != 0 then
                  1. set treeCopy = copy of subtree rooted at loop[j], change the outermost statement in treecopy to
                  do ij = ub - (erj-1)*incj, ubj, incj, and make treeCopy a child of currentparent.
               end if
       5. Make unrolledBody a child of nextParent and delete the original subtree rooted at loop[1]


      *
}
*/

static uint32_t
get_loop_instruction_count(nir_loop *loop)
{

}

static bool
unroll_loop(nir_loop_info *li, loop_unroll_state *state)
{
   if (!li->limiting_terminator)
      return false;

   if (!li->is_trip_count_known)
      return false;

   uint32_t iterations = li->trip_count;

   uint32_t max_instructions = state->options->max_loop_instructions;

   /* If maximum instructions has not been set then set a default value */
   max_instructions = max_instructions != 0 ? max_instructions : 20; // XXX: Arbitrarily chosen value.

//   uint32_t loop_instructions = get_loop_instruction_count(li->loop);
   uint32_t loop_instructions = 10;
   if (loop_instructions * 2 < max_instructions)
      return false;

   uint32_t unrolled_loop_instructions = 0;

   uint32_t unroll_factor = 1;

   /* There are 3 ssa-defs that simply roll the loop, those will not get
    * duplicated when we unroll the loop, and so we can subtract those.
    */
   while (unrolled_loop_instructions < max_instructions) {
      unrolled_loop_instructions = (loop_instructions - 3) * unroll_factor;
      unroll_factor++;
   }

   /* We want to completely unroll the loop, as the cost for that is lower */
   if (unroll_factor >= iterations);
      //unroll_loop(loop, iterations); //XXX: FIXME

   uint32_t total_defs_original = iterations * loop_instructions;
   uint32_t total_unroll_instruction_count = (loop_instructions - 3) * iterations;

   if ((float) total_unroll_instruction_count *
       COMPLETE_UNROLL_BENEFIT_FACTOR < (float) total_defs_original);
      //XXX: FIXME we can completely unroll the loop

   /* We can now probably do a check over the whole loop to find a guess for
    * the cost of execution in cycles. If we have a nir -> backend-cycles mapping
    * that tells us that in average a number of nir-instrs take X cycles we can
    * do some calculations to get an estimate of the cycles needed. We can also have
    * a option that tells us the cycle cost of doing a loop iteration.
    */
}

static bool
nir_opt_loop_unroll_impl(nir_function_impl *impl)
{
   nir_metadata_require(impl, nir_metadata_loop_analysis);

//   impl->loop_infos; // XXX: Should have a way to get the innermost loops.

   return false; // XXX: Return something meaningfull
}

bool
nir_opt_loop_unroll(nir_shader *shader)
{
   bool progress = false;

   nir_shader_compiler_options *options = shader->options;

   nir_foreach_overload(shader, overload) {
      if (overload->impl)
         progress |= nir_opt_loop_unroll_impl(overload->impl);
   }
   return false;
}
