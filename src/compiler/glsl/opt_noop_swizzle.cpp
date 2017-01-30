/*
 * Copyright © 2010 Intel Corporation
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
 * \file opt_noop_swizzle.cpp
 *
 * If a swizzle doesn't change the order or count of components, then
 * remove the swizzle so that other optimization passes see the value
 * behind it.
 */

#include "ir.h"
#include "ir_visitor.h"
#include "ir_rvalue_visitor.h"
#include "compiler/glsl_types.h"

namespace {

class ir_noop_swizzle_visitor : public ir_rvalue_visitor {
public:
   ir_noop_swizzle_visitor()
   {
      this->progress = false;
   }

   void handle_rvalue(ir_rvalue **rvalue);
   bool progress;
};

} /* unnamed namespace */

static bool
opt_swizzle_swizzle(ir_swizzle *ir)
{
   int mask2[4];

   ir_swizzle *swiz2 = ir->val->as_swizzle();
   if (!swiz2)
      return visit_continue;

   memset(&mask2, 0, sizeof(mask2));
   if (swiz2->mask.num_components >= 1)
      mask2[0] = swiz2->mask.x;
   if (swiz2->mask.num_components >= 2)
      mask2[1] = swiz2->mask.y;
   if (swiz2->mask.num_components >= 3)
      mask2[2] = swiz2->mask.z;
   if (swiz2->mask.num_components >= 4)
      mask2[3] = swiz2->mask.w;

   if (ir->mask.num_components >= 1)
      ir->mask.x = mask2[ir->mask.x];
   if (ir->mask.num_components >= 2)
      ir->mask.y = mask2[ir->mask.y];
   if (ir->mask.num_components >= 3)
      ir->mask.z = mask2[ir->mask.z];
   if (ir->mask.num_components >= 4)
      ir->mask.w = mask2[ir->mask.w];

   ir->val = swiz2->val;

   return true;
}

void
ir_noop_swizzle_visitor::handle_rvalue(ir_rvalue **rvalue)
{
   if (!*rvalue)
      return;

   ir_swizzle *swiz = (*rvalue)->as_swizzle();

   if (!swiz)
      return;

   /* Check first if we can optimize two a sequence of two swizzles */
   if (opt_swizzle_swizzle(swiz))
      this->progress = true;

   if (swiz->type != swiz->val->type)
      return;

   int elems = swiz->val->type->vector_elements;
   if (swiz->mask.x != 0)
      return;
   if (elems >= 2 && swiz->mask.y != 1)
      return;
   if (elems >= 3 && swiz->mask.z != 2)
      return;
   if (elems >= 4 && swiz->mask.w != 3)
      return;

   this->progress = true;
   *rvalue = swiz->val;
}

bool
do_noop_swizzle(exec_list *instructions)
{
   ir_noop_swizzle_visitor v;
   visit_list_elements(&v, instructions);

   return v.progress;
}
