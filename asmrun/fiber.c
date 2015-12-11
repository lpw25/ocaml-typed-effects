/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

#include <string.h>
#include "caml/alloc.h"
#include "caml/mlvalues.h"
#include "caml/roots.h"
#include "stack.h"

/* The following variables are cached copies of corresponding values at the
 * bottom of the stack object. */
char * caml_top_of_stack;
char * caml_stack_threshold = NULL;
uintnat caml_last_return_address = 1; /* not in OCaml code initially */

void caml_clean_stack (value stack) {
  Assert(Tag_val(stack) == Stack_tag);
  Stack_dirty(stack) = Val_long(0);
}

static void dirty_stack(value stack)
{
  if(Is_young(stack) || Stack_dirty(stack) == Val_long(1))
    return;

  Stack_dirty(stack) = Val_long(1);
  caml_remember_stack (stack);
}

static value save_stack_dirty (int mark_dirty)
{
  value old_stack = caml_current_stack;
  if (mark_dirty)
    dirty_stack(old_stack);
  return old_stack;
}

static void load_stack(value newstack)
{
  Assert(sizeof(newstack) == sizeof(caml_current_stack));
  Assert(Tag_val(newstack) == Stack_tag);
  caml_top_of_stack = Stack_high(newstack);
  caml_stack_threshold = Stack_base(newstack) + Stack_threshold;
  caml_current_stack = newstack;
}

static int stack_is_saved = 0;
void caml_save_stack_gc(int mark_dirty)
{
  Assert(!stack_is_saved);
  save_stack_dirty (mark_dirty);
  stack_is_saved = 1;
}

void caml_restore_stack_gc()
{
  Assert(stack_is_saved);
  load_stack(caml_current_stack);
  stack_is_saved = 0;
}

#define Fiber_stack_wosize (((Stack_threshold) * 2) / sizeof(value))

value caml_alloc_stack (value hval, value hexn, value heff) {
  CAMLparam3(hval, hexn, heff);
  CAMLlocal1(stack);
  char* sp;
  struct caml_context *ctxt;

  stack = caml_alloc(Fiber_stack_wosize, Stack_tag);
  Stack_dirty(stack) = Val_long(0);
  Stack_handle_value(stack) = hval;
  Stack_handle_exception(stack) = hexn;
  Stack_handle_effect(stack) = heff;
  Stack_parent(stack) = Val_unit;

  /* Setup for initial enter. SWITCH_C_TO_OCAML expects a context at the bottom
   * of stack. So setup a dummy context. */
  sp = Stack_high(stack);
  sp -= sizeof(struct caml_context);
  ctxt = (struct caml_context*)sp;
  ctxt->exception_ptr_offset = 0;
  ctxt->gc_regs = NULL;
  ctxt->callback_offset = 0;
  Stack_sp(stack) = sizeof(struct caml_context);

  CAMLreturn (stack);
}

void caml_realloc_stack () {
  CAMLparam0();
  CAMLlocal2(old_stack, new_stack);
  /* All sizes are in bytes */
  asize_t size;
  uintnat stack_used;

  old_stack = caml_current_stack;
  stack_used = Stack_sp(old_stack);
  size = Stack_high(old_stack) - Stack_base(old_stack);
  size *= 2;
  caml_gc_log (0x08, "Growing stack to %" ARCH_INTNAT_PRINTF_FORMAT "uk bytes\n",
               size / 1024);

  new_stack = caml_alloc(Stack_ctx_words + (size / sizeof(value)), Stack_tag);
  memcpy(Stack_high(new_stack) - stack_used,
         Stack_high(old_stack) - stack_used,
         stack_used);

  Stack_sp(new_stack) = Stack_sp(old_stack);
  Stack_handle_value(new_stack) = Stack_handle_value(old_stack);
  Stack_handle_exception(new_stack) = Stack_handle_exception(old_stack);
  Stack_handle_effect(new_stack) = Stack_handle_effect(old_stack);
  Stack_parent(new_stack) = Stack_parent(old_stack);
  Stack_dirty(new_stack) = Val_long(0);

  if (Stack_dirty(old_stack) == Val_long(1)) {
    dirty_stack(new_stack);
  }

  caml_current_stack = new_stack;

  /* Reset old stack */
  Stack_sp(old_stack) = 0;
  Stack_dirty(old_stack) = Val_long(0);
  Stack_handle_value(old_stack) = Val_long(0);
  Stack_handle_exception(old_stack) = Val_long(0);
  Stack_handle_effect(old_stack) = Val_long(0);
  Stack_parent(old_stack) = Val_unit;

  CAMLreturn0;
}

void caml_init_main_stack (value* gc_regs)
{
  CAMLparamN(gc_regs, 6);
  value stack;
  char* sp;
  struct caml_context *ctxt;

  /* Create a stack for the main program.
     The GC is not initialised yet, so we use caml_alloc_shr
     which cannot trigger it */
  stack = caml_alloc_shr(Stack_size/sizeof(value), Stack_tag);
  Stack_dirty(stack) = Val_long(0);
  Stack_handle_value(stack) = Val_long(0);
  Stack_handle_exception(stack) = Val_long(0);
  Stack_handle_effect(stack) = Val_long(0);
  Stack_parent(stack) = Val_unit;

  /* Setup for initial enter. SWITCH_C_TO_OCAML expects a context at the bottom
   * of stack. So setup a dummy context. */
  sp = Stack_high(stack);
  sp -= sizeof(struct caml_context);
  ctxt = (struct caml_context*)sp;
  ctxt->exception_ptr_offset = 0;
  ctxt->gc_regs = NULL;
  ctxt->callback_offset = 0;
  Stack_sp(stack) = sizeof(struct caml_context);

  caml_current_stack = stack;
  CAMLreturn0;
}

void caml_scan_stack (scanning_action f, value stack)
{
  char * sp;
  uintnat retaddr;
  value * regs;
  frame_descr * d;
  uintnat h;
  int n, ofs;
#ifdef Stack_grows_upwards
  short * p;  /* PR#4339: stack offsets are negative in this case */
#else
  unsigned short * p;
#endif
  value *root;
  struct caml_context* context;

  if (caml_frame_descriptors == NULL) caml_init_frame_descriptors();

next_chunk:
  Assert(Is_block(stack) && Tag_val(stack) == Stack_tag);
  f(Stack_handle_value(stack), &Stack_handle_value(stack));
  f(Stack_handle_exception(stack), &Stack_handle_exception(stack));
  f(Stack_handle_effect(stack), &Stack_handle_effect(stack));
  f(Stack_parent(stack), &Stack_parent(stack));

  sp = Stack_high(stack) - Stack_sp(stack);
  context = (struct caml_context*)sp;
  regs = context->gc_regs;
  sp += sizeof(struct caml_context) + context->callback_offset;
  retaddr = *(uintnat*)sp;
  sp += sizeof(value);

  while(1) {
    /* Find the descriptor corresponding to the return address */
    h = Hash_retaddr(retaddr);
    while(1) {
      d = caml_frame_descriptors[h];
      if (d->retaddr == retaddr) break;
      h = (h+1) & caml_frame_descriptors_mask;
    }
    if (d->frame_size != 0xFFFF) {
      /* Scan the roots in this frame */
      for (p = d->live_ofs, n = d->num_live; n > 0; n--, p++) {
        ofs = *p;
        if (ofs & 1) {
          root = regs + (ofs >> 1);
        } else {
          root = (value *)(sp + ofs);
        }
        f (*root, root);
      }
      /* Move to next frame */
#ifndef Stack_grows_upwards
      sp += (d->frame_size & 0xFFFC);
#else
      sp -= (d->frame_size & 0xFFFC);
#endif
      retaddr = Saved_return_address(sp);
      /* XXX KC: disabled already scanned optimization. */
    } else {
      /* This marks the top of an ML stack chunk. */
      value* stackp = Callback_link(sp);
      stack = *stackp;
      /* Continue with the next stack chunk. */
      f (stack, stackp);
      if (Is_block(stack) && stack == *stackp) {
        /* If the previous chunk has not been scanned, scan it. */
        goto next_chunk;
      }
      return;
    }
  }
}

void caml_scan_dirty_stack (scanning_action f, value stack) {
  if (Stack_dirty(stack) == Val_long(1)) {
    caml_scan_stack(f, stack);
  }
}

uintnat (*caml_stack_usage_hook)(void) = NULL;

uintnat caml_stack_usage (void)
{
  uintnat sz;
  sz = Stack_sp(caml_current_stack);
  if (caml_stack_usage_hook != NULL)
    sz += (*caml_stack_usage_hook)();
  return sz;
}
