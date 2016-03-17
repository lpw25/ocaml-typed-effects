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
#include "caml/startup_aux.h"

/* The following variables are cached copies of corresponding values at the
 * bottom of the stack object. */
char * caml_top_of_stack;
char * caml_stack_threshold = NULL;
uintnat caml_last_return_address = 1; /* not in OCaml code initially */

CAMLprim value caml_clone_cont (value cont)
{
  CAMLparam1(cont);
  CAMLlocal3(new_cont, prev_target, source);
  value target;

  if (Field (cont, 0) == Val_unit)
    caml_invalid_argument ("continuation already taken");

  prev_target = Val_unit;
  source = Field (cont, 0);
  new_cont = caml_alloc (1, 0);

  do {
    Assert (Is_block (source) && Tag_val(source) == Stack_tag);

    target = caml_alloc (Wosize_val(source), Stack_tag);
    memcpy ((void*)target, (void*)source, Wosize_val(source) * sizeof(value));

    if (prev_target == Val_unit) {
      caml_modify (&Field(new_cont, 0), target);
    } else {
      caml_modify (&Stack_parent(prev_target), target);
    }

    prev_target = target;
    source = Stack_parent(source);
  } while (source != Val_unit);

  CAMLreturn(new_cont);
}

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

static void save_stack_dirty (int mark_dirty)
{
  if (mark_dirty)
    dirty_stack(caml_current_stack);
}

static int stack_is_saved = 0;
void caml_save_stack_gc(int mark_dirty)
{
  Assert(!stack_is_saved);
  save_stack_dirty (mark_dirty);
  stack_is_saved = 1;
}

static void load_stack (value stack) {
  caml_stack_threshold = Stack_base(stack) + Stack_threshold;
  caml_top_of_stack = Stack_high(stack);
  caml_current_stack = stack;
}

void caml_restore_stack_gc()
{
  Assert(stack_is_saved);
  Assert(Tag_val(caml_current_stack) == Stack_tag);
  load_stack(caml_current_stack);
  stack_is_saved = 0;
}

void caml_restore_stack ()
{
  if (caml_current_stack != Val_unit) {
    Assert(Tag_val(caml_current_stack) == Stack_tag);
    load_stack(caml_current_stack);
  }
}

value caml_alloc_main_stack (uintnat init_size)
{
  CAMLparam0();
  CAMLlocal1(stack);

  /* Create a stack for the main program.
     The GC is not initialised yet, so we use caml_alloc_shr
     which cannot trigger it */
  stack = caml_alloc_shr(init_size, Stack_tag);
  Stack_dirty(stack) = Val_long(0);
  Stack_handle_value(stack) = Val_long(0);
  Stack_handle_exception(stack) = Val_long(0);
  Stack_handle_effect(stack) = Val_long(0);
  Stack_parent(stack) = Val_unit;
  Stack_sp(stack) = 0;

  CAMLreturn(stack);
}

void caml_init_main_stack (uintnat init_size)
{
  value stack;

  stack = caml_alloc_main_stack (init_size);
  load_stack(stack);
}

void caml_realloc_stack () {
  CAMLparam0();
  CAMLlocal2(old_stack, new_stack);
  /* All sizes are in bytes */
  asize_t size;
  uintnat stack_used;

  old_stack = caml_current_stack;
  stack_used = Stack_sp(old_stack);
  size = Wosize_val(old_stack);
  size *= 2;

  caml_gc_log ("Growing old_stack=0x%lx to %lu words\n", old_stack, size);
  new_stack = caml_alloc(size, Stack_tag);
  caml_gc_log ("New_stack=0x%lx\n", new_stack);

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

  load_stack(new_stack);

  /* Reset old stack */
  Stack_sp(old_stack) = 0;
  Stack_dirty(old_stack) = Val_long(0);
  Stack_handle_value(old_stack) = Val_long(0);
  Stack_handle_exception(old_stack) = Val_long(0);
  Stack_handle_effect(old_stack) = Val_long(0);
  Stack_parent(old_stack) = Val_unit;

  CAMLreturn0;
}

void caml_maybe_expand_stack (value* gc_regs)
{
  CAMLparamN(gc_regs, 5);
  uintnat stack_available;

  Assert(Tag_val(caml_current_stack) == Stack_tag);

  stack_available = Bosize_val(caml_current_stack)
    - (Stack_sp(caml_current_stack) + Stack_ctx_words * sizeof(value));
  if (stack_available < 2 * Stack_threshold)
    caml_realloc_stack ();

  CAMLreturn0;
}

extern void caml_fiber_exn_handler (value) Noreturn;
extern void caml_fiber_val_handler (value) Noreturn;

value caml_alloc_stack (value hval, value hexn, value heff) {
  CAMLparam3(hval, hexn, heff);
  CAMLlocal1(stack);
  char* sp;
  struct caml_context *ctxt;

  stack = caml_alloc(caml_init_fiber_wsz, Stack_tag);
  Stack_dirty(stack) = Val_long(0);
  Stack_handle_value(stack) = hval;
  Stack_handle_exception(stack) = hexn;
  Stack_handle_effect(stack) = heff;
  Stack_parent(stack) = Val_unit;

  sp = Stack_high(stack);
  /* Fiber exception handler that returns to parent */
  sp -= sizeof(value);
  *(value**)sp = (value*)caml_fiber_exn_handler;
  /* No previous exception frame */
  sp -= sizeof(value);
  *(uintnat*)sp = 0;
  /* Value handler that returns to parent */
  sp -= sizeof(value);
  *(value**)sp = (value*)caml_fiber_val_handler;

  /* Build a context */
  sp -= sizeof(struct caml_context);
  ctxt = (struct caml_context*)sp;
  ctxt->exception_ptr_offset = 2 * sizeof(value);
  ctxt->gc_regs = NULL;
  Stack_sp(stack) = 3 * sizeof(value) + sizeof(struct caml_context);

  caml_gc_log ("Allocate stack=0x%lx of %lu words\n",
               stack, caml_init_fiber_wsz);

  CAMLreturn (stack);
}



void caml_scan_stack_high (scanning_action f, value stack, value* stack_high)
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

  f(Stack_handle_value(stack), &Stack_handle_value(stack));
  f(Stack_handle_exception(stack), &Stack_handle_exception(stack));
  f(Stack_handle_effect(stack), &Stack_handle_effect(stack));
  f(Stack_parent(stack), &Stack_parent(stack));

  if (Stack_sp(stack) == 0) return;

  sp = ((char*)stack_high) - Stack_sp(stack);

next_chunk:
  if (sp == (char*)stack_high) return;
  context = (struct caml_context*)sp;
  regs = context->gc_regs;
  sp += sizeof(struct caml_context);

  if (sp == (char*)stack_high) return;
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
#ifndef Stack_grows_upwards
      sp += Next_chunk_offset;
#else
      sp -= Next_chunk_offset;
#endif
      goto next_chunk;
    }
  }
}

void caml_scan_stack (scanning_action f, value stack)
{
  value* stack_high = (value*)Stack_high(stack);
  caml_scan_stack_high (f,stack,stack_high);
}

void caml_scan_dirty_stack (scanning_action f, value stack)
{
  if (Stack_dirty(stack) == Val_long(1)) {
    caml_scan_stack(f, stack);
  }
}

void caml_switch_stack(value target) {
  CAMLparam1(target);

  Assert (Is_block(target) && Tag_val(target) == Stack_tag);

  dirty_stack (caml_current_stack);

  load_stack(target);

  if (caml_gc_phase == Phase_mark &&
      Color_val(caml_current_stack) != Caml_black) {
    caml_scan_stack(caml_darken, caml_current_stack);
    Hd_val(caml_current_stack) = Blackhd_hd(Hd_val(caml_current_stack));
  }
  CAMLreturn0;
}

void caml_update_gc_regs_slot (value* gc_regs)
{
  struct caml_context *ctxt;
  ctxt = (struct caml_context*) (((char*)Stack_high(caml_current_stack))
                                 - Stack_sp(caml_current_stack));
  ctxt->gc_regs = gc_regs;
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

#ifdef DEBUG
uintnat stack_sp(value stk) {
  return Stack_sp(stk);
}

value stack_dirty(value stk) {
  return Stack_dirty(stk);
}

value stack_parent(value stk) {
  return Stack_parent(stk);
}
#endif
