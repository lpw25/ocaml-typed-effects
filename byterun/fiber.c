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

/* To initialize and resize the stacks */

#include <string.h>
#include "caml/config.h"
#include "caml/fail.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/fiber.h"
#include "caml/instruct.h"
#include "caml/alloc.h"
#include "caml/fix_code.h"
#include "caml/startup_aux.h"

CAMLexport value caml_current_stack;
CAMLexport value * caml_stack_high; /* one-past-the-end */
CAMLexport value * caml_stack_threshold; /* low + Stack_threshold */
CAMLexport value * caml_extern_sp;

CAMLexport intnat caml_trap_sp_off = 1;
CAMLexport intnat caml_trap_barrier_off;
CAMLexport intnat caml_extra_args;
CAMLexport int caml_c_call_args;
CAMLexport code_t caml_saved_pc;

value caml_global_data = Val_unit;

uintnat caml_max_stack_size;            /* also used in gc_ctrl.c */

static void dirty_stack (value stack);

static value save_stack_dirty (int mark_dirty)
{
  value old_stack = caml_current_stack;
  Stack_sp(old_stack) = caml_stack_high - caml_extern_sp;
  Assert(caml_stack_threshold == Stack_base(old_stack) + Stack_threshold / sizeof(value));
  Assert(caml_stack_high == Stack_high(old_stack));
  Assert(caml_extern_sp == caml_stack_high - Stack_sp(old_stack));
  if (mark_dirty)
    dirty_stack(old_stack);
  return old_stack;
}

static value save_stack (void)
{
  return save_stack_dirty(1);
}

static void load_stack(value newstack)
{
  Assert(sizeof(newstack) == sizeof(caml_current_stack));
  Assert(Tag_val(newstack) == Stack_tag);
  caml_stack_threshold = Stack_base(newstack) + Stack_threshold / sizeof(value);
  caml_stack_high = Stack_high(newstack);
  caml_extern_sp = caml_stack_high - Stack_sp(newstack);
  caml_current_stack = newstack;
}

CAMLprim value caml_alloc_stack(value hval, value hexn, value heff)
{
  CAMLparam3(hval, hexn, heff);
  CAMLlocal1(stack);
  value* sp;
  value* high;

  stack = caml_alloc(caml_init_fiber_wsz, Stack_tag);
  high = sp = Stack_high(stack);

  // ?
  sp -= 1;
  sp[0] = Val_long(1); /* trapsp ?? */

  Stack_sp(stack) = high - sp;
  Stack_dirty(stack) = Val_long(0);
  Stack_handle_value(stack) = hval;
  Stack_handle_exception(stack) = hexn;
  Stack_handle_effect(stack) = heff;
  Stack_parent(stack) = Val_unit;

  CAMLreturn (stack);
}

value caml_switch_stack(value stk)
{
  value s = save_stack();
  load_stack(stk);
  if (caml_gc_phase == Phase_mark &&
      Color_val(caml_current_stack) != Caml_black) {
    caml_scan_stack(caml_darken, caml_current_stack);
    Hd_val(caml_current_stack) = Blackhd_hd(Hd_val(caml_current_stack));
  }
  return s;
}

void caml_init_main_stack(uintnat initial_max_size)
{
  value stack;

  /* Create a stack for the main program.
     The GC is not initialised yet, so we use caml_alloc_shr
     which cannot trigger it */
  stack = caml_alloc_shr(Stack_size/sizeof(value), Stack_tag);
  Stack_sp(stack) = 0;
  Stack_dirty(stack) = Val_long(0);
  Stack_handle_value(stack) = Val_long(0);
  Stack_handle_exception(stack) = Val_long(0);
  Stack_handle_effect(stack) = Val_long(0);
  Stack_parent(stack) = Val_unit;
  caml_max_stack_size = initial_max_size;
  load_stack(stack);
}

/*
  Find the stack that performed an effect,
  skipping over several stacks that delegated
  the effect if necessary.

  Reverses the parent pointers to point
  performer -> delegator instead of
  delegator -> performer.
*/
value caml_find_performer(value stack)
{
  value parent = caml_current_stack;
  do {
    value delegator = Stack_parent(stack);
    Stack_parent(stack) = parent;
    parent = stack;
    stack = delegator;
  } while (stack != Val_unit);
  return parent;
}


/*
  Stack management.

  Used by the interpreter to allocate stack space.
*/

int caml_on_current_stack(value* p)
{
  return Stack_base(caml_current_stack) <= p && p < caml_stack_high;
}

void caml_realloc_stack(asize_t required_space, value* saved_vals, int nsaved)
{
  CAMLparamN(saved_vals, nsaved);
  CAMLlocal2(old_stack, new_stack);
  asize_t size;
  int stack_used;

  old_stack = save_stack();

  stack_used = Stack_sp(old_stack);
  size = Stack_high(old_stack) - Stack_base(old_stack);
  do {
    if (size >= caml_max_stack_size) caml_raise_stack_overflow();
    size *= 2;
  } while (size < stack_used + required_space);
  caml_gc_log ("Growing stack to %" ARCH_INTNAT_PRINTF_FORMAT "uk bytes\n",
               (uintnat) size * sizeof(value) / 1024);

  new_stack = caml_alloc(Stack_ctx_words + size, Stack_tag);
  memcpy(Stack_high(new_stack) - stack_used,
         Stack_high(old_stack) - stack_used,
         stack_used * sizeof(value));

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

CAMLprim value caml_ensure_stack_capacity(value required_space)
{
  asize_t req = Long_val(required_space);
  if (caml_extern_sp - req < Stack_base(caml_current_stack))
    caml_realloc_stack(req, 0, 0);
  return Val_unit;
}

void caml_change_max_stack_size (uintnat new_max_size)
{
  asize_t size = caml_stack_high - caml_extern_sp
                 + Stack_threshold / sizeof (value);

  if (new_max_size < size) new_max_size = size;
  if (new_max_size != caml_max_stack_size) {
    caml_gc_log ("Changing stack limit to %luk bytes\n",
                 new_max_size * sizeof (value) / 1024);
  }
  caml_max_stack_size = new_max_size;
}

/*
  Root scanning.

  Used by the GC to find roots on the fiber.of running or runnable fibers.
*/

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

void caml_restore_stack()
{
  load_stack(caml_current_stack);
}

static void dirty_stack(value stack)
{
  if(Is_young(stack) || Stack_dirty(stack) == Val_long(1))
    return;

  Stack_dirty(stack) = Val_long(1);
  caml_remember_stack (stack);
}

void caml_clean_stack(value stack)
{
  Assert(Tag_val(stack) == Stack_tag);
  Stack_dirty(stack) = Val_long(0);
}

CAMLprim value caml_clone_cont (value cont)
{
  CAMLparam1(cont);
  CAMLlocal1(new_cont);
  value source, target;
  value* slot;

  if (Field (cont, 0) == Val_unit)
    caml_invalid_argument ("continuation already taken");
  source = Field (cont, 0);

  new_cont = caml_alloc (1, 0);
  slot = &Field(new_cont, 0);

  do {
    Assert (Is_block (source) && Tag_val(source) == Stack_tag);

    target = caml_alloc (Wosize_val(source), Stack_tag);
    memcpy ((void*)target, (void*)source, Wosize_val(source) * sizeof(value));
    caml_modify (slot, target);

    slot = &Stack_parent(target);
    source = Stack_parent(source);
  } while (source != Val_unit);

  CAMLreturn(new_cont);
}

value* caml_scan_stack_high (scanning_action f, value stack,
                             value* stack_high)
{
  value *low, *sp;

  f(Stack_handle_value(stack), &Stack_handle_value(stack));
  f(Stack_handle_exception(stack), &Stack_handle_exception(stack));
  f(Stack_handle_effect(stack), &Stack_handle_effect(stack));
  f(Stack_parent(stack), &Stack_parent(stack));

  low = stack_high - Stack_sp(stack);
  for (sp = low; sp < stack_high; sp++) {
    f(*sp, sp);
  }
  return NULL;
}

void caml_scan_stack (scanning_action f, value stack)
{
  if (stack == Val_unit) return;
  caml_scan_stack_high (f, stack, Stack_high(stack));
}

void caml_scan_dirty_stack(scanning_action f, value stack)
{
  if (Stack_dirty(stack) == Val_long(1)) {
    caml_scan_stack(f, stack);
  }
}

CAMLexport uintnat (*caml_stack_usage_hook)(void) = NULL;

uintnat caml_stack_usage(void)
{
  uintnat sz;
  sz = caml_stack_high - caml_extern_sp;
  if (caml_stack_usage_hook != NULL)
    sz += (*caml_stack_usage_hook)();
  return sz;
}
