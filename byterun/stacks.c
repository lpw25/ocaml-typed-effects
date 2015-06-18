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
#include "caml/stacks.h"
#include "caml/instruct.h"
#include "caml/alloc.h"
#include "caml/fix_code.h"

/* One word at the base of the stack is used to store the stack pointer */
#define Stack_ctx_words 5
#define Stack_base(stk) (Op_val(stk) + Stack_ctx_words)
#define Stack_high(stk) (Op_val(stk) + Wosize_val(stk))
#define Stack_sp(stk) (*(long*)(Op_val(stk) + 0))
#define Stack_handle_value(stk) (*(Op_val(stk) + 1))
#define Stack_handle_exception(stk) (*(Op_val(stk) + 2))
#define Stack_handle_effect(stk) (*(Op_val(stk) + 3))
#define Stack_dirty(stk) (*(Op_val(stk) + 4))

CAMLexport value caml_current_stack;
CAMLexport value caml_parent_stack = Val_long(0);
CAMLexport value * caml_stack_high; /* one-past-the-end */
CAMLexport value * caml_stack_threshold; /* low + Stack_threshold */
CAMLexport value * caml_extern_sp;

CAMLexport intnat caml_trap_sp_off = 1;
CAMLexport intnat caml_trap_barrier_off;
CAMLexport intnat caml_extra_args;
CAMLexport int caml_c_call_args;
CAMLexport code_t caml_saved_pc;

value caml_global_data = 0;

uintnat caml_max_stack_size;            /* also used in gc_ctrl.c */

static void dirty_stack (value stack);

static value save_stack_dirty (int mark_dirty)
{
  value old_stack = caml_current_stack;
  Stack_sp(old_stack) = caml_extern_sp - caml_stack_high;
  Assert(caml_stack_threshold == Stack_base(old_stack) + Stack_threshold / sizeof(value));
  Assert(caml_stack_high == Stack_high(old_stack));
  Assert(caml_extern_sp == caml_stack_high + Stack_sp(old_stack));
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
  caml_extern_sp = caml_stack_high + Stack_sp(newstack);
  caml_current_stack = newstack;
}

static opcode_t finish_code[] = { FINISH };

void caml_init_finish_code (void)
{
#ifdef THREADED_CODE
  caml_thread_code(finish_code, sizeof(finish_code));
#endif
}

#define Fiber_stack_wosize ((Stack_threshold / sizeof(value)) *2)

value caml_handle(value body, value hval, value hexn, value heff, intnat extra_args)
{
  CAMLparam4(body, hval, hexn, heff);
  CAMLlocal2(new_stack, old_stack);
  value *sp, *high;

  /* Push the trapsp, parent stack and extra args */
  /* FIXME caml_trap_barrier_off? */
  sp = caml_extern_sp;
  sp -= 3;
  sp[0] = Val_long(extra_args);
  sp[1] = caml_parent_stack;
  sp[2] = Val_long(caml_trap_sp_off);
  caml_extern_sp = sp;

  /* create a new stack */
  new_stack = caml_alloc(Fiber_stack_wosize, Stack_tag);
  high = Stack_high(new_stack);
  sp = high;

  sp -= 4;
  sp[0] = Val_long(0); /* () */
  sp[1] = Val_pc(finish_code);  /* pc */
  sp[2] = Val_long(0); /* env */
  sp[3] = Val_long(0); /* extra_args */

  Stack_sp(new_stack) = sp - high;
  Stack_handle_value(new_stack) = hval;
  Stack_handle_exception(new_stack) = hexn;
  Stack_handle_effect(new_stack) = heff;

  /* Switch to the new stack */
  old_stack = save_stack();
  load_stack(new_stack);

  /* Set trapsp and parent stack */
  caml_trap_sp_off = 1;
  caml_parent_stack = old_stack;

  CAMLreturn(body);
}

value caml_perform(value effect)
{
  CAMLparam1(effect);
  CAMLlocal2(old_stack, new_stack);
  value cont;
  value *sp;

  /* push the trapsp */
  sp = caml_extern_sp;
  sp -= 1;
  sp[0] = Val_long(caml_trap_sp_off);
  caml_extern_sp = sp;

  /* Switch to the parent stack */
  old_stack = save_stack();
  new_stack = caml_parent_stack;
  load_stack(new_stack);

  /* Create the continuation */
  cont = caml_alloc_small(2, 0);
  Field(cont, 0) =  old_stack;
  Field(cont, 1) = 0;

  /* Set trapsp and parent stack */
  sp = caml_extern_sp;
  caml_parent_stack = sp[1];
  caml_trap_sp_off = Long_val(sp[2]);

  /* Complete the call frame */
  sp[1] = effect;
  sp[2] = cont;

  CAMLreturn(Stack_handle_effect(old_stack));
}

static value use_continuation(value cont)
{
  int cont_status;

  cont_status = Int_val(Field(cont, 1));
  if(cont_status == -1)
    caml_invalid_argument("continuation already used");

  caml_modify(&Field(cont, 1), Val_int(-1));
  return Field(cont, 0);
}

value caml_continue(value cont, value ret, intnat extra_args)
{
  CAMLparam1(ret);
  CAMLlocal2(old_stack, new_stack);
  value *sp;

  /* Retrieve stack from continuation */
  new_stack = use_continuation(cont);

  /* Push the trapsp, parent stack and extra args */
  sp = caml_extern_sp;
  sp -= 3;
  sp[0] = Val_long(extra_args);
  sp[1] = caml_parent_stack;
  sp[2] = Val_long(caml_trap_sp_off);
  caml_extern_sp = sp;

  /* Switch to the new stack */
  old_stack = save_stack();
  load_stack(new_stack);

  /* Set trapsp and parent stack */
  sp = caml_extern_sp;
  caml_trap_sp_off = Long_val(sp[0]);
  caml_parent_stack = old_stack;
  sp += 1;
  caml_extern_sp = sp;

  CAMLreturn(ret);
}

value caml_finish(value ret)
{
  CAMLparam1(ret);
  CAMLlocal2(old_stack, new_stack);
  value *sp;
  value extra_args_v;

  /* Switch to the parent stack */
  old_stack = save_stack();
  new_stack = caml_parent_stack;
  load_stack(new_stack);

  sp = caml_extern_sp;

  /* Set trapsp and parent stack */
  extra_args_v = sp[0];
  caml_parent_stack = sp[1];
  caml_trap_sp_off = Long_val(sp[2]);
  sp += 1;

  /* Complete the call frame and replace extra_args */
  sp[0] = extra_args_v;
  sp[1] = ret;

  caml_extern_sp = sp;

  CAMLreturn(Stack_handle_value(old_stack));
}

value caml_finish_exception(value exn)
{
  CAMLparam1(exn);
  CAMLlocal2(old_stack, new_stack);
  value *sp;
  value extra_args_v;

  /* Switch to the parent stack */
  old_stack = save_stack();
  new_stack = caml_parent_stack;
  load_stack(new_stack);

  sp = caml_extern_sp;

  /* Set trapsp and parent stack */
  extra_args_v = sp[0];
  caml_parent_stack = sp[1];
  caml_trap_sp_off = Long_val(sp[2]);
  sp += 1;

  /* Complete the call frame and replace extra_args */
  sp[0] = extra_args_v;
  sp[1] = exn;

  caml_extern_sp = sp;

  CAMLreturn(Stack_handle_exception(old_stack));
}

void caml_init_stack (uintnat initial_max_size)
{
  value stack;

  /* Create a stack for the main program. The GC is not initialised yet, so we
   * use caml_alloc_shr which cannot trigger it. */
  stack = caml_alloc_shr(Stack_size/sizeof(value), Stack_tag);
  Stack_sp(stack) = 0;
  Stack_handle_value(stack) = Val_long(0);
  Stack_handle_exception(stack) = Val_long(0);
  Stack_handle_effect(stack) = Val_long(0);
  Stack_dirty(stack) = Val_long(0);
  caml_max_stack_size = initial_max_size;
  load_stack(stack);
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

  stack_used = -Stack_sp(old_stack);
  size = Stack_high(old_stack) - Stack_base(old_stack);
  do {
    if (size >= caml_max_stack_size) caml_raise_stack_overflow();
    size *= 2;
  } while (size < stack_used + required_space);
  caml_gc_message (0x08, "Growing stack to %"
                         ARCH_INTNAT_PRINTF_FORMAT "uk bytes",
                   (uintnat) size * sizeof(value) / 1024);

  new_stack = caml_alloc(Stack_ctx_words + size, Stack_tag);

  memcpy(Stack_high(new_stack) - stack_used,
         Stack_high(old_stack) - stack_used,
         stack_used * sizeof(value));

  Stack_sp(new_stack) = Stack_sp(old_stack);
  Stack_handle_value(new_stack) = Stack_handle_value(old_stack);
  Stack_handle_exception(new_stack) = Stack_handle_exception(old_stack);
  Stack_handle_effect(new_stack) = Stack_handle_effect(old_stack);

  dirty_stack(new_stack);
  load_stack(new_stack);
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
  if (new_max_size != caml_max_stack_size){
    caml_gc_message (0x08, "Changing stack limit to %luk bytes\n",
                     new_max_size * sizeof (value) / 1024);
  }
  caml_max_stack_size = new_max_size;
}

/*
  Root scanning.

  Used by the GC to find roots on the stacks of running or runnable fibers.
*/

static int stack_is_saved = 0;

void caml_save_stack_gc (int mark_dirty)
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

static void dirty_stack(value stack)
{
  if(Is_young(stack) || Stack_dirty(stack) == Val_long(1))
    return;

  Stack_dirty(stack) = Val_long(1);
  caml_remember_stack (stack);
}

void caml_clean_stack(value stack)
{
  Assert(Stack_dirty(stack) == Val_long(1));
  Stack_dirty(stack) = Val_long(0);
}

void caml_scan_stack(scanning_action f, value stack)
{
  value *low, *high, *sp;

  if(!Is_block(stack))
    return;

  Assert(Tag_val(stack) == Stack_tag);

  f(Stack_handle_value(stack), &Stack_handle_value(stack));
  f(Stack_handle_exception(stack), &Stack_handle_exception(stack));
  f(Stack_handle_effect(stack), &Stack_handle_effect(stack));

  high = Stack_high(stack);
  low = high + Stack_sp(stack);
  for (sp = low; sp < high; sp++) {
    f(*sp, sp);
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
