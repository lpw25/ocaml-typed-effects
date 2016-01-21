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

/* structure of the stacks */

#ifndef CAML_STACKS_H
#define CAML_STACKS_H


#include "misc.h"
#include "mlvalues.h"
#include "memory.h"
#include "roots.h"

/* One word at the base of the stack is used to store the stack pointer */
#define Stack_ctx_words 6
#ifndef NATIVE_CODE
#define Stack_base(stk) (Op_val(stk) + Stack_ctx_words)
#define Stack_high(stk) (Op_val(stk) + Wosize_val(stk))
#endif
#define Stack_sp(stk) (*(long*)(Op_val(stk) + 0))
#define Stack_dirty(stk) (*(Op_val(stk) + 1))
#define Stack_handle_value(stk) (*(Op_val(stk) + 2))
#define Stack_handle_exception(stk) (*(Op_val(stk) + 3))
#define Stack_handle_effect(stk) (*(Op_val(stk) + 4))
#define Stack_parent(stk) (*(Op_val(stk) + 5))

CAMLextern value caml_current_stack;
CAMLextern value * caml_stack_high;
CAMLextern value * caml_stack_threshold;
CAMLextern value * caml_extern_sp;
CAMLextern intnat caml_trap_sp_off;
CAMLextern intnat caml_trap_barrier_off;

value caml_find_performer(value stack);

void caml_scan_stack(scanning_action, value stack);
value* caml_scan_stack_high(scanning_action, value stack, value* stack_high);
void caml_scan_dirty_stack(scanning_action, value stack);
void caml_save_stack_gc (int mark_dirty);
void caml_restore_stack(void);
void caml_restore_stack_gc();
void caml_clean_stack(value stack);

/* The table of global identifiers. */
extern value caml_global_data;

#define Trap_pc(tp) ((tp)[0])
#define Trap_link(tp) ((tp)[1])

void caml_init_finish_code (void);
value caml_switch_stack(value stk);
void caml_init_main_stack (uintnat initial_max_size);
void caml_realloc_stack (asize_t required_size, value* save, int nsave);
void caml_change_max_stack_size (uintnat new_max_size);
uintnat caml_stack_usage (void);
int caml_on_current_stack(value*);

CAMLextern uintnat (*caml_stack_usage_hook)(void);
int caml_running_main_fiber();
value caml_fiber_death();

#endif /* CAML_STACKS_H */
