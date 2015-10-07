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

CAMLextern value caml_current_stack;
CAMLextern value caml_parent_stack;
CAMLextern value * caml_stack_high;
CAMLextern value * caml_stack_threshold;
CAMLextern value * caml_extern_sp;
CAMLextern intnat caml_trap_sp_off;
CAMLextern intnat caml_trap_barrier_off;
CAMLextern intnat caml_extra_args;
CAMLextern int caml_c_call_args;
CAMLextern code_t caml_saved_pc;

value caml_handle(value body, value hval, value heff, value hexn, intnat extra_args);
value caml_perform(value effect);
value caml_continue(value cont, value ret, intnat extra_args);
value caml_finish(value ret);
value caml_finish_exception(value exn);

void caml_scan_stack(scanning_action, value stack);
void caml_save_stack_gc (int mark_dirty);
void caml_restore_stack_gc();
void caml_clean_stack(value stack);

#define Trap_pc(tp) ((tp)[0])
#define Trap_link(tp) ((tp)[1])

void caml_init_finish_code (void);
void caml_init_stack (uintnat initial_max_size);
void caml_realloc_stack (asize_t required_size, value* save, int nsave);
void caml_change_max_stack_size (uintnat new_max_size);
uintnat caml_stack_usage (void);
int caml_on_current_stack(value*);

CAMLextern uintnat (*caml_stack_usage_hook)(void);
int caml_running_main_fiber();
value caml_fiber_death();

#endif /* CAML_STACKS_H */
