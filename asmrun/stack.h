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

/* Machine-dependent interface with the asm code */

#ifndef CAML_STACK_H
#define CAML_STACK_H

/* Macros to access the stack frame */

#ifdef TARGET_sparc
#define Saved_return_address(sp) *((intnat *)((sp) + 92))
#define Callback_link(sp) ((struct caml_context *)((sp) + 104)) //FIXME KC
#endif

#ifdef TARGET_i386
#define Saved_return_address(sp) *((intnat *)((sp) - 4))
#ifndef SYS_win32
#define Callback_link(sp) ((struct caml_context *)((sp) + 16)) //FIXME KC
#else
#define Callback_link(sp) ((struct caml_context *)((sp) + 8)) //FIXME KC
#endif
#endif

#ifdef TARGET_power
#define Saved_return_address(sp) *((intnat *)((sp) - SIZEOF_PTR))
#define Already_scanned(sp, retaddr) ((retaddr) & 1)
#define Mark_scanned(sp, retaddr) \
          (*((intnat *)((sp) - SIZEOF_PTR)) = (retaddr) | 1)
#define Mask_already_scanned(retaddr) ((retaddr) & ~1)
#ifdef SYS_aix
#define Trap_frame_size 32
#else
#define Trap_frame_size 16
#endif
#define Callback_link(sp) ((struct caml_context *)((sp) + Trap_frame_size)) //FIXME KC
#endif

#ifdef TARGET_arm
#define Saved_return_address(sp) *((intnat *)((sp) - 4))
#define Callback_link(sp) ((struct caml_context *)((sp) + 8)) //FIXME KC
#endif

#ifdef TARGET_amd64
#define Saved_return_address(sp) *((intnat *)((sp) - 8))
#define Callback_link(sp) ((value *)((sp) + 16))
#endif

#ifdef TARGET_arm64
#define Saved_return_address(sp) *((intnat *)((sp) - 8))
#define Callback_link(sp) ((struct caml_context *)((sp) + 16)) //FIXME KC
#endif

/* Structure of OCaml callback contexts */

struct caml_context {
  uintnat exception_ptr_offset; /* exception pointer offset from top of stack */
  value * gc_regs;              /* pointer to register block */
  uintnat callback_offset;      /* Offset of callback link from OCaml part of stack. */
};

/* Structure of frame descriptors */

typedef struct {
  uintnat retaddr;
  unsigned short frame_size;
  unsigned short num_live;
  unsigned short live_ofs[1];
} frame_descr;

struct caml_loc_info {
  int loc_valid;
  int loc_is_raise;
  char * loc_filename;
  int loc_lnum;
  int loc_startchr;
  int loc_endchr;
};

/* Hash table of frame descriptors */

extern frame_descr ** caml_frame_descriptors;
extern int caml_frame_descriptors_mask;

#define Hash_retaddr(addr) \
  (((uintnat)(addr) >> 3) & caml_frame_descriptors_mask)

extern void caml_init_frame_descriptors(void);
extern void caml_register_frametable(intnat *);
extern void caml_register_dyn_global(void *);

extern void caml_save_stack_gc(int);
extern void caml_restore_stack_gc(void);
extern void caml_switch_stack(value);
CAMLextern void extract_location_info(frame_descr * d,
                                      /*out*/ struct caml_loc_info * li);
extern uintnat caml_stack_usage (void);
extern uintnat (*caml_stack_usage_hook)(void);

/* Declaration of variables used in the asm code */

/* Current OCaml stack */
extern value  caml_current_stack;
/* Current top of stack. [caml_top_of_stack == caml_system_sp] when running C
 * code. */
extern char * caml_top_of_stack;
/* Current stack threshold. Used to check for stack overflow of OCaml code. */
extern char * caml_stack_threshold;
/* Saved system stack pointer */
extern char * caml_system_sp;
/* Saved top of system stack (approx.) */
extern char * caml_system_top_of_stack;
/* Offset of exception pointer from the top of stack */
extern uintnat caml_exception_ptr_offset;
/* The address of the gc_regs slot in the caml_context at the bottom of the
 * OCaml stack. During allocation and GC, the gc_regs structure is built after
 * the context is built. We use this address to update the gc_regs slot in the
 * context after the regs table is built. */
extern value ** caml_gc_regs_slot;

extern value caml_globals[];
extern intnat caml_globals_inited;
extern intnat * caml_frametable[];

#define Stack_ctx_words 6 /* Must be consistent with amd64.S:LOAD_OCAML_STACK */
#ifdef NATIVE_CODE
#define Stack_base(stk) ((char*)(Op_val(stk) + Stack_ctx_words))
#define Stack_high(stk) ((char*)(Op_val(stk) + Wosize_val(stk)))
#endif
#define Stack_sp(stk) (*(long*)(Op_val(stk) + 0))
#define Stack_dirty(stk) (*(Op_val(stk) + 1))
#define Stack_handle_value(stk) (*(Op_val(stk) + 2))
#define Stack_handle_exception(stk) (*(Op_val(stk) + 3))
#define Stack_handle_effect(stk) (*(Op_val(stk) + 4))
#define Stack_parent(stk) (*(Op_val(stk) + 5))

#endif /* CAML_STACK_H */
