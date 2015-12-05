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

#include <stdio.h>
#include "caml/mlvalues.h"
#include "caml/roots.h"

void caml_clean_stack (value stack) {
}

void caml_save_stack_gc () {
}

void caml_restore_stack_gc () {
}

void caml_scan_dirty_stack (scanning_action f, value stack) {
}

void caml_scan_stack (scanning_action f, value stack) {
}

value caml_alloc_stack (value hval, value hexn, value heff) {
  caml_fatal_error ("caml_alloc_stack: not implemented\n");
}

void caml_realloc_stack () {
  fprintf (stderr, "caml_realloc_stack\n");
  fflush (stderr);
}
