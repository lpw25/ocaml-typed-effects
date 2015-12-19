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

/* To walk the memory roots for garbage collection */

#include "caml/finalise.h"
#include "caml/globroots.h"
#include "caml/memory.h"
#include "caml/major_gc.h"
#include "caml/minor_gc.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "stack.h"
#include "caml/roots.h"
#include <string.h>
#include <stdio.h>

/* Roots registered from C functions */

struct caml__roots_block *caml_local_roots = NULL;

void (*caml_scan_roots_hook) (scanning_action) = NULL;

/* The hashtable of frame descriptors */

frame_descr ** caml_frame_descriptors = NULL;
int caml_frame_descriptors_mask;

/* Linked-list */

typedef struct link {
  void *data;
  struct link *next;
} link;

static link *cons(void *data, link *tl) {
  link *lnk = caml_stat_alloc(sizeof(link));
  lnk->data = data;
  lnk->next = tl;
  return lnk;
}

#define iter_list(list,lnk) \
  for (lnk = list; lnk != NULL; lnk = lnk->next)

/* Linked-list of frametables */

static link *frametables = NULL;

void caml_register_frametable(intnat *table) {
  frametables = cons(table,frametables);

  if (NULL != caml_frame_descriptors) {
    caml_stat_free(caml_frame_descriptors);
    caml_frame_descriptors = NULL;
    /* force caml_init_frame_descriptors to be called */
  }
}

void caml_init_frame_descriptors(void)
{
  intnat num_descr, tblsize, i, j, len;
  intnat * tbl;
  frame_descr * d;
  uintnat nextd;
  uintnat h;
  link *lnk;

  static int inited = 0;

  if (!inited) {
    for (i = 0; caml_frametable[i] != 0; i++)
      caml_register_frametable(caml_frametable[i]);
    inited = 1;
  }

  /* Count the frame descriptors */
  num_descr = 0;
  iter_list(frametables,lnk) {
    num_descr += *((intnat*) lnk->data);
  }

  /* The size of the hashtable is a power of 2 greater or equal to
     2 times the number of descriptors */
  tblsize = 4;
  while (tblsize < 2 * num_descr) tblsize *= 2;

  /* Allocate the hash table */
  caml_frame_descriptors =
    (frame_descr **) caml_stat_alloc(tblsize * sizeof(frame_descr *));
  for (i = 0; i < tblsize; i++) caml_frame_descriptors[i] = NULL;
  caml_frame_descriptors_mask = tblsize - 1;

  /* Fill the hash table */
  iter_list(frametables,lnk) {
    tbl = (intnat*) lnk->data;
    len = *tbl;
    d = (frame_descr *)(tbl + 1);
    for (j = 0; j < len; j++) {
      h = Hash_retaddr(d->retaddr);
      while (caml_frame_descriptors[h] != NULL) {
        h = (h+1) & caml_frame_descriptors_mask;
      }
      caml_frame_descriptors[h] = d;
      nextd =
        ((uintnat)d +
         sizeof(char *) + sizeof(short) + sizeof(short) +
         sizeof(short) * d->num_live + sizeof(frame_descr *) - 1)
        & -sizeof(frame_descr *);
      if (d->frame_size & 1 && 
          d->frame_size != (unsigned short)-1) {
        nextd += 8;
      }
      d = (frame_descr *) nextd;
    }
  }
}

/* Communication with [caml_start_program] and [caml_call_gc]. */

value caml_current_stack = Val_unit;
char *caml_system_sp;
char *caml_system_top_of_stack;
value **caml_gc_regs_slot;

intnat caml_globals_inited = 0;
static intnat caml_globals_scanned = 0;
static link * caml_dyn_globals = NULL;

void caml_register_dyn_global(void *v) {
  caml_dyn_globals = cons((void*) v,caml_dyn_globals);
}

/* Call [caml_oldify_one] on (at least) all the roots that point to the minor
   heap. */
void caml_oldify_local_roots (void)
{
  int i, j;
  value glob;
  value * root;
  struct caml__roots_block *lr;
  link *lnk;

  /* The global roots */
  for (i = caml_globals_scanned;
       i <= caml_globals_inited && caml_globals[i] != 0;
       i++) {
    glob = caml_globals[i];
    for (j = 0; j < Wosize_val(glob); j++){
      Oldify (&Field (glob, j));
    }
  }
  caml_globals_scanned = caml_globals_inited;

  /* Dynamic global roots */
  iter_list(caml_dyn_globals, lnk) {
    glob = (value) lnk->data;
    for (j = 0; j < Wosize_val(glob); j++){
      Oldify (&Field (glob, j));
    }
  }

  /* The stack and local roots */
  Oldify (&caml_current_stack);

  /* Local C roots */
  for (lr = caml_local_roots; lr != NULL; lr = lr->next) {
    for (i = 0; i < lr->ntables; i++){
      for (j = 0; j < lr->nitems; j++){
        root = &(lr->tables[i][j]);
        Oldify (root);
      }
    }
  }
  /* Global C roots */
  caml_scan_global_young_roots(&caml_oldify_one);
  /* Finalised values */
  caml_final_do_young_roots (&caml_oldify_one);
  /* Hook */
  if (caml_scan_roots_hook != NULL) (*caml_scan_roots_hook)(&caml_oldify_one);
}


/* Call [darken] on all roots */

void caml_darken_all_roots (void)
{
  caml_do_roots (caml_darken);
}

void caml_do_roots (scanning_action f)
{
  int i, j;
  value glob;
  link *lnk;

  /* The global roots */
  for (i = 0; caml_globals[i] != 0; i++) {
    glob = caml_globals[i];
    for (j = 0; j < Wosize_val(glob); j++)
      f (Field (glob, j), &Field (glob, j));
  }

  /* Dynamic global roots */
  iter_list(caml_dyn_globals, lnk) {
    glob = (value) lnk->data;
    for (j = 0; j < Wosize_val(glob); j++){
      f (Field (glob, j), &Field (glob, j));
    }
  }

  /* The stack and local roots */
  if (caml_frame_descriptors == NULL) caml_init_frame_descriptors();
  caml_do_local_roots(f, caml_local_roots);
  /* Global C roots */
  caml_scan_global_roots(f);
  /* Finalised values */
  caml_final_do_strong_roots (f);
  /* Hook */
  if (caml_scan_roots_hook != NULL) (*caml_scan_roots_hook)(f);
}

void caml_scan_stack(scanning_action f, value stack);

void caml_do_local_roots(scanning_action f,
                         struct caml__roots_block * local_roots)
{
  struct caml__roots_block *lr;
  int i,j;
  value *root;

  f (caml_current_stack, &caml_current_stack);

  /* Scan stack explicitly to avoid missing out on live registers during
   * `caml_darken_all_roots`. But skip for compaction. */
  if (Is_block(caml_current_stack) && 
      Tag_val(caml_current_stack) == Stack_tag) {
    caml_scan_stack (f, caml_current_stack);
  }

  /* Local C roots */
  for (lr = local_roots; lr != NULL; lr = lr->next) {
    for (i = 0; i < lr->ntables; i++){
      for (j = 0; j < lr->nitems; j++){
        root = &(lr->tables[i][j]);
        f (*root, root);
      }
    }
  }
}
