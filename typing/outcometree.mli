(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*     Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt        *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Module [Outcometree]: results displayed by the toplevel *)

(* These types represent messages that the toplevel displays as normal
   results or errors. The real displaying is customisable using the hooks:
      [Toploop.print_out_value]
      [Toploop.print_out_type]
      [Toploop.print_out_sig_item]
      [Toploop.print_out_phrase] *)

type out_ident =
  | Oide_apply of out_ident * out_ident
  | Oide_dot of out_ident * string
  | Oide_ident of string

type out_value =
  | Oval_array of out_value list
  | Oval_char of char
  | Oval_constr of out_ident * out_value list
  | Oval_ellipsis
  | Oval_float of float
  | Oval_int of int
  | Oval_int32 of int32
  | Oval_int64 of int64
  | Oval_nativeint of nativeint
  | Oval_list of out_value list
  | Oval_printer of (Format.formatter -> unit)
  | Oval_record of (out_ident * out_value) list
  | Oval_string of string
  | Oval_stuff of string
  | Oval_tuple of out_value list
  | Oval_variant of string * out_value option

type out_sort =
  | Osrt_type
  | Osrt_effect

type out_type =
  | Otyp_abstract
  | Otyp_open
  | Otyp_alias of out_type * (string * out_sort)
  | Otyp_arrow of string * out_type * out_arrow * out_type
  | Otyp_class of bool * out_ident * out_type list
  | Otyp_constr of out_ident * out_type list
  | Otyp_manifest of out_type * out_type
  | Otyp_object of (string * out_type) list * bool option
  | Otyp_record of (string * out_label_mutability * out_type) list
  | Otyp_stuff of string
  | Otyp_sum of (string * out_type list * out_type option) list
  | Otyp_tuple of out_type list
  | Otyp_var of bool * (string * out_sort)
  | Otyp_variant of
      bool * out_variant * bool * (string list) option
  | Otyp_poly of (string * out_sort) list * out_type
  | Otyp_module of string * string list * out_type list
  | Otyp_effects of out_effect_row

and out_variant =
  | Ovar_fields of (string * bool * out_type list) list
  | Ovar_name of out_ident * out_type list

and out_effect_constructor =
  { oeconstr_label : string;
    oeconstr_polys : (string * out_sort) list;
    oeconstr_args : out_type list;
    oeconstr_res : out_type option;
    oeconstr_default : bool; }

and out_effect_row =
  | Oeff_constr of out_effect_constructor * out_effect_row
  | Oeff_alias of out_effect_row * (string * out_sort)
  | Oeff_row of out_type
  | Oeff_nil

and out_arrow =
  | Oarr_io
  | Oarr_io_tilde
  | Oarr_io_row of out_effect_row
  | Oarr_io_tilde_row of out_effect_constructor list

and out_label_mutability =
  | Olmut_immutable
  | Olmut_mutable

type out_class_type =
  | Octy_constr of out_ident * out_type list
  | Octy_arrow of string * out_type * out_class_type
  | Octy_signature of out_type option * out_class_sig_item list
and out_class_sig_item =
  | Ocsg_constraint of out_type * out_type
  | Ocsg_method of string * bool * bool * out_type
  | Ocsg_value of string * bool * bool * out_type

type out_module_type =
  | Omty_abstract
  | Omty_functor of string * out_module_type option * out_module_type
  | Omty_ident of out_ident
  | Omty_signature of out_sig_item list
  | Omty_alias of out_ident
and out_sig_item =
  | Osig_class of
      bool * string * (string * out_sort * (bool * bool)) list *
        out_class_type * out_rec_status
  | Osig_class_type of
      bool * string * (string * out_sort * (bool * bool)) list *
        out_class_type * out_rec_status
  | Osig_typext of out_extension_constructor * out_ext_status
  | Osig_modtype of string * out_module_type
  | Osig_module of string * out_module_type * out_rec_status
  | Osig_type of out_type_decl * out_type_status
  | Osig_value of string * out_type * string list
and out_type_decl =
  { otype_name: string;
    otype_params: (string * out_sort * (bool * bool)) list;
    otype_type: out_type;
    otype_private: Asttypes.private_flag;
    otype_cstrs: (out_type * out_type) list }
and out_extension_constructor =
  { oext_name: string;
    oext_type_name: string;
    oext_type_params: (string * out_sort) list;
    oext_args: out_type list;
    oext_ret_type: out_type option;
    oext_private: Asttypes.private_flag }
and out_type_extension =
  { otyext_name: string;
    otyext_params: (string * out_sort) list;
    otyext_constructors: (string * out_type list * out_type option) list;
    otyext_private: Asttypes.private_flag }
and out_rec_status =
  | Orec_not
  | Orec_first
  | Orec_next
and out_type_status =
  | Otype_not of out_sort
  | Otype_first of out_sort
  | Otype_next of out_sort option
and out_ext_status =
  | Oext_first
  | Oext_next
  | Oext_exception

type out_phrase =
  | Ophr_eval of out_value * out_type
  | Ophr_signature of (out_sig_item * out_value option) list
  | Ophr_exception of (exn * out_value)
