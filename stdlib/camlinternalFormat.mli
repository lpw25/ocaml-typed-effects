(* No comments, OCaml stdlib internal use only. *)

open CamlinternalFormatBasics

val is_in_char_set : char_set -> char -> bool
val rev_char_set : char_set -> char_set

type mutable_char_set = bytes
val create_char_set : unit -> mutable_char_set
val add_in_char_set : mutable_char_set -> char -> unit
val freeze_char_set : mutable_char_set -> char_set

type ('a, 'b, 'c, 'd, 'e, 'f, !p) param_format_ebb = Param_format_EBB :
     ('x -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
     ('a, 'b, 'c, 'd, 'e, 'f, !p) param_format_ebb

val param_format_of_ignored_format :
  ('a, 'b, 'c, 'd, 'y, 'x, !p) ignored ->
  ('x, 'b, 'c, 'y, 'e, 'f, !p) fmt ->
  ('a, 'b, 'c, 'd, 'e, 'f, !p) param_format_ebb

type ('b, 'c, !p) acc_formatting_gen =
  | Acc_open_tag of ('b, 'c, !p) acc
  | Acc_open_box of ('b, 'c, !p) acc

and ('b, 'c, !p) acc =
  | Acc_formatting_lit of ('b, 'c, !p) acc * formatting_lit
  | Acc_formatting_gen of ('b, 'c, !p) acc * ('b, 'c, !p) acc_formatting_gen
  | Acc_string_literal of ('b, 'c, !p) acc * string
  | Acc_char_literal   of ('b, 'c, !p) acc * char
  | Acc_data_string    of ('b, 'c, !p) acc * string
  | Acc_data_char      of ('b, 'c, !p) acc * char
  | Acc_delay          of ('b, 'c, !p) acc * ('b -[!p]-> 'c)
  | Acc_flush          of ('b, 'c, !p) acc
  | Acc_invalid_arg    of ('b, 'c, !p) acc * string
  | End_of_acc

type ('a, 'b, !p) heter_list =
  | Cons : 'c * ('a, 'b, !p) heter_list -> ('c -[!p]-> 'a, 'b, !p) heter_list
  | Nil : ('b, 'b, !p) heter_list

type ('b, 'c, 'e, 'f, !p) fmt_ebb = Fmt_EBB :
     ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.fmt ->
     ('b, 'c, 'e, 'f, !p) fmt_ebb

type !p wio : effect = ![io | !p]

val make_printf :
  ('b -[io | !p]-> ('b, 'c, !p wio) acc -[io | !p]-> 'd) ->>
    'b ->> ('b, 'c, !p wio) acc ->>
    ('a, 'b, 'c, 'c, 'c, 'd, !p wio) CamlinternalFormatBasics.fmt -[io | !p]-> 'a

val output_acc :
  out_channel ->> (out_channel, unit, !p wio) acc -[io | !p]-> unit
val bufput_acc :
  Buffer.t ->> (Buffer.t, unit, !p wio) acc -[io | !p]-> unit
val strput_acc :
  Buffer.t ->> (unit, string, !p wio) acc -[io | !p]-> unit

val type_format :
  ('g, 'b, 'c, 'j, 'k, 'l, !q) CamlinternalFormatBasics.fmt ->
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.fmtty ->
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.fmt

val fmt_ebb_of_string :
  ?legacy_behavior:bool -> string -> ('b, 'c, 'e, 'f, !p) fmt_ebb
(* warning: the optional flag legacy_behavior is EXPERIMENTAL and will
   be removed in the next version. You must not set it explicitly. It
   is only used by the type-checker implementation.
*)

val format_of_string_fmtty :
  string ->
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.fmtty ->
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.format6e

val format_of_string_format :
  string ->
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.format6e ->
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.format6e

val char_of_iconv : CamlinternalFormatBasics.int_conv -> char
val string_of_formatting_lit : CamlinternalFormatBasics.formatting_lit -> string
val string_of_formatting_gen :
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.formatting_gen
  -> string

val string_of_fmtty :
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.fmtty -> string
val string_of_fmt :
  ('a, 'b, 'c, 'd, 'e, 'f, !p) CamlinternalFormatBasics.fmt -> string

val open_box_of_string : string -> int * block_type

val symm :
   ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
    'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
-> ('a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2,
    'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1) fmtty_rel

val trans :
   ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
    'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
-> ('a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2,
    'a3, 'b3, 'c3, 'd3, 'e3, 'f3, !p3) fmtty_rel
-> ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
    'a3, 'b3, 'c3, 'd3, 'e3, 'f3, !p3) fmtty_rel

val recast :
   ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1) fmt
-> ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
    'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
-> ('a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmt
