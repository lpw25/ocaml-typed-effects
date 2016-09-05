(* No comments, OCaml stdlib internal use only. *)

type padty = Left | Right | Zeros

type int_conv =
  | Int_d | Int_pd | Int_sd | Int_i | Int_pi | Int_si
  | Int_x | Int_Cx | Int_X | Int_CX | Int_o | Int_Co | Int_u

type float_conv =
  | Float_f | Float_pf | Float_sf | Float_e | Float_pe | Float_se
  | Float_E | Float_pE | Float_sE | Float_g | Float_pg | Float_sg
  | Float_G | Float_pG | Float_sG | Float_F

type char_set = string

type counter = Line_counter | Char_counter | Token_counter

type ('a, 'b, !s) padding =
  | No_padding  : ('a, 'a, !s) padding
  | Lit_padding : padty * int -> ('a, 'a, !s) padding
  | Arg_padding : padty -> (int -[!s]-> 'a, 'a, !s) padding

type pad_option = int option

type ('a, 'b, !p) precision =
  | No_precision : ('a, 'a, !p) precision
  | Lit_precision : int -> ('a, 'a, !p) precision
  | Arg_precision : (int -[!p]-> 'a, 'a, !p) precision

type prec_option = int option

type ('a, 'b, 'c, !p) custom_arity =
  | Custom_zero : ('a, string, 'a, !p) custom_arity
  | Custom_succ : ('a, 'b, 'c, !p) custom_arity ->
    ('a, 'x -[!p]-> 'b, 'x -[!p]-> 'c, !p) custom_arity

type block_type = Pp_hbox | Pp_vbox | Pp_hvbox | Pp_hovbox | Pp_box | Pp_fits

type formatting_lit =
  | Close_box
  | Close_tag
  | Break of string * int * int
  | FFlush
  | Force_newline
  | Flush_newline
  | Magic_size of string * int
  | Escaped_at
  | Escaped_percent
  | Scan_indic of char

type ('a, 'b, 'c, 'd, 'e, 'f, !p) formatting_gen =
  | Open_tag : ('a, 'b, 'c, 'd, 'e, 'f, !p) format6e ->
    ('a, 'b, 'c, 'd, 'e, 'f, !p) formatting_gen
  | Open_box : ('a, 'b, 'c, 'd, 'e, 'f, !p) format6e ->
    ('a, 'b, 'c, 'd, 'e, 'f, !p) formatting_gen

and ('a, 'b, 'c, 'd, 'e, 'f, !p) fmtty =
    ('a, 'b, 'c, 'd, 'e, 'f, !p,
     'a, 'b, 'c, 'd, 'e, 'f, !p) fmtty_rel
and ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
   'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel =
| Char_ty :                                                 (* %c  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (char -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     char -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| String_ty :                                               (* %s  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (string -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     string -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Int_ty :                                                  (* %d  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (int -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     int -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Int32_ty :                                                (* %ld *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (int32 -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     int32 -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Nativeint_ty :                                            (* %nd *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (nativeint -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     nativeint -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Int64_ty :                                                (* %Ld *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (int64 -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     int64 -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Float_ty :                                                (* %f  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (float -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     float -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Bool_ty :                                                 (* %B  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (bool -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     bool -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Format_arg_ty :                                           (* %{...%} *)
    ('g, 'h, 'i, 'j, 'k, 'l, !q) fmtty *
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (('g, 'h, 'i, 'j, 'k, 'l, !q) format6e -[!p1]->
       'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     ('g, 'h, 'i, 'j, 'k, 'l, !q) format6e -[!p2]->
       'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Format_subst_ty :                                         (* %(...%) *)
    ('g, 'h, 'i, 'j, 'k, 'l, !q,
     'g1, 'b1, 'c1, 'j1, 'd1, 'a1, !p1) fmtty_rel *
    ('g, 'h, 'i, 'j, 'k, 'l, !q,
     'g2, 'b2, 'c2, 'j2, 'd2, 'a2, !p2) fmtty_rel *
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (('g, 'h, 'i, 'j, 'k, 'l, !q) format6e -[!p1]->
      'g1, 'b1, 'c1, 'j1, 'e1, 'f1, !p1,
     ('g, 'h, 'i, 'j, 'k, 'l, !q) format6e -[!p2]->
      'g2, 'b2, 'c2, 'j2, 'e2, 'f2, !p2) fmtty_rel

(* Printf and Format specific constructors. *)
| Alpha_ty :                                                (* %a  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (('b1 -[!p1]-> 'x -[!p1]-> 'c1) -[!p1]-> 'x -[!p1]->
      'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     ('b2 -[!p2]-> 'x -[!p2]-> 'c2) -[!p2]-> 'x -[!p2]->
      'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Theta_ty :                                                (* %t  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    (('b1 -[!p1]-> 'c1) -[!p1]->
     'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     ('b2 -[!p2]-> 'c2) -[!p2]->
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel
| Any_ty :                                                  (* Used for custom formats *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    ('x -[!p1]-> 'a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'x -[!p2]-> 'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel

(* Scanf specific constructor. *)
| Reader_ty :                                               (* %r  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    ('x -[!p1]-> 'a1, 'b1, 'c1, ('b1 -[!p1]-> 'x) -[!p1]-> 'd1,
      'e1, 'f1, !p1,
     'x -[!p2]-> 'a2, 'b2, 'c2, ('b2 -[!p2]-> 'x) -[!p2]-> 'd2,
      'e2, 'f2, !p2) fmtty_rel
| Ignored_reader_ty :                                       (* %_r  *)
    ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->
    ('a1, 'b1, 'c1, ('b1 -[!p1]-> 'x) -[!p1]-> 'd1, 'e1, 'f1, !p1,
     'a2, 'b2, 'c2, ('b2 -[!p2]-> 'x) -[!p2]-> 'd2, 'e2, 'f2, !p2) fmtty_rel

| End_of_fmtty :
    ('f1, 'b1, 'c1, 'd1, 'd1, 'f1, !p1,
     'f2, 'b2, 'c2, 'd2, 'd2, 'f2, !p2) fmtty_rel

(**)

(** List of format elements. *)
and ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt =
| Char :                                                   (* %c *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (char -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Caml_char :                                              (* %C *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (char -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| String :                                                 (* %s *)
    ('x, string -[!p]-> 'a, !p) padding
    * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Caml_string :                                            (* %S *)
    ('x, string -[!p]-> 'a, !p) padding
    * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Int :                                                    (* %[dixXuo] *)
    int_conv * ('x, 'y, !p) padding * ('y, int -[!p]-> 'a, !p) precision *
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Int32 :                                                  (* %l[dixXuo] *)
    int_conv * ('x, 'y, !p) padding * ('y, int32 -[!p]-> 'a, !p) precision *
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Nativeint :                                              (* %n[dixXuo] *)
    int_conv * ('x, 'y, !p) padding
    * ('y, nativeint -[!p]-> 'a, !p) precision *
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Int64 :                                                  (* %L[dixXuo] *)
    int_conv * ('x, 'y, !p) padding * ('y, int64 -[!p]-> 'a, !p) precision *
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Float :                                                  (* %[feEgGF] *)
    float_conv * ('x, 'y, !p) padding * ('y, float -[!p]-> 'a, !p) precision *
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Bool :                                                   (* %[bB] *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (bool -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Flush :                                                  (* %! *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt

| String_literal :                                         (* abc *)
    string * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Char_literal :                                           (* x *)
    char * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt

| Format_arg :                                             (* %{...%} *)
    pad_option * ('g, 'h, 'i, 'j, 'k, 'l, !q) fmtty *
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (('g, 'h, 'i, 'j, 'k, 'l, !q) format6e -[!p]->
       'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Format_subst :                                           (* %(...%) *)
    pad_option *
    ('g, 'h, 'i, 'j, 'k, 'l, !q,
     'g2, 'b, 'c, 'j2, 'd, 'a, !p) fmtty_rel *
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
    (('g, 'h, 'i, 'j, 'k, 'l, !q) format6e -[!p]->
      'g2, 'b, 'c, 'j2, 'e, 'f, !p) fmt

(* Printf and Format specific constructor. *)
| Alpha :                                                  (* %a *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (('b -[!p]-> 'x -[!p]-> 'c) -[!p]-> 'x -[!p]->
       'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Theta :                                                  (* %t *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (('b -[!p]-> 'c) -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt

(* Format specific constructor: *)
| Formatting_lit :                                         (* @_ *)
    formatting_lit * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Formatting_gen :                                             (* @_ *)
    ('a1, 'b, 'c, 'd1, 'e1, 'f1, !p) formatting_gen *
    ('f1, 'b, 'c, 'e1, 'e2, 'f2, !p) fmt ->
    ('a1, 'b, 'c, 'd1, 'e2, 'f2, !p) fmt

(* Scanf specific constructors: *)
| Reader :                                                 (* %r *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      ('x -[!p]-> 'a, 'b, 'c, ('b -[!p]-> 'x) -[!p]-> 'd, 'e, 'f, !p) fmt
| Scan_char_set :                                          (* %[...] *)
    pad_option * char_set * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (string -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Scan_get_counter :                                       (* %[nlNL] *)
    counter * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
      (int -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
| Scan_next_char :                                         (* %0c *)
    ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
    (char -[!p]-> 'a, 'b, 'c, 'd, 'e, 'f, !p) fmt
  (* %0c behaves as %c for printing, but when scanning it does not
     consume the character from the input stream *)
| Ignored_param :                                          (* %_ *)
    ('a, 'b, 'c, 'd, 'y, 'x, !p) ignored
    * ('x, 'b, 'c, 'y, 'e, 'f, !p) fmt ->
      ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt

(* Custom printing format *)
| Custom :
    ('a, 'x, 'y, !p) custom_arity * (unit -[!p]-> 'x)
    * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->
    ('y, 'b, 'c, 'd, 'e, 'f, !p) fmt

| End_of_format :
      ('f, 'b, 'c, 'e, 'e, 'f, !p) fmt

and ('a, 'b, 'c, 'd, 'e, 'f, !p) ignored =
  | Ignored_char :
      ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_caml_char :
      ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_string :
      pad_option -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_caml_string :
      pad_option -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_int :
      int_conv * pad_option -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_int32 :
      int_conv * pad_option -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_nativeint :
      int_conv * pad_option -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_int64 :
      int_conv * pad_option -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_float :
      pad_option *
        prec_option -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_bool :
      ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_format_arg :
      pad_option * ('g, 'h, 'i, 'j, 'k, 'l, !q) fmtty ->
        ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_format_subst :
      pad_option * ('a, 'b, 'c, 'd, 'e, 'f, !p) fmtty ->
        ('a, 'b, 'c, 'd, 'e, 'f, !p) ignored
  | Ignored_reader :
      ('a, 'b, 'c, ('b -[!p]-> 'x) -[!p]-> 'd, 'd, 'a, !p) ignored
  | Ignored_scan_char_set :
      pad_option * char_set -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_scan_get_counter :
      counter -> ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored
  | Ignored_scan_next_char :
      ('a, 'b, 'c, 'd, 'd, 'a, !p) ignored

and ('a, 'b, 'c, 'd, 'e, 'f, !p) format6e =
  Format of ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt * string


val concat_fmtty :
  ('g1, 'b1, 'c1, 'j1, 'd1, 'a1, !p1,
   'g2, 'b2, 'c2, 'j2, 'd2, 'a2, !p2) fmtty_rel ->>
  ('a1, 'b1, 'c1, 'd1, 'e1, 'f1, !p1,
   'a2, 'b2, 'c2, 'd2, 'e2, 'f2, !p2) fmtty_rel ->>
  ('g1, 'b1, 'c1, 'j1, 'e1, 'f1, !p1,
   'g2, 'b2, 'c2, 'j2, 'e2, 'f2, !p2) fmtty_rel

val erase_rel :
  ('a, 'b, 'c, 'd, 'e, 'f, !p,
   'g, 'h, 'i, 'j, 'k, 'l, !q) fmtty_rel ->>
  ('a, 'b, 'c, 'd, 'e, 'f, !p) fmtty

val concat_fmt :
  ('a, 'b, 'c, 'd, 'e, 'f, !p) fmt ->>
  ('f, 'b, 'c, 'e, 'g, 'h, !p) fmt ->>
  ('a, 'b, 'c, 'd, 'g, 'h, !p) fmt
