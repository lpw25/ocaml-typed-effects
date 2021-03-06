(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Character operations *)

external code: char -> int = "%identity"
external unsafe_chr: int -> char = "%identity"

let chr n =
  let open Int_compare in
  if n < 0 || n > 255 then invalid_arg "Char.chr" else unsafe_chr n

external string_create: int -> string = "caml_create_string"
external string_unsafe_get : string -> int -> char = "%string_unsafe_get"
external string_unsafe_set : string -> int -> char -> unit
                           = "%string_unsafe_set"

let escaped = function
  | '\'' -> "\\'"
  | '\\' -> "\\\\"
  | '\n' -> "\\n"
  | '\t' -> "\\t"
  | '\r' -> "\\r"
  | '\b' -> "\\b"
  | ' ' .. '~' as c ->
      let s = string_create 1 in
      string_unsafe_set s 0 c;
      s
  | c ->
      let n = code c in
      let s = string_create 4 in
      string_unsafe_set s 0 '\\';
      string_unsafe_set s 1 (unsafe_chr (48 + n / 100));
      string_unsafe_set s 2 (unsafe_chr (48 + (n / 10) mod 10));
      string_unsafe_set s 3 (unsafe_chr (48 + n mod 10));
      s

module Compare = struct
  external ( = ) : char -> char -> bool = "%equal"
  external ( <> ) : char -> char -> bool = "%notequal"
  external ( < ) : char -> char -> bool = "%lessthan"
  external ( > ) : char -> char -> bool = "%greaterthan"
  external ( <= ) : char -> char -> bool = "%lessequal"
  external ( >= ) : char -> char -> bool = "%greaterequal"
  external compare : char -> char -> int = "%compare"

  let min x y = if x <= y then x else y
  let max x y = if x >= y then x else y
end

let lowercase c =
  let open Compare in
  if (c >= 'A' && c <= 'Z')
  || (c >= '\192' && c <= '\214')
  || (c >= '\216' && c <= '\222')
  then unsafe_chr(code c + 32)
  else c

let uppercase c =
  let open Compare in
  if (c >= 'a' && c <= 'z')
  || (c >= '\224' && c <= '\246')
  || (c >= '\248' && c <= '\254')
  then unsafe_chr(code c - 32)
  else c

type t = char

let compare c1 c2 = code c1 - code c2
