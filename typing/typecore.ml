(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Typechecking for the core language *)

open Misc
open Asttypes
open Parsetree
open Types
open Typedtree
open Btype
open Ctype

type error =
    Polymorphic_label of Longident.t
  | Constructor_arity_mismatch of Longident.t * int * int
  | Label_mismatch of Longident.t * (type_expr * type_expr) list
  | Pattern_type_clash of (type_expr * type_expr) list
  | Pattern_effect_clash of (type_expr * type_expr) list
  | Or_pattern_type_clash of Ident.t * (type_expr * type_expr) list
  | Multiply_bound_variable of string
  | Orpat_vars of Ident.t
  | Expr_type_clash of (type_expr * type_expr) list
  | Expr_effect_clash of (type_expr * type_expr) list
  | Apply_non_function of type_expr
  | Apply_wrong_label of label * type_expr
  | Label_multiply_defined of string
  | Label_missing of Ident.t list
  | Label_not_mutable of Longident.t
  | Label_effect_clash of (type_expr * type_expr) list
  | Wrong_name of string * type_expr * string * Path.t * Longident.t
  | Name_type_mismatch of
      string * Longident.t * (Path.t * Path.t) * (Path.t * Path.t) list
  | Invalid_format of string
  | Undefined_method of type_expr * string
  | Undefined_inherited_method of string
  | Virtual_class of Longident.t
  | Private_type of type_expr
  | Private_label of Longident.t * type_expr
  | Unbound_instance_variable of string
  | Instance_variable_not_mutable of bool * string
  | Not_subtype of (type_expr * type_expr) list * (type_expr * type_expr) list
  | Outside_class
  | Value_multiply_overridden of string
  | Coercion_failure of
      type_expr * type_expr * (type_expr * type_expr) list * bool
  | Too_many_arguments of bool * type_expr
  | Abstract_wrong_label of label * type_expr
  | Scoping_let_module of string * type_expr
  | Masked_instance_variable of Longident.t
  | Not_a_variant_type of Longident.t
  | Incoherent_label_order
  | Less_general of string * (type_expr * type_expr) list
  | Modules_not_allowed
  | Cannot_infer_signature
  | Not_a_packed_module of type_expr
  | Recursive_local_constraint of (type_expr * type_expr) list
  | Unexpected_existential
  | Unqualified_gadt_pattern of Path.t * string
  | Invalid_interval
  | Invalid_for_loop_index
  | No_value_clauses
  | Exception_pattern_below_toplevel
  | Effect_pattern_below_toplevel
  | Invalid_continuation_pattern
  | Unexpected_continuation_pattern of Longident.t
  | Missing_continuation_pattern of Longident.t

exception Error of Location.t * Env.t * error
exception Error_forward of Location.error

(* Forward declaration, to be filled in by Typemod.type_module *)

let type_module =
  ref ((fun env md -> assert false) :
       Env.t -> Parsetree.module_expr -> Typedtree.module_expr)

(* Forward declaration, to be filled in by Typemod.type_open *)

let type_open =
  ref (fun _ -> assert false)

(* Forward declaration, to be filled in by Typemod.type_package *)

let type_package =
  ref (fun _ -> assert false)

(* Forward declaration, to be filled in by Typeclass.class_structure *)
let type_object =
  ref (fun env s -> assert false :
       Env.t -> Location.t -> Parsetree.class_structure ->
         Typedtree.class_structure * Types.class_signature * string list)

(*
  Saving and outputting type information.
  We keep these function names short, because they have to be
  called each time we create a record of type [Typedtree.expression]
  or [Typedtree.pattern] that will end up in the typed AST.
*)
let re node =
  Cmt_format.add_saved_type (Cmt_format.Partial_expression node);
  Stypes.record (Stypes.Ti_expr node);
  node
;;
let rp node =
  Cmt_format.add_saved_type (Cmt_format.Partial_pattern node);
  Stypes.record (Stypes.Ti_pat node);
  node
;;


let fst3 (x, _, _) = x
let snd3 (_,x,_) = x

let case lhs rhs =
  {c_lhs = lhs; c_guard = None; c_rhs = rhs}

(* Upper approximation of free identifiers on the parse tree *)

let iter_expression f e =

  let rec expr e =
    f e;
    match e.pexp_desc with
    | Pexp_extension _ (* we don't iterate under extension point *)
    | Pexp_ident _
    | Pexp_new _
    | Pexp_constant _ -> ()
    | Pexp_function pel -> List.iter case pel
    | Pexp_fun (_, eo, _, e) -> may expr eo; expr e
    | Pexp_apply (e, lel) -> expr e; List.iter (fun (_, e) -> expr e) lel
    | Pexp_let (_, pel, e) ->  expr e; List.iter binding pel
    | Pexp_match (e, pel)
    | Pexp_try (e, pel) -> expr e; List.iter case pel
    | Pexp_array el
    | Pexp_tuple el -> List.iter expr el
    | Pexp_construct (_, eo)
    | Pexp_variant (_, eo)
    | Pexp_perform (_, eo) -> may expr eo
    | Pexp_record (iel, eo) ->
        may expr eo; List.iter (fun (_, e) -> expr e) iel
    | Pexp_open (_, _, e)
    | Pexp_newtype (_, _, e)
    | Pexp_poly (e, _)
    | Pexp_lazy e
    | Pexp_assert e
    | Pexp_setinstvar (_, e)
    | Pexp_send (e, _)
    | Pexp_constraint (e, _)
    | Pexp_coerce (e, _, _)
    | Pexp_field (e, _) -> expr e
    | Pexp_while (e1, e2)
    | Pexp_sequence (e1, e2)
    | Pexp_setfield (e1, _, e2) -> expr e1; expr e2
    | Pexp_ifthenelse (e1, e2, eo) -> expr e1; expr e2; may expr eo
    | Pexp_for (_, e1, e2, _, e3) -> expr e1; expr e2; expr e3
    | Pexp_override sel -> List.iter (fun (_, e) -> expr e) sel
    | Pexp_letmodule (_, me, e) -> expr e; module_expr me
    | Pexp_object { pcstr_fields = fs } -> List.iter class_field fs
    | Pexp_pack me -> module_expr me

  and case {pc_lhs = _; pc_guard; pc_rhs} =
    may expr pc_guard;
    expr pc_rhs

  and binding x =
    expr x.pvb_expr

  and module_expr me =
    match me.pmod_desc with
    | Pmod_extension _
    | Pmod_ident _ -> ()
    | Pmod_structure str -> List.iter structure_item str
    | Pmod_constraint (me, _)
    | Pmod_functor (_, _, me) -> module_expr me
    | Pmod_apply (me1, me2) -> module_expr me1; module_expr me2
    | Pmod_unpack e -> expr e


  and structure_item str =
    match str.pstr_desc with
    | Pstr_eval (e, _) -> expr e
    | Pstr_value (_, pel) -> List.iter binding pel
    | Pstr_primitive _
    | Pstr_type _
    | Pstr_typext _
    | Pstr_exception _
    | Pstr_effect _
    | Pstr_modtype _
    | Pstr_open _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension _ -> ()
    | Pstr_include {pincl_mod = me}
    | Pstr_module {pmb_expr = me} -> module_expr me
    | Pstr_recmodule l -> List.iter (fun x -> module_expr x.pmb_expr) l
    | Pstr_class cdl -> List.iter (fun c -> class_expr c.pci_expr) cdl

  and class_expr ce =
    match ce.pcl_desc with
    | Pcl_constr _ -> ()
    | Pcl_structure { pcstr_fields = fs } -> List.iter class_field fs
    | Pcl_fun (_, eo, _,  ce) -> may expr eo; class_expr ce
    | Pcl_apply (ce, lel) ->
        class_expr ce; List.iter (fun (_, e) -> expr e) lel
    | Pcl_let (_, pel, ce) ->
        List.iter binding pel; class_expr ce
    | Pcl_constraint (ce, _) -> class_expr ce
    | Pcl_extension _ -> ()

  and class_field cf =
    match cf.pcf_desc with
    | Pcf_inherit (_, ce, _) -> class_expr ce
    | Pcf_val (_, _, Cfk_virtual _)
    | Pcf_method (_, _, Cfk_virtual _ ) | Pcf_constraint _ -> ()
    | Pcf_val (_, _, Cfk_concrete (_, e))
    | Pcf_method (_, _, Cfk_concrete (_, e)) -> expr e
    | Pcf_initializer e -> expr e
    | Pcf_attribute _ | Pcf_extension _ -> ()

  in
  expr e


let all_idents_cases el =
  let idents = Hashtbl.create 8 in
  let f = function
    | {pexp_desc=Pexp_ident { txt = Longident.Lident id; _ }; _} ->
        Hashtbl.replace idents id ()
    | _ -> ()
  in
  List.iter
    (fun cp ->
      may (iter_expression f) cp.pc_guard;
      iter_expression f cp.pc_rhs
    )
    el;
  Hashtbl.fold (fun x () rest -> x :: rest) idents []


(* Typing of constants *)

let type_constant = function
    Const_int _ -> instance_def Predef.type_int
  | Const_char _ -> instance_def Predef.type_char
  | Const_string _ -> instance_def Predef.type_string
  | Const_float _ -> instance_def Predef.type_float
  | Const_int32 _ -> instance_def Predef.type_int32
  | Const_int64 _ -> instance_def Predef.type_int64
  | Const_nativeint _ -> instance_def Predef.type_nativeint

(* Specific version of type_option, using newty rather than newgenty *)

let type_option ty =
  newty (Tconstr(Predef.path_option, [ty], Stype, ref Mnil))

let mkexp exp_desc exp_type exp_loc exp_env =
  { exp_desc; exp_type; exp_loc; exp_env; exp_extra = []; exp_attributes = [] }

let option_none ty loc =
  let lid = Longident.Lident "None"
  and env = Env.initial_safe_string in
  let cnone = Env.lookup_constructor lid env in
  mkexp (Texp_construct(mknoloc lid, cnone, [])) ty loc env

let option_some texp =
  let lid = Longident.Lident "Some" in
  let csome = Env.lookup_constructor lid Env.initial_safe_string in
  mkexp ( Texp_construct(mknoloc lid , csome, [texp]) )
    (type_option texp.exp_type) texp.exp_loc texp.exp_env

let extract_option_type env ty =
  match expand_head env ty with {desc = Tconstr(path, [ty], _, _)}
    when Path.same path Predef.path_option -> ty
  | _ -> assert false

let extract_concrete_record env ty =
  match extract_concrete_typedecl env ty with
    (p0, p, {type_kind=Type_record (fields, _)}) -> (p0, p, fields)
  | _ -> raise Not_found

let extract_concrete_variant env ty =
  match extract_concrete_typedecl env ty with
    (p0, p, {type_kind=Type_variant cstrs}) -> (p0, p, cstrs)
  | (p0, p, {type_kind=Type_open}) -> (p0, p, [])
  | _ -> raise Not_found

let extract_label_names sexp env ty =
  try
    let (_, _,fields) = extract_concrete_record env ty in
    List.map (fun l -> l.Types.ld_id) fields
  with Not_found ->
    assert false

let explicit_arity =
  List.exists
    (function
      | ({txt="ocaml.explicit_arity"|"explicit_arity"; _}, _) -> true
      | _ -> false
    )

(* Typing of patterns *)

(* unification inside type_pat*)
let unify_pat_types loc env ty ty' =
  try
    unify env ty ty'
  with
    Unify trace ->
      raise(Error(loc, env, Pattern_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, env, Typetexp.Variant_tags (l1, l2)))

(* unification inside type_exp and type_expect *)
let unify_exp_types loc env ty expected_ty =
  (* Format.eprintf "@[%a@ %a@]@." Printtyp.raw_type_expr exp.exp_type
    Printtyp.raw_type_expr expected_ty; *)
  try
    unify env ty expected_ty
  with
    Unify trace ->
      raise(Error(loc, env, Expr_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, env, Typetexp.Variant_tags (l1, l2)))

(* effect unification inside type_pat *)
let unify_pat_effects loc env eff expected_eff =
  try
    unify env eff expected_eff
  with
    Unify trace ->
      raise(Error(loc, env, Pattern_effect_clash(trace)))

(* effect unification inside type_exp and type_expect *)
let unify_exp_effects loc env eff expected_eff =
  try
    unify env eff expected_eff
  with
    Unify trace ->
      raise(Error(loc, env, Expr_effect_clash(trace)))

(* level at which to create the local type declarations *)
let newtype_level = ref None
let get_newtype_level () =
  match !newtype_level with
    Some y -> y
  | None -> assert false

let unify_pat_types_gadt loc env ty ty' =
  let newtype_level =
    match !newtype_level with
    | None -> assert false
    | Some x -> x
  in
  try
    unify_gadt ~newtype_level env ty ty'
  with
    Unify trace ->
      raise(Error(loc, !env, Pattern_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, !env, Typetexp.Variant_tags (l1, l2)))
  | Unification_recursive_abbrev trace ->
      raise(Error(loc, !env, Recursive_local_constraint trace))


(* Creating new conjunctive types is not allowed when typing patterns *)

let unify_pat env pat expected_ty =
  unify_pat_types pat.pat_loc env pat.pat_type expected_ty

(* make all Reither present in open variants *)
let finalize_variant pat =
  match pat.pat_desc with
    Tpat_variant(tag, opat, r) ->
      let row =
        match expand_head pat.pat_env pat.pat_type with
          {desc = Tvariant row} -> r := row; row_repr row
        | _ -> assert false
      in
      begin match row_field tag row with
      | Rabsent -> () (* assert false *)
      | Reither (true, [], _, e) when not row.row_closed ->
          set_row_field e (Rpresent None)
      | Reither (false, ty::tl, _, e) when not row.row_closed ->
          set_row_field e (Rpresent (Some ty));
          begin match opat with None -> assert false
          | Some pat -> List.iter (unify_pat pat.pat_env pat) (ty::tl)
          end
      | Reither (c, l, true, e) when not (row_fixed row) ->
          set_row_field e (Reither (c, [], false, ref None))
      | _ -> ()
      end;
      (* Force check of well-formedness   WHY? *)
      (* unify_pat pat.pat_env pat
        (newty(Tvariant{row_fields=[]; row_more=newvar(); row_closed=false;
                        row_bound=(); row_fixed=false; row_name=None})); *)
  | _ -> ()

let rec iter_pattern f p =
  f p;
  iter_pattern_desc (iter_pattern f) p.pat_desc

let has_variants p =
  try
    iter_pattern (function {pat_desc=Tpat_variant _} -> raise Exit | _ -> ())
      p;
    false
  with Exit ->
    true


(* pattern environment *)
let pattern_variables = ref ([] :
 (Ident.t * type_expr * string loc * Location.t * bool (* as-variable *)) list)
let pattern_force = ref ([] : (unit -> unit) list)
let pattern_scope = ref (None : Annot.ident option);;
let allow_modules = ref false
let module_variables = ref ([] : (string loc * Location.t) list)
let reset_pattern scope allow =
  pattern_variables := [];
  pattern_force := [];
  pattern_scope := scope;
  allow_modules := allow;
  module_variables := [];
;;

let enter_variable ?(is_module=false) ?(is_as_variable=false) loc name ty =
  if List.exists (fun (id, _, _, _, _) -> Ident.name id = name.txt)
      !pattern_variables
  then raise(Error(loc, Env.empty, Multiply_bound_variable name.txt));
  let id = Ident.create name.txt in
  pattern_variables :=
    (id, ty, name, loc, is_as_variable) :: !pattern_variables;
  if is_module then begin
    (* Note: unpack patterns enter a variable of the same name *)
    if not !allow_modules then
      raise (Error (loc, Env.empty, Modules_not_allowed));
    module_variables := (name, loc) :: !module_variables
  end else
    (* moved to genannot *)
    may (fun s -> Stypes.record (Stypes.An_ident (name.loc, name.txt, s)))
        !pattern_scope;
  id

let sort_pattern_variables vs =
  List.sort
    (fun (x,_,_,_,_) (y,_,_,_,_) ->
      Pervasives.compare (Ident.name x) (Ident.name y))
    vs

let enter_orpat_variables loc env  p1_vs p2_vs =
  (* unify_vars operate on sorted lists *)

  let p1_vs = sort_pattern_variables p1_vs
  and p2_vs = sort_pattern_variables p2_vs in

  let rec unify_vars p1_vs p2_vs = match p1_vs, p2_vs with
      | (x1,t1,_,l1,a1)::rem1, (x2,t2,_,l2,a2)::rem2 when Ident.equal x1 x2 ->
          if x1==x2 then
            unify_vars rem1 rem2
          else begin
            begin try
              unify env t1 t2
            with
            | Unify trace ->
                raise(Error(loc, env, Or_pattern_type_clash(x1, trace)))
            end;
          (x2,x1)::unify_vars rem1 rem2
          end
      | [],[] -> []
      | (x,_,_,_,_)::_, [] -> raise (Error (loc, env, Orpat_vars x))
      | [],(x,_,_,_,_)::_  -> raise (Error (loc, env, Orpat_vars x))
      | (x,_,_,_,_)::_, (y,_,_,_,_)::_ ->
          let min_var =
            if Ident.name x < Ident.name y then x
            else y in
          raise (Error (loc, env, Orpat_vars min_var)) in
  unify_vars p1_vs p2_vs

let rec build_as_type env p =
  match p.pat_desc with
    Tpat_alias(p1,_, _) -> build_as_type env p1
  | Tpat_tuple pl ->
      let tyl = List.map (build_as_type env) pl in
      newty (Ttuple tyl)
  | Tpat_construct(_, cstr, pl) ->
      let keep = cstr.cstr_private = Private || cstr.cstr_existentials <> [] in
      if keep then p.pat_type else
      let tyl = List.map (build_as_type env) pl in
      let ty_args, ty_res = instance_constructor cstr in
      List.iter2 (fun (p,ty) -> unify_pat env {p with pat_type = ty})
        (List.combine pl tyl) ty_args;
      ty_res
  | Tpat_variant(l, p', _) ->
      let ty = may_map (build_as_type env) p' in
      newty (Tvariant{row_fields=[l, Rpresent ty]; row_more=newvar Stype;
                      row_bound=(); row_name=None;
                      row_fixed=false; row_closed=false})
  | Tpat_record (lpl,_) ->
      let lbl = snd3 (List.hd lpl) in
      if lbl.lbl_private = Private then p.pat_type else
      let ty = newvar Stype in
      let ppl = List.map (fun (_, l, p) -> l.lbl_pos, p) lpl in
      let do_label lbl =
        let _, ty_arg, ty_res = instance_label false lbl in
        unify_pat env {p with pat_type = ty} ty_res;
        let refinable =
          lbl.lbl_mut = Immutable && List.mem_assoc lbl.lbl_pos ppl &&
          match (repr lbl.lbl_arg).desc with Tpoly _ -> false | _ -> true in
        if refinable then begin
          let arg = List.assoc lbl.lbl_pos ppl in
          unify_pat env {arg with pat_type = build_as_type env arg} ty_arg
        end else begin
          let _, ty_arg', ty_res' = instance_label false lbl in
          unify env ty_arg ty_arg';
          unify_pat env p ty_res'
        end in
      Array.iter do_label lbl.lbl_all;
      ty
  | Tpat_or(p1, p2, row) ->
      begin match row with
        None ->
          let ty1 = build_as_type env p1 and ty2 = build_as_type env p2 in
          unify_pat env {p2 with pat_type = ty2} ty1;
          ty1
      | Some row ->
          let row = row_repr row in
          newty (Tvariant{row with row_closed=false; row_more=newvar Stype})
      end
  | Tpat_any | Tpat_var _ | Tpat_constant _
  | Tpat_array _ | Tpat_lazy _ -> p.pat_type
  | Tpat_exception _ | Tpat_effect _ -> assert false

let build_or_pat env loc lid =
  let path, decl = Typetexp.find_type env loc lid
  in
  let tyl = List.map (fun ty -> newvar (type_sort ty)) decl.type_params in
  let row0 =
    let ty =
      expand_head env (newty(Tconstr(path, tyl, decl.type_sort, ref Mnil)))
    in
    match ty.desc with
      Tvariant row when static_row row -> row
    | _ -> raise(Error(loc, env, Not_a_variant_type lid))
  in
  let pats, fields =
    List.fold_left
      (fun (pats,fields) (l,f) ->
        match row_field_repr f with
          Rpresent None ->
            (l,None) :: pats,
            (l, Reither(true,[], true, ref None)) :: fields
        | Rpresent (Some ty) ->
            (l, Some {pat_desc=Tpat_any; pat_loc=Location.none; pat_env=env;
                      pat_type=ty; pat_extra=[]; pat_attributes=[]})
            :: pats,
            (l, Reither(false, [ty], true, ref None)) :: fields
        | _ -> pats, fields)
      ([],[]) (row_repr row0).row_fields in
  let row =
    { row_fields = List.rev fields; row_more = newvar Stype; row_bound = ();
      row_closed = false; row_fixed = false; row_name = Some (path, tyl) }
  in
  let ty = newty (Tvariant row) in
  let gloc = {loc with Location.loc_ghost=true} in
  let row' = ref {row with row_more=newvar Stype} in
  let pats =
    List.map
      (fun (l,p) ->
        {pat_desc=Tpat_variant(l,p,row'); pat_loc=gloc;
         pat_env=env; pat_type=ty; pat_extra=[]; pat_attributes=[]})
      pats
  in
  match pats with
    [] -> raise(Error(loc, env, Not_a_variant_type lid))
  | pat :: pats ->
      let r =
        List.fold_left
          (fun pat pat0 ->
            {pat_desc=Tpat_or(pat0,pat,Some row0); pat_extra=[];
             pat_loc=gloc; pat_env=env; pat_type=ty; pat_attributes=[]})
          pat pats in
      (path, rp { r with pat_loc = loc },ty)

(* Type paths *)

let rec expand_path env p =
  let decl =
    try Some (Env.find_type p env) with Not_found -> None
  in
  match decl with
    Some {type_manifest = Some ty} ->
      begin match repr ty with
        {desc=Tconstr(p,_,_,_)} -> expand_path env p
      | _ -> p
         (* PR#6394: recursive module may introduce incoherent manifest *)
      end
  | _ ->
      let p' = Env.normalize_path None env p in
      if Path.same p p' then p else expand_path env p'

let compare_type_path env tpath1 tpath2 =
  Path.same (expand_path env tpath1) (expand_path env tpath2)

(* Records *)

module NameChoice(Name : sig
  type t
  val type_kind: string
  val get_name: t -> string
  val get_type: t -> type_expr
  val get_descrs: Env.type_descriptions -> t list
  val fold: (t -> 'a -> 'a) -> Longident.t option -> Env.t -> 'a -> 'a
  val unbound_name_error: Env.t -> Longident.t loc -> 'a
end) = struct
  open Name

  let get_type_path env d =
    match (get_type d).desc with
    | Tconstr(p, _, _, _) -> p
    | _ -> assert false

  let spellcheck ppf env p lid =
    Typetexp.spellcheck_simple ppf fold
      (fun d ->
        if compare_type_path env p (get_type_path env d)
        then get_name d else "") env lid

  let lookup_from_type env tpath lid =
    let descrs = get_descrs (Env.find_type_descrs tpath env) in
    Env.mark_type_used env (Path.last tpath) (Env.find_type tpath env);
    match lid.txt with
      Longident.Lident s -> begin
        try
          List.find (fun nd -> get_name nd = s) descrs
        with Not_found ->
          raise (Error (lid.loc, env,
                        Wrong_name ("", newvar Stype, type_kind, tpath, lid.txt)))
      end
    | _ -> raise Not_found

  let rec unique eq acc = function
      [] -> List.rev acc
    | x :: rem ->
        if List.exists (eq x) acc then unique eq acc rem
        else unique eq (x :: acc) rem

  let ambiguous_types env lbl others =
    let tpath = get_type_path env lbl in
    let others =
      List.map (fun (lbl, _) -> get_type_path env lbl) others in
    let tpaths = unique (compare_type_path env) [tpath] others in
    match tpaths with
      [_] -> []
    | _ -> List.map Printtyp.string_of_path tpaths

  let disambiguate_by_type env tpath lbls =
    let check_type (lbl, _) =
      let lbl_tpath = get_type_path env lbl in
      compare_type_path env tpath lbl_tpath
    in
    List.find check_type lbls

  let disambiguate ?(warn=Location.prerr_warning) ?(check_lk=fun _ _ -> ())
      ?scope lid env opath lbls =
    let scope = match scope with None -> lbls | Some l -> l in
    let lbl = match opath with
      None ->
        begin match lbls with
          [] -> unbound_name_error env lid
        | (lbl, use) :: rest ->
            use ();
            let paths = ambiguous_types env lbl rest in
            if paths <> [] then
              warn lid.loc
                (Warnings.Ambiguous_name ([Longident.last lid.txt],
                                          paths, false));
            lbl
        end
    | Some(tpath0, tpath, pr) ->
        let warn_pr () =
          let kind = if type_kind = "record" then "field" else "constructor" in
          warn lid.loc
            (Warnings.Not_principal
               ("this type-based " ^ kind ^ " disambiguation"))
        in
        try
          let lbl, use = disambiguate_by_type env tpath scope in
          use ();
          if not pr then begin
            (* Check if non-principal type is affecting result *)
            match lbls with
              [] -> warn_pr ()
            | (lbl', use') :: rest ->
                let lbl_tpath = get_type_path env lbl' in
                if not (compare_type_path env tpath lbl_tpath) then warn_pr ()
                else
                  let paths = ambiguous_types env lbl rest in
                  if paths <> [] then
                    warn lid.loc
                      (Warnings.Ambiguous_name ([Longident.last lid.txt],
                                                paths, false))
          end;
          lbl
        with Not_found -> try
          let lbl = lookup_from_type env tpath lid in
          check_lk tpath lbl;
          let s = Printtyp.string_of_path tpath in
          warn lid.loc
            (Warnings.Name_out_of_scope (s, [Longident.last lid.txt], false));
          if not pr then warn_pr ();
          lbl
        with Not_found ->
          if lbls = [] then unbound_name_error env lid else
          let tp = (tpath0, expand_path env tpath) in
          let tpl =
            List.map
              (fun (lbl, _) ->
                let tp0 = get_type_path env lbl in
                let tp = expand_path env tp0 in
                  (tp0, tp))
              lbls
          in
          raise (Error (lid.loc, env,
                        Name_type_mismatch (type_kind, lid.txt, tp, tpl)))
    in
    begin match scope with
      (lab1,_)::_ when lab1 == lbl -> ()
    | _ ->
        Location.prerr_warning lid.loc
          (Warnings.Disambiguated_name(get_name lbl))
    end;
    lbl
end

let wrap_disambiguate kind ty f x =
  try f x with Error (loc, env, Wrong_name (_,_,tk,tp,lid)) ->
    raise (Error (loc, env, Wrong_name (kind,ty,tk,tp,lid)))

module Label = NameChoice (struct
  type t = label_description
  let type_kind = "record"
  let get_name lbl = lbl.lbl_name
  let get_type lbl = lbl.lbl_res
  let get_descrs = snd
  let fold = Env.fold_labels
  let unbound_name_error = Typetexp.unbound_label_error
end)

let disambiguate_label_by_ids keep env closed ids labels =
  let check_ids (lbl, _) =
    let lbls = Hashtbl.create 8 in
    Array.iter (fun lbl -> Hashtbl.add lbls lbl.lbl_name ()) lbl.lbl_all;
    List.for_all (Hashtbl.mem lbls) ids
  and check_closed (lbl, _) =
    (not closed || List.length ids = Array.length lbl.lbl_all)
  in
  let labels' = List.filter check_ids labels in
  if keep && labels' = [] then (false, labels) else
  let labels'' = List.filter check_closed labels' in
  if keep && labels'' = [] then (false, labels') else (true, labels'')

(* Only issue warnings once per record constructor/pattern *)
let disambiguate_lid_a_list loc closed env opath lid_a_list =
  let ids = List.map (fun (lid, _) -> Longident.last lid.txt) lid_a_list in
  let w_pr = ref false and w_amb = ref []
  and w_scope = ref [] and w_scope_ty = ref "" in
  let warn loc msg =
    let open Warnings in
    match msg with
    | Not_principal _ -> w_pr := true
    | Ambiguous_name([s], l, _) -> w_amb := (s, l) :: !w_amb
    | Name_out_of_scope(ty, [s], _) ->
        w_scope := s :: !w_scope; w_scope_ty := ty
    | _ -> Location.prerr_warning loc msg
  in
  let process_label lid =
    (* Strategy for each field:
       * collect all the labels in scope for that name
       * if the type is known and principal, just eventually warn
         if the real label was not in scope
       * fail if there is no known type and no label found
       * otherwise use other fields to reduce the list of candidates
       * if there is no known type reduce it incrementally, so that
         there is still at least one candidate (for error message)
       * if the reduced list is valid, call Label.disambiguate
     *)
    let scope = Typetexp.find_all_labels env lid.loc lid.txt in
    if opath = None && scope = [] then
      Typetexp.unbound_label_error env lid;
    let (ok, labels) =
      match opath with
        Some (_, _, true) -> (true, scope) (* disambiguate only checks scope *)
      | _  -> disambiguate_label_by_ids (opath=None) env closed ids scope
    in
    if ok then Label.disambiguate lid env opath labels ~warn ~scope
          else fst (List.hd labels) (* will fail later *)
  in
  let lbl_a_list =
    List.map (fun (lid,a) -> lid, process_label lid, a) lid_a_list in
  if !w_pr then
    Location.prerr_warning loc
      (Warnings.Not_principal "this type-based record disambiguation")
  else begin
    match List.rev !w_amb with
      (_,types)::others as amb ->
        let paths =
          List.map (fun (_,lbl,_) -> Label.get_type_path env lbl) lbl_a_list in
        let path = List.hd paths in
        if List.for_all (compare_type_path env path) (List.tl paths) then
          Location.prerr_warning loc
            (Warnings.Ambiguous_name (List.map fst amb, types, true))
        else
          List.iter
            (fun (s,l) -> Location.prerr_warning loc
                (Warnings.Ambiguous_name ([s],l,false)))
            amb
    | _ -> ()
  end;
  if !w_scope <> [] then
    Location.prerr_warning loc
      (Warnings.Name_out_of_scope (!w_scope_ty, List.rev !w_scope, true));
  lbl_a_list

let rec find_record_qual = function
  | [] -> None
  | ({ txt = Longident.Ldot (modname, _) }, _) :: _ -> Some modname
  | _ :: rest -> find_record_qual rest

let type_label_a_list ?labels loc closed env type_lbl_a opath lid_a_list =
  let lbl_a_list =
    match lid_a_list, labels with
      ({txt=Longident.Lident s}, _)::_, Some labels when Hashtbl.mem labels s ->
        (* Special case for rebuilt syntax trees *)
        List.map
          (function lid, a -> match lid.txt with
            Longident.Lident s -> lid, Hashtbl.find labels s, a
          | _ -> assert false)
          lid_a_list
    | _ ->
        let lid_a_list =
          match find_record_qual lid_a_list with
            None -> lid_a_list
          | Some modname ->
              List.map
                (fun (lid, a as lid_a) ->
                  match lid.txt with Longident.Lident s ->
                    {lid with txt=Longident.Ldot (modname, s)}, a
                  | _ -> lid_a)
                lid_a_list
        in
        disambiguate_lid_a_list loc closed env opath lid_a_list
  in
  (* Invariant: records are sorted in the typed tree *)
  let lbl_a_list =
    List.sort
      (fun (_,lbl1,_) (_,lbl2,_) -> compare lbl1.lbl_pos lbl2.lbl_pos)
      lbl_a_list
  in
  List.map type_lbl_a lbl_a_list
;;

(* Checks over the labels mentioned in a record pattern:
   no duplicate definitions (error); properly closed (warning) *)

let check_recordpat_labels loc lbl_pat_list closed =
  match lbl_pat_list with
  | [] -> ()                            (* should not happen *)
  | (_, label1, _) :: _ ->
      let all = label1.lbl_all in
      let defined = Array.make (Array.length all) false in
      let check_defined (_, label, _) =
        if defined.(label.lbl_pos)
        then raise(Error(loc, Env.empty, Label_multiply_defined label.lbl_name))
        else defined.(label.lbl_pos) <- true in
      List.iter check_defined lbl_pat_list;
      if closed = Closed
      && Warnings.is_active (Warnings.Non_closed_record_pattern "")
      then begin
        let undefined = ref [] in
        for i = 0 to Array.length all - 1 do
          if not defined.(i) then undefined := all.(i).lbl_name :: !undefined
        done;
        if !undefined <> [] then begin
          let u = String.concat ", " (List.rev !undefined) in
          Location.prerr_warning loc (Warnings.Non_closed_record_pattern u)
        end
      end

(* Constructors *)

module Constructor = NameChoice (struct
  type t = constructor_description
  let type_kind = "variant"
  let get_name cstr = cstr.cstr_name
  let get_type cstr = cstr.cstr_res
  let get_descrs = fst
  let fold = Env.fold_constructors
  let unbound_name_error = Typetexp.unbound_constructor_error
end)

(* unification of a type with a tconstr with
   freshly created arguments *)
let unify_head_only loc env ty constr =
  let (_, ty_res) = instance_constructor constr in
  match (repr ty_res).desc with
  | Tconstr(p,args,s,m) ->
      ty_res.desc <-
        Tconstr(p,List.map (fun ty -> newvar (type_sort ty)) args,s,m);
      enforce_constraints env ty_res;
      unify_pat_types loc env ty_res ty
  | _ -> assert false

(* Typing of patterns *)

(* Simplified patterns for effect continuations *)
let type_continuation_pat env expected_ty sp =
  let loc = sp.ppat_loc in
  match sp.ppat_desc with
  | Ppat_any -> None
  | Ppat_var name ->
      let id = enter_variable loc name expected_ty in
      Some (id, name)
  | Ppat_extension ext ->
      raise (Error_forward (Typetexp.error_of_extension ext))
  | _ -> raise (Error (loc, env, Invalid_continuation_pattern))

(* type_pat does not generate local constraints inside or patterns *)
type type_pat_mode =
  | Normal
  | Inside_or

(* type_pat propagates the expected type as well as maps for
   constructors and labels.
   Unification may update the typing environment. *)
let rec type_pat ~constrs ~labels ~no_existentials ~mode ~env ~allow_exn
                 sp expected_ty expected_eff =
  let type_pat ?(mode=mode) ?(env=env) =
    type_pat ~constrs ~labels ~no_existentials
             ~mode ~env ~allow_exn:false
  in
  let loc = sp.ppat_loc in
  match sp.ppat_desc with
    Ppat_any ->
      rp {
        pat_desc = Tpat_any;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_var name ->
      let id = enter_variable loc name expected_ty in
      rp {
        pat_desc = Tpat_var (id, name);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_unpack name ->
      let id = enter_variable loc name expected_ty ~is_module:true in
      rp {
        pat_desc = Tpat_var (id, name);
        pat_loc = sp.ppat_loc;
        pat_extra=[Tpat_unpack, loc, sp.ppat_attributes];
        pat_type = expected_ty;
        pat_attributes = [];
        pat_env = !env }
  | Ppat_constraint({ppat_desc=Ppat_var name; ppat_loc=lloc},
                    ({ptyp_desc=Ptyp_poly _} as sty)) ->
      (* explicitly polymorphic type *)
      let cty, force =
        Typetexp.transl_simple_type_delayed !env (Some Stype) sty
      in
      let ty = cty.ctyp_type in
      unify_pat_types lloc !env ty expected_ty;
      pattern_force := force :: !pattern_force;
      begin match ty.desc with
      | Tpoly (body, tyl) ->
          begin_def ();
          let _, ty' = instance_poly ~keep_names:true false tyl body in
          end_def ();
          generalize ty';
          let id = enter_variable lloc name ty' in
          rp {
            pat_desc = Tpat_var (id, name);
            pat_loc = lloc;
            pat_extra = [Tpat_constraint cty, loc, sp.ppat_attributes];
            pat_type = ty;
            pat_attributes = [];
            pat_env = !env
          }
      | _ -> assert false
      end
  | Ppat_alias(sq, name) ->
      let q = type_pat sq expected_ty expected_eff in
      begin_def ();
      let ty_var = build_as_type !env q in
      end_def ();
      generalize ty_var;
      let id = enter_variable ~is_as_variable:true loc name ty_var in
      rp {
        pat_desc = Tpat_alias(q, id, name);
        pat_loc = loc; pat_extra=[];
        pat_type = q.pat_type;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_constant cst ->
      unify_pat_types loc !env (type_constant cst) expected_ty;
      rp {
        pat_desc = Tpat_constant cst;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_interval (Const_char c1, Const_char c2) ->
      let open Ast_helper.Pat in
      let gloc = {loc with Location.loc_ghost=true} in
      let rec loop c1 c2 =
        if c1 = c2 then constant ~loc:gloc (Const_char c1)
        else
          or_ ~loc:gloc
            (constant ~loc:gloc (Const_char c1))
            (loop (Char.chr(Char.code c1 + 1)) c2)
      in
      let p = if c1 <= c2 then loop c1 c2 else loop c2 c1 in
      let p = {p with ppat_loc=loc} in
      type_pat p expected_ty expected_eff
        (* TODO: record 'extra' to remember about interval *)
  | Ppat_interval _ ->
      raise (Error (loc, !env, Invalid_interval))
  | Ppat_tuple spl ->
      if List.length spl < 2 then
        Syntaxerr.ill_formed_ast loc "Tuples must have at least 2 components.";
      let spl_ann = List.map (fun p -> (p,newvar Stype)) spl in
      let ty = newty (Ttuple(List.map snd spl_ann)) in
      unify_pat_types loc !env ty expected_ty;
      let pl = List.map (fun (p,t) -> type_pat p t expected_eff) spl_ann in
      rp {
        pat_desc = Tpat_tuple pl;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_construct(lid, sarg) ->
      let opath =
        try
          let (p0, p, _) = extract_concrete_variant !env expected_ty in
            Some (p0, p, true)
        with Not_found -> None
      in
      let constrs =
        match lid.txt, constrs with
          Longident.Lident s, Some constrs when Hashtbl.mem constrs s ->
            [Hashtbl.find constrs s, (fun () -> ())]
        | _ ->  Typetexp.find_all_constructors !env lid.loc lid.txt
      in
      let check_lk tpath constr =
        if constr.cstr_generalized then
          raise (Error (lid.loc, !env,
                        Unqualified_gadt_pattern (tpath, constr.cstr_name)))
      in
      let constr =
        wrap_disambiguate "This variant pattern is expected to have" expected_ty
          (Constructor.disambiguate lid !env opath ~check_lk) constrs
      in
      Env.mark_constructor Env.Pattern !env (Longident.last lid.txt) constr;
      Typetexp.check_deprecated loc constr.cstr_attributes constr.cstr_name;
      if no_existentials && constr.cstr_existentials <> [] then
        raise (Error (loc, !env, Unexpected_existential));
      (* if constructor is gadt, we must verify that the expected type has the
         correct head *)
      if constr.cstr_generalized then
        unify_head_only loc !env expected_ty constr;
      let sargs =
        match sarg with
          None -> []
        | Some {ppat_desc = Ppat_tuple spl} when
            constr.cstr_arity > 1 || explicit_arity sp.ppat_attributes
          -> spl
        | Some({ppat_desc = Ppat_any} as sp) when constr.cstr_arity <> 1 ->
            if constr.cstr_arity = 0 then
              Location.prerr_warning sp.ppat_loc
                                     Warnings.Wildcard_arg_to_constant_constr;
            replicate_list sp constr.cstr_arity
        | Some sp -> [sp] in
      if List.length sargs <> constr.cstr_arity then
        raise(Error(loc, !env, Constructor_arity_mismatch(lid.txt,
                                     constr.cstr_arity, List.length sargs)));
      let (ty_args, ty_res) =
        instance_constructor ~in_pattern:(env, get_newtype_level ()) constr
      in
      if constr.cstr_generalized && mode = Normal then
        unify_pat_types_gadt loc env ty_res expected_ty
      else
        unify_pat_types loc !env ty_res expected_ty;
      let args =
        List.map2 (fun p t -> type_pat p t expected_eff) sargs ty_args
      in
      rp {
        pat_desc=Tpat_construct(lid, constr, args);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_variant(l, sarg) ->
      let arg_type = match sarg with None -> [] | Some _ -> [newvar Stype] in
      let row = { row_fields =
                    [l, Reither(sarg = None, arg_type, true, ref None)];
                  row_bound = ();
                  row_closed = false;
                  row_more = newvar Stype;
                  row_fixed = false;
                  row_name = None } in
      unify_pat_types loc !env (newty (Tvariant row)) expected_ty;
      let arg =
        (* PR#6235: propagate type information *)
        match sarg, arg_type with
          Some p, [ty] -> Some (type_pat p ty expected_eff)
        | _            -> None
      in
      rp {
        pat_desc = Tpat_variant(l, arg, ref {row with row_more = newvar Stype});
        pat_loc = loc; pat_extra=[];
        pat_type =  expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_record(lid_sp_list, closed) ->
      if lid_sp_list = [] then
        Syntaxerr.ill_formed_ast loc "Records cannot be empty.";
      let opath, record_ty =
        try
          let (p0, p,_) = extract_concrete_record !env expected_ty in
          Some (p0, p, true), expected_ty
        with Not_found -> None, newvar Stype
      in
      let type_label_pat (label_lid, label, sarg) =
        begin_def ();
        let (vars, ty_arg, ty_res) = instance_label false label in
        if vars = [] then end_def ();
        begin try
          unify_pat_types loc !env ty_res record_ty
        with Unify trace ->
          raise(Error(label_lid.loc, !env,
                      Label_mismatch(label_lid.txt, trace)))
        end;
        let arg = type_pat sarg ty_arg expected_eff in
        if vars <> [] then begin
          end_def ();
          generalize ty_arg;
          List.iter generalize vars;
          let instantiated tv =
            let tv = expand_head !env tv in
            not (is_Tvar tv) || tv.level <> generic_level in
          if List.exists instantiated vars then
            raise (Error(label_lid.loc, !env, Polymorphic_label label_lid.txt))
        end;
        (label_lid, label, arg)
      in
      let lbl_pat_list =
        wrap_disambiguate "This record pattern is expected to have" expected_ty
          (type_label_a_list ?labels loc false !env type_label_pat opath)
          lid_sp_list
      in
      check_recordpat_labels loc lbl_pat_list closed;
      let mut =
        List.exists
          (fun (_, lbl, _) -> lbl.lbl_mut = Mutable)
          lbl_pat_list
      in
      if mut then begin
        let eff = instance_def (Predef.effect_io (newvar Seffect)) in
        unify_pat_effects loc !env eff expected_eff
      end;
      unify_pat_types loc !env record_ty expected_ty;
      rp {
        pat_desc = Tpat_record (lbl_pat_list, closed);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_array spl ->
      let ty_elt = newvar Stype in
      unify_pat_types
        loc !env (instance_def (Predef.type_array ty_elt)) expected_ty;
      let spl_ann = List.map (fun p -> (p,newvar Stype)) spl in
      let pl =
        List.map (fun (p,t) -> type_pat p ty_elt expected_eff) spl_ann
      in
      let eff = instance_def (Predef.effect_io (newvar Seffect)) in
      unify_pat_effects loc !env eff expected_eff;
      rp {
        pat_desc = Tpat_array pl;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_or(sp1, sp2) ->
      let initial_pattern_variables = !pattern_variables in
      let p1 = type_pat ~mode:Inside_or sp1 expected_ty expected_eff in
      let p1_variables = !pattern_variables in
      pattern_variables := initial_pattern_variables;
      let p2 = type_pat ~mode:Inside_or sp2 expected_ty expected_eff in
      let p2_variables = !pattern_variables in
      let alpha_env =
        enter_orpat_variables loc !env p1_variables p2_variables in
      pattern_variables := p1_variables;
      rp {
        pat_desc = Tpat_or(p1, alpha_pat alpha_env p2, None);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_lazy sp1 ->
      let nv = newvar Stype in
      unify_pat_types loc !env (instance_def (Predef.type_lazy_t nv))
        expected_ty;
      let p1 = type_pat sp1 nv expected_eff in
      let eff = instance_def (Predef.effect_io (newvar Seffect)) in
      unify_pat_effects loc !env eff expected_eff;
      rp {
        pat_desc = Tpat_lazy p1;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_constraint(sp, sty) ->
      (* Separate when not already separated by !principal *)
      let separate = true in
      if separate then begin_def();
      let cty, force =
        Typetexp.transl_simple_type_delayed !env (Some Stype) sty
      in
      let ty = cty.ctyp_type in
      let ty, expected_ty' =
        if separate then begin
          end_def();
          generalize_structure ty;
          instance !env ty, instance !env ty
        end else ty, ty
      in
      unify_pat_types loc !env ty expected_ty;
      let p = type_pat sp expected_ty' expected_eff in
      (*Format.printf "%a@.%a@."
        Printtyp.raw_type_expr ty
        Printtyp.raw_type_expr p.pat_type;*)
      pattern_force := force :: !pattern_force;
      let extra = (Tpat_constraint cty, loc, sp.ppat_attributes) in
      if separate then
        match p.pat_desc with
          Tpat_var (id,s) ->
            {p with pat_type = ty;
             pat_desc = Tpat_alias
               ({p with pat_desc = Tpat_any; pat_attributes = []}, id,s);
             pat_extra = [extra];
            }
        | _ -> {p with pat_type = ty;
                pat_extra = extra :: p.pat_extra}
      else p
  | Ppat_type lid ->
      let (path, p,ty) = build_or_pat !env loc lid.txt in
      unify_pat_types loc !env ty expected_ty;
      { p with pat_extra =
        (Tpat_type (path, lid), loc, sp.ppat_attributes) :: p.pat_extra }
  | Ppat_exception sp1 ->
      if not allow_exn then
        raise (Error (loc, !env, Exception_pattern_below_toplevel));
      let p1 = type_pat sp1 (instance_def Predef.type_exn) expected_eff in
      let eff = instance_def (Predef.effect_io (newvar Seffect)) in
      unify_pat_effects loc !env eff expected_eff;
      rp {
        pat_desc = Tpat_exception p1;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_effect(lid, sarg, scont) ->
      if not allow_exn then
        raise (Error (loc, !env, Effect_pattern_below_toplevel));
      let ecstr = Typetexp.find_effect_constructor !env lid.loc lid.txt in
      let sargs =
        match sarg with
        | None -> []
        | Some {ppat_desc = Ppat_tuple spl} when
            ecstr.ecstr_arity > 1 || explicit_arity sp.ppat_attributes ->
            spl
        | Some({ppat_desc = Ppat_any} as sp) when ecstr.ecstr_arity <> 1 ->
            if ecstr.ecstr_arity = 0 then
              Location.prerr_warning sp.ppat_loc
                                     Warnings.Wildcard_arg_to_constant_constr;
            replicate_list sp ecstr.ecstr_arity
        | Some sp -> [sp]
      in
      if List.length sargs <> ecstr.ecstr_arity then
        raise(Error(loc, !env, Constructor_arity_mismatch(lid.txt,
                                     ecstr.ecstr_arity, List.length sargs)));
      let (ty_args, ty_res) =
        instance_effect_constructor
          ~in_pattern:(env, get_newtype_level ()) ecstr
      in
      let args =
        List.map2 (fun p t -> type_pat p t expected_eff) sargs ty_args
      in
      let cont =
        match ty_res, scont with
        | None, None -> None
        | Some res_type, Some scont ->
            let ty_cont =
              instance_def (Predef.type_continuation res_type expected_ty)
            in
            Some (type_continuation_pat !env ty_cont scont)
        | None, Some _ ->
            raise(Error(loc, !env, Unexpected_continuation_pattern lid.txt))
        | Some _, None ->
            raise(Error(loc, !env, Missing_continuation_pattern lid.txt))
      in
        rp {
        pat_desc = Tpat_effect(lid, ecstr, args, cont);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_extension ext ->
      raise (Error_forward (Typetexp.error_of_extension ext))

let type_pat ?(allow_existentials=false) ?constrs ?labels
    ?(lev=get_current_level()) ~env ~allow_exn
    sp expected_ty expected_eff =
  newtype_level := Some lev;
  try
    let r =
      type_pat ~no_existentials:(not allow_existentials) ~constrs ~labels
        ~mode:Normal ~env ~allow_exn sp expected_ty expected_eff in
    iter_pattern (fun p -> p.pat_env <- !env) r;
    newtype_level := None;
    r
  with e ->
    newtype_level := None;
    raise e


(* this function is passed to Partial.parmatch
   to type check gadt nonexhaustiveness *)
let partial_pred ~lev env expected_ty expected_eff constrs labels p =
  let snap = snapshot () in
  try
    reset_pattern None true;
    let typed_p =
      type_pat ~allow_existentials:true ~lev
        ~constrs ~labels ~env:(ref env) ~allow_exn:true
        p expected_ty expected_eff
    in
    backtrack snap;
    (* types are invalidated but we don't need them here *)
    Some typed_p
  with _ ->
    backtrack snap;
    None

let check_partial ?(lev=get_current_level ()) env expected_ty expected_eff =
  Parmatch.check_partial_gadt
    (partial_pred ~lev env expected_ty expected_eff)
    env

let rec iter3 f lst1 lst2 lst3 =
  match lst1,lst2,lst3 with
  | x1::xs1,x2::xs2,x3::xs3 ->
      f x1 x2 x3;
      iter3 f xs1 xs2 xs3
  | [],[],[] ->
      ()
  | _ ->
      assert false

let add_pattern_variables ?check ?check_as env =
  let pv = get_ref pattern_variables in
  (List.fold_right
     (fun (id, ty, name, loc, as_var) env ->
       let check = if as_var then check_as else check in
       Env.add_value ?check id
         {val_type = ty; val_kind = Val_reg; Types.val_loc = loc;
          val_attributes = [];
         } env
     )
     pv env,
   get_ref module_variables)

let type_pattern ~lev ~allow_exn env spat scope expected_ty expected_eff =
  reset_pattern scope true;
  let new_env = ref env in
  let pat =
    type_pat ~allow_existentials:true ~lev ~env:new_env ~allow_exn
             spat expected_ty expected_eff
  in
  let new_env, unpacks =
    add_pattern_variables !new_env
      ~check:(fun s -> Warnings.Unused_var_strict s)
      ~check_as:(fun s -> Warnings.Unused_var s) in
  (pat, new_env, get_ref pattern_force, unpacks)

let type_pattern_list ~allow_exn env spatl scope expected_tys expected_eff allow =
  reset_pattern scope allow;
  let new_env = ref env in
  let patl =
    List.map2
      (fun spat expected_ty ->
        type_pat ~allow_exn ~env:new_env spat expected_ty expected_eff)
      spatl expected_tys
  in
  let new_env, unpacks = add_pattern_variables !new_env in
  (patl, new_env, get_ref pattern_force, unpacks)

let type_class_arg_pattern cl_num val_env met_env l spat eff_expected =
  reset_pattern None false;
  let nv = newvar Stype in
  let pat =
    type_pat ~allow_exn:false ~env:(ref val_env) spat nv eff_expected
  in
  if has_variants pat then begin
    Parmatch.pressure_variants val_env [pat];
    iter_pattern finalize_variant pat
  end;
  List.iter (fun f -> f()) (get_ref pattern_force);
  if is_optional l then unify_pat val_env pat (type_option (newvar Stype));
  let (pv, met_env) =
    List.fold_right
      (fun (id, ty, name, loc, as_var) (pv, env) ->
         let check s =
           if as_var then Warnings.Unused_var s
           else Warnings.Unused_var_strict s in
         let id' = Ident.create (Ident.name id) in
         ((id', name, id, ty)::pv,
          Env.add_value id' {val_type = ty;
                             val_kind = Val_ivar (Immutable, cl_num);
                             val_attributes = [];
                             Types.val_loc = loc;
                            } ~check
            env))
      !pattern_variables ([], met_env)
  in
  let val_env, _ = add_pattern_variables val_env in
  (pat, pv, val_env, met_env)

let type_self_pattern cl_num privty val_env met_env par_env spat eff_expected =
  let open Ast_helper in
  let spat =
    Pat.mk (Ppat_alias (Pat.mk(Ppat_alias (spat, mknoloc "selfpat-*")),
                        mknoloc ("selfpat-" ^ cl_num)))
  in
  reset_pattern None false;
  let nv = newvar Stype in
  let pat =
    type_pat ~allow_exn:false ~env:(ref val_env) spat nv eff_expected
  in
  List.iter (fun f -> f()) (get_ref pattern_force);
  let meths = ref Meths.empty in
  let vars = ref Vars.empty in
  let pv = !pattern_variables in
  pattern_variables := [];
  let (val_env, met_env, par_env) =
    List.fold_right
      (fun (id, ty, name, loc, as_var) (val_env, met_env, par_env) ->
         (Env.add_value id {val_type = ty;
                            val_kind = Val_unbound;
                            val_attributes = [];
                            Types.val_loc = loc;
                           } val_env,
          Env.add_value id {val_type = ty;
                            val_kind = Val_self (meths, vars, cl_num, privty);
                            val_attributes = [];
                            Types.val_loc = loc;
                           }
            ~check:(fun s -> if as_var then Warnings.Unused_var s
                             else Warnings.Unused_var_strict s)
            met_env,
          Env.add_value id {val_type = ty; val_kind = Val_unbound;
                            val_attributes = [];
                            Types.val_loc = loc;
                           } par_env))
      pv (val_env, met_env, par_env)
  in
  (pat, meths, vars, val_env, met_env, par_env)

let delayed_checks = ref []
let reset_delayed_checks () = delayed_checks := []
let add_delayed_check f =
  delayed_checks := (f, Warnings.backup ()) :: !delayed_checks

let force_delayed_checks () =
  (* checks may change type levels *)
  let snap = Btype.snapshot () in
  let w_old = Warnings.backup () in
  List.iter
    (fun (f, w) -> Warnings.restore w; f ())
    (List.rev !delayed_checks);
  Warnings.restore w_old;
  reset_delayed_checks ();
  Btype.backtrack snap

let rec final_subexpression sexp =
  match sexp.pexp_desc with
    Pexp_let (_, _, e)
  | Pexp_sequence (_, e)
  | Pexp_try (e, _)
  | Pexp_ifthenelse (_, e, _)
  | Pexp_match (_, {pc_rhs=e} :: _)
    -> final_subexpression e
  | _ -> sexp

(* Generalization criterion for expressions *)

let rec is_nonexpansive exp =
  match exp.exp_desc with
    Texp_ident(_,_,_) -> true
  | Texp_constant _ -> true
  | Texp_let(rec_flag, pat_exp_list, body) ->
      List.for_all (fun vb -> is_nonexpansive vb.vb_expr) pat_exp_list &&
      is_nonexpansive body
  | Texp_function _ -> true
  | Texp_apply(e, (_,None,_)::el) ->
      is_nonexpansive e && List.for_all is_nonexpansive_opt (List.map snd3 el)
  | Texp_match(e, cases, _) ->
      is_nonexpansive e &&
      List.for_all
        (fun {c_lhs = _; c_guard; c_rhs} ->
           is_nonexpansive_opt c_guard && is_nonexpansive c_rhs
        ) cases
  | Texp_tuple el ->
      List.for_all is_nonexpansive el
  | Texp_construct( _, _, el) ->
      List.for_all is_nonexpansive el
  | Texp_variant(_, arg) -> is_nonexpansive_opt arg
  | Texp_record(lbl_exp_list, opt_init_exp) ->
      List.for_all
        (fun (_, lbl, exp) -> lbl.lbl_mut = Immutable && is_nonexpansive exp)
        lbl_exp_list
      && is_nonexpansive_opt opt_init_exp
  | Texp_field(exp, lbl, _) -> is_nonexpansive exp
  | Texp_array [] -> true
  | Texp_ifthenelse(cond, ifso, ifnot) ->
      is_nonexpansive ifso && is_nonexpansive_opt ifnot
  | Texp_sequence (e1, e2) -> is_nonexpansive e2  (* PR#4354 *)
  | Texp_new (_, _, cl_decl) when Ctype.class_type_arity cl_decl.cty_type > 0 ->
      true
  (* Note: nonexpansive only means no _observable_ side effects *)
  | Texp_lazy e -> is_nonexpansive e
  | Texp_object ({cstr_fields=fields; cstr_type = { csig_vars=vars}}, _) ->
      let count = ref 0 in
      List.for_all
        (fun field -> match field.cf_desc with
            Tcf_method _ -> true
          | Tcf_val (_, _, _, Tcfk_concrete (_, e), _) ->
              incr count; is_nonexpansive e
          | Tcf_val (_, _, _, Tcfk_virtual _, _) ->
              incr count; true
          | Tcf_initializer e -> is_nonexpansive e
          | Tcf_constraint _ -> true
          | Tcf_inherit _ -> false
          | Tcf_attribute _ -> true)
        fields &&
      Vars.fold (fun _ (mut,_,_) b -> decr count; b && mut = Immutable)
        vars true &&
      !count = 0
  | Texp_letmodule (_, _, mexp, e) ->
      is_nonexpansive_mod mexp && is_nonexpansive e
  | Texp_pack mexp ->
      is_nonexpansive_mod mexp
  | _ -> false

and is_nonexpansive_mod mexp =
  match mexp.mod_desc with
  | Tmod_ident _ -> true
  | Tmod_functor _ -> true
  | Tmod_unpack (e, _) -> is_nonexpansive e
  | Tmod_constraint (m, _, _, _) -> is_nonexpansive_mod m
  | Tmod_structure str ->
      List.for_all
        (fun item -> match item.str_desc with
          | Tstr_eval _ | Tstr_primitive _ | Tstr_type _
          | Tstr_modtype _ | Tstr_open _ | Tstr_class_type _  -> true
          | Tstr_value (_, pat_exp_list) ->
              List.for_all (fun vb -> is_nonexpansive vb.vb_expr) pat_exp_list
          | Tstr_module {mb_expr=m;_}
          | Tstr_include {incl_mod=m;_} -> is_nonexpansive_mod m
          | Tstr_recmodule id_mod_list ->
              List.for_all (fun {mb_expr=m;_} -> is_nonexpansive_mod m)
                id_mod_list
          | Tstr_exception {ext_kind = Text_decl _} ->
              false (* true would be unsound *)
          | Tstr_effect {eff_kind = Teff_variant _; eff_manifest = None} ->
              false (* true would be unsound *)
          | Tstr_exception {ext_kind = Text_rebind _} -> true
          | Tstr_effect ({eff_kind = Teff_abstract}
                         | {eff_manifest = Some _}) ->
              true
          | Tstr_typext te ->
              List.for_all
                (function {ext_kind = Text_decl _} -> false
                        | {ext_kind = Text_rebind _} -> true)
                te.tyext_constructors
          | Tstr_class _ -> false (* could be more precise *)
          | Tstr_attribute _ -> true
        )
        str.str_items
  | Tmod_apply _ -> false

and is_nonexpansive_opt = function
    None -> true
  | Some e -> is_nonexpansive e

(* Approximate the type of an expression, for better recursion *)

let rec approx_type env sty =
  match sty.ptyp_desc with
    Ptyp_arrow (p, _, _, sty) ->
      let ty1 =
        if is_optional p then type_option (newvar Stype) else newvar Stype
      in
      newty (Tarrow (p, ty1, newvar Seffect, approx_type env sty, Cok))
  | Ptyp_tuple args ->
      newty (Ttuple (List.map (approx_type env) args))
  | Ptyp_constr (lid, ctl) ->
      begin try
        let (path, decl) = Env.lookup_type lid.txt env in
        if List.length ctl <> decl.type_arity then raise Not_found;
        let tyl = List.map (approx_type env) ctl in
        newconstr path tyl decl.type_sort
      with Not_found -> newvar Stype
      end
  | Ptyp_poly (_, sty) ->
      approx_type env sty
  | _ -> newvar Stype

let rec type_approx env sexp =
  match sexp.pexp_desc with
    Pexp_let (_, _, e) -> type_approx env e
  | Pexp_fun (p, _, _, e) when is_optional p ->
      let ty1 = type_option (newvar Stype) in
      let ty2 = newvar Seffect in
      let ty3 = type_approx env e in
       newty (Tarrow(p, ty1, ty2, ty3, Cok))
  | Pexp_fun (p,_,_, e) ->
      let ty1 = newvar Stype in
      let ty2 = newvar Seffect in
      let ty3 = type_approx env e in
       newty (Tarrow(p, ty1, ty2, ty3, Cok))
  | Pexp_function ({pc_rhs=e}::_) ->
      let ty1 = newvar Stype in
      let ty2 = newvar Seffect in
      let ty3 = type_approx env e in
       newty (Tarrow("", ty1, ty2, ty3, Cok))
  | Pexp_match (_, {pc_rhs=e}::_) -> type_approx env e
  | Pexp_try (e, _) -> type_approx env e
  | Pexp_tuple l -> newty (Ttuple(List.map (type_approx env) l))
  | Pexp_ifthenelse (_,e,_) -> type_approx env e
  | Pexp_sequence (_,e) -> type_approx env e
  | Pexp_constraint (e, sty) ->
      let ty = type_approx env e in
      let ty1 = approx_type env sty in
      begin try unify env ty ty1 with Unify trace ->
        raise(Error(sexp.pexp_loc, env, Expr_type_clash trace))
      end;
      ty1
  | Pexp_coerce (e, sty1, sty2) ->
      let approx_ty_opt = function
        | None -> newvar Stype
        | Some sty -> approx_type env sty
      in
      let ty = type_approx env e
      and ty1 = approx_ty_opt sty1
      and ty2 = approx_type env sty2 in
      begin try unify env ty ty1 with Unify trace ->
        raise(Error(sexp.pexp_loc, env, Expr_type_clash trace))
      end;
      ty2
  | _ -> newvar Stype

(* List labels in a function type, and whether return type is a variable *)
let rec list_labels_aux env visited ls ty_fun =
  let ty = expand_head env ty_fun in
  if List.memq ty visited then
    List.rev ls, false
  else match ty.desc with
    Tarrow (l, _, _, ty_res, _) ->
      list_labels_aux env (ty::visited) (l::ls) ty_res
  | _ ->
      List.rev ls, is_Tvar ty

let list_labels env ty =
  wrap_trace_gadt_instances env (list_labels_aux env [] []) ty

(* Check that all univars are safe in a type *)
let check_univars env expans kind exp ty_expected vars =
  if expans && not (is_nonexpansive exp) then
    generalize_expansive env exp.exp_type;
  (* need to expand twice? cf. Ctype.unify2 *)
  let vars = List.map (expand_head env) vars in
  let vars = List.map (expand_head env) vars in
  let vars' =
    List.filter
      (fun t ->
        let t = repr t in
        generalize t;
        match t.desc with
          Tvar(name, sort) when t.level = generic_level ->
            log_type t; t.desc <- Tunivar(name, sort); true
        | _ -> false)
      vars in
  if List.length vars = List.length vars' then () else
  let ty = newgenty (Tpoly(repr exp.exp_type, vars'))
  and ty_expected = repr ty_expected in
  raise (Error (exp.exp_loc, env,
                Less_general(kind, [ty, ty; ty_expected, ty_expected])))

(* Check that a type is not a function *)
let check_application_result env statement exp =
  let loc = exp.exp_loc in
  match (expand_head env exp.exp_type).desc with
  | Tarrow _ ->
      Location.prerr_warning exp.exp_loc Warnings.Partial_application
  | Tvar _ -> ()
  | Tconstr (p, _, _, _) when Path.same p Predef.path_unit -> ()
  | _ ->
      if statement then
        Location.prerr_warning loc Warnings.Statement_type

(* Check that a type is generalizable at some level *)
let generalizable level ty =
  let rec check ty =
    let ty = repr ty in
    if ty.level < lowest_level then () else
    if ty.level <= level then raise Exit else
    (mark_type_node ty; iter_type_expr check ty)
  in
  try check ty; unmark_type ty; true
  with Exit -> unmark_type ty; false

(* Hack to allow coercion of self. Will clean-up later. *)
let self_coercion = ref ([] : (Path.t * Location.t list ref) list)

(* Helpers for packaged modules. *)
let create_package_type loc env (p, l) =
  let s = !Typetexp.transl_modtype_longident loc env p in
  let fields =
    List.map (fun (name, ct) ->
        name, Typetexp.transl_simple_type env false (Some Stype) ct) l
  in
  let ty = newty (Tpackage (s,
                    List.map fst l,
                   List.map (fun (_, cty) -> cty.ctyp_type) fields))
  in
   (s, fields, ty)

 let wrap_unpacks sexp unpacks =
   let open Ast_helper in
   List.fold_left
     (fun sexp (name, loc) ->
       Exp.letmodule ~loc:sexp.pexp_loc
         name
         (Mod.unpack ~loc
            (Exp.ident ~loc:name.loc (mkloc (Longident.Lident name.txt) name.loc)))
         sexp
     )
    sexp unpacks

(* Helpers for type_cases *)

let contains_variant_either ty =
  let rec loop ty =
    let ty = repr ty in
    if ty.level >= lowest_level then begin
      mark_type_node ty;
      match ty.desc with
        Tvariant row ->
          let row = row_repr row in
          if not row.row_fixed then
            List.iter
              (fun (_,f) ->
                match row_field_repr f with Reither _ -> raise Exit | _ -> ())
              row.row_fields;
          iter_row loop row
      | _ ->
          iter_type_expr loop ty
    end
  in
  try loop ty; unmark_type ty; false
  with Exit -> unmark_type ty; true

let iter_ppat f p =
  match p.ppat_desc with
  | Ppat_any | Ppat_var _ | Ppat_constant _ | Ppat_interval _
  | Ppat_extension _
  | Ppat_type _ | Ppat_unpack _ -> ()
  | Ppat_array pats -> List.iter f pats
  | Ppat_or (p1,p2) -> f p1; f p2
  | Ppat_effect(_, p1, p2) -> may f p1; may f p2
  | Ppat_variant (_, arg) | Ppat_construct (_, arg) -> may f arg
  | Ppat_tuple lst ->  List.iter f lst
  | Ppat_exception p | Ppat_alias (p,_)
  | Ppat_constraint (p,_) | Ppat_lazy p -> f p
  | Ppat_record (args, flag) -> List.iter (fun (_,p) -> f p) args

let contains_polymorphic_variant p =
  let rec loop p =
    match p.ppat_desc with
      Ppat_variant _ | Ppat_type _ -> raise Exit
    | _ -> iter_ppat loop p
  in
  try loop p; false with Exit -> true

let contains_gadt env p =
  let rec loop p =
    match p.ppat_desc with
      Ppat_construct (lid, _) ->
        begin try
          let cstrs = Env.lookup_all_constructors lid.txt env in
          List.iter (fun (cstr,_) -> if cstr.cstr_generalized then raise Exit)
            cstrs
        with Not_found -> ()
        end; iter_ppat loop p
    | _ -> iter_ppat loop p
  in
  try loop p; false with Exit -> true

let check_absent_variant env =
  iter_pattern
    (function {pat_desc = Tpat_variant (s, arg, row)} as pat ->
      let row = row_repr !row in
      if List.exists (fun (s',fi) -> s = s' && row_field_repr fi <> Rabsent)
          row.row_fields
      || not row.row_fixed && not (static_row row)  (* same as Ctype.poly *)
      then () else
      let ty_arg =
        match arg with None -> [] | Some p -> [correct_levels p.pat_type] in
      let row' = {row_fields = [s, Reither(arg=None,ty_arg,true,ref None)];
                  row_more = newvar Stype; row_bound = ();
                  row_closed = false; row_fixed = false; row_name = None} in
      (* Should fail *)
      unify_pat env {pat with pat_type = newty (Tvariant row')}
                    (correct_levels pat.pat_type)
      | _ -> ())

(* Duplicate types of values in the environment *)
(* XXX Should we do something about global type variables too? *)

let duplicate_ident_types loc caselist env =
  let caselist =
    List.filter (fun {pc_lhs} -> contains_gadt env pc_lhs) caselist in
  let idents = all_idents_cases caselist in
  List.fold_left
    (fun env s ->
      try
        (* XXX This will mark the value as being used;
           I don't think this is what we want *)
        let (path, desc) = Env.lookup_value (Longident.Lident s) env in
        match path with
          Path.Pident id ->
            let desc = {desc with val_type = correct_levels desc.val_type} in
            Env.add_value id desc env
        | _ -> env
      with Not_found -> env)
    env idents

let check_value_case loc env caselist =
  (* Note: A fully empty pattern matching can be generated by Camlp4
     with its revised syntax.  Let's accept it for backward
     compatibility. *)
  match caselist with
  | [] -> ()
  | caselist ->
      let has_value =
        List.exists
          (fun case ->
            match case.pc_lhs with
            | { ppat_desc = Ppat_exception _ } -> false
            | { ppat_desc = Ppat_effect _ } -> false
            | _ -> true)
          caselist
      in
      if not has_value then
        raise (Error (loc, env, No_value_clauses))

let make_exception_default caselist =
  List.map
    (fun case ->
      match case.pc_lhs with
      | { ppat_desc = Ppat_exception _ } -> case
      | { ppat_desc = Ppat_effect _ } -> case
      | pat ->
          { case with pc_lhs =
              { pat with ppat_desc =
                  Ppat_exception pat }})
    caselist

(* Typing of expressions *)

let unify_exp env exp expected_ty =
  (* Format.eprintf "@[%a@ %a@]@." Printtyp.raw_type_expr exp.exp_type
    Printtyp.raw_type_expr expected_ty; *)
    unify_exp_types exp.exp_loc env exp.exp_type expected_ty

let rec type_exp env sexp eff_expected =
  (* We now delegate everything to type_expect *)
  type_expect env sexp (newvar Stype) eff_expected

(* Typing of an expression with an expected type.
   This provide better error messages, and allows controlled
   propagation of return type information.
   In the principal case, [type_expected'] may be at generic_level.
 *)

and type_expect ?in_function env sexp ty_expected eff_expected =
  let previous_saved_types = Cmt_format.get_saved_types () in
  Typetexp.warning_enter_scope ();
  Typetexp.warning_attribute sexp.pexp_attributes;
  let exp = type_expect_ ?in_function env sexp ty_expected eff_expected in
  Typetexp.warning_leave_scope ();
  Cmt_format.set_saved_types
    (Cmt_format.Partial_expression exp :: previous_saved_types);
  exp

and type_expect_ ?in_function env sexp ty_expected eff_expected =
  let loc = sexp.pexp_loc in
  (* Record the expression type before unifying it with the expected type *)
  let rue exp =
    unify_exp env (re exp) (instance env ty_expected);
    exp
  in
  let rufe eff exp =
    unify_exp env (re exp) (instance env ty_expected);
    unify_exp_effects exp.exp_loc env eff eff_expected;
    exp
  in
  match sexp.pexp_desc with
  | Pexp_ident lid ->
      begin
        let (path, desc) = Typetexp.find_value env loc lid.txt in
        if !Clflags.annotations then begin
          let dloc = desc.Types.val_loc in
          let annot =
            if dloc.Location.loc_ghost then Annot.Iref_external
            else Annot.Iref_internal dloc
          in
          let name = Path.name ~paren:Oprint.parenthesized_ident path in
          Stypes.record (Stypes.An_ident (loc, name, annot))
        end;
        let ty = instance env (open_effects_covariant env desc.val_type) in
        rue {
          exp_desc =
            begin match desc.val_kind with
              Val_ivar (_, cl_num) ->
                let (self_path, _) =
                  Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
                in
                Texp_instvar(self_path, path,
                             match lid.txt with
                                 Longident.Lident txt -> { txt; loc = lid.loc }
                               | _ -> assert false)
            | Val_self (_, _, cl_num, _) ->
                let (path, _) =
                  Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
                in
                Texp_ident(path, lid, desc)
            | Val_unbound ->
                raise(Error(loc, env, Masked_instance_variable lid.txt))
            (*| Val_prim _ ->
                let p = Env.normalize_path (Some loc) env path in
                Env.add_required_global (Path.head p);
                Texp_ident(path, lid, desc)*)
            | _ ->
                Texp_ident(path, lid, desc)
          end;
          exp_loc = loc; exp_extra = [];
          exp_type = ty;
          exp_attributes = sexp.pexp_attributes;
          exp_env = env }
      end
  | Pexp_constant(Const_string (str, _) as cst) -> (
    (* Terrible hack for format strings *)
    let ty_exp = expand_head env ty_expected in
    let fmt6_path =
      Path.(Pdot (Pident (Ident.create_persistent "CamlinternalFormatBasics"),
                  "format6", 0)) in
    let is_format = match ty_exp.desc with
      | Tconstr(path, _, _, _) when Path.same path fmt6_path ->
        if !Clflags.principal && ty_exp.level <> generic_level then
          Location.prerr_warning loc
            (Warnings.Not_principal "this coercion to format6");
        true
      | _ -> false
    in
    if is_format then
      let format_parsetree =
        { (type_format loc str env) with pexp_loc = sexp.pexp_loc }  in
      type_expect ?in_function env format_parsetree ty_expected eff_expected
    else
      rue {
        exp_desc = Texp_constant cst;
        exp_loc = loc; exp_extra = [];
        exp_type = instance_def Predef.type_string;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  )
  | Pexp_constant cst ->
      rue {
        exp_desc = Texp_constant cst;
        exp_loc = loc; exp_extra = [];
        exp_type = type_constant cst;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_let(Nonrecursive,
             [{pvb_pat=spat; pvb_expr=sval; pvb_attributes=[]}], sbody)
    when contains_gadt env spat ->
    (* TODO: allow non-empty attributes? *)
      type_expect ?in_function env
        {sexp with
         pexp_desc = Pexp_match (sval, [Ast_helper.Exp.case spat sbody])}
        ty_expected eff_expected
  | Pexp_let(rec_flag, spat_sexp_list, sbody) ->
      let scp =
        match sexp.pexp_attributes, rec_flag with
        | [{txt="#default"},_], _ -> None
        | _, Recursive -> Some (Annot.Idef loc)
        | _, Nonrecursive -> Some (Annot.Idef sbody.pexp_loc)
      in
      let (pat_exp_list, new_env, unpacks) =
        type_let env rec_flag spat_sexp_list scp true eff_expected in
      let body =
        type_expect new_env (wrap_unpacks sbody unpacks) ty_expected eff_expected in
      re {
        exp_desc = Texp_let(rec_flag, pat_exp_list, body);
        exp_loc = loc; exp_extra = [];
        exp_type = body.exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_fun (l, Some default, spat, sexp) ->
      assert(is_optional l); (* default allowed only with optional argument *)
      let open Ast_helper in
      let default_loc = default.pexp_loc in
      let scases = [
        Exp.case
          (Pat.construct ~loc:default_loc
             (mknoloc (Longident.(Ldot (Lident "*predef*", "Some"))))
             (Some (Pat.var ~loc:default_loc (mknoloc "*sth*"))))
          (Exp.ident ~loc:default_loc (mknoloc (Longident.Lident "*sth*")));

        Exp.case
          (Pat.construct ~loc:default_loc
             (mknoloc (Longident.(Ldot (Lident "*predef*", "None"))))
             None)
          default;
       ]
      in
      let smatch =
        Exp.match_ ~loc (Exp.ident ~loc (mknoloc (Longident.Lident "*opt*")))
          scases
      in
      let sfun =
        Exp.fun_ ~loc
          l None
          (Pat.var ~loc (mknoloc "*opt*"))
          (Exp.let_ ~loc Nonrecursive ~attrs:[mknoloc "#default",PStr []]
             [Vb.mk spat smatch] sexp)
      in
      type_expect ?in_function env sfun ty_expected eff_expected
        (* TODO: keep attributes, call type_function directly *)
  | Pexp_fun (l, None, spat, sexp) ->
      type_function ?in_function loc sexp.pexp_attributes env ty_expected
        l [{pc_lhs=spat; pc_guard=None; pc_rhs=sexp}]
  | Pexp_function caselist ->
      type_function ?in_function
        loc sexp.pexp_attributes env ty_expected "" caselist
  | Pexp_apply(sfunct, sargs) ->
      if sargs = [] then
        Syntaxerr.ill_formed_ast loc "Function application with no argument.";
      begin_def (); (* one more level for non-returning functions *)
      if !Clflags.principal then begin_def ();
      let funct = type_exp env sfunct eff_expected in
      if !Clflags.principal then begin
          end_def ();
          generalize_structure funct.exp_type
        end;
      let rec lower_args seen ty_fun =
        let ty = expand_head env ty_fun in
        if List.memq ty seen then () else
        match ty.desc with
          Tarrow (l, ty_arg, ty_eff, ty_fun, com) ->
            (try
               unify_var env (newvar Stype) ty_arg
             with Unify _ -> assert false);
            lower_args (ty::seen) ty_fun
        | _ -> ()
      in
      let ty = instance env funct.exp_type in
      end_def ();
      wrap_trace_gadt_instances env (lower_args []) ty;
      begin_def ();
      let (args, ty_res) = type_application loc env funct sargs eff_expected in
      end_def ();
      unify_var env (newvar Stype) funct.exp_type;
      rue {
        exp_desc = Texp_apply(funct, args);
        exp_loc = loc; exp_extra = [];
        exp_type = ty_res;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_match(sarg, caselist) ->
      let eff = newvar Seffect in
      begin_def ();
      let arg = type_exp env sarg eff in
      end_def ();
      if is_nonexpansive arg then generalize arg.exp_type
      else generalize_expansive env arg.exp_type;
      close_effects_covariant env arg.exp_type;
      check_value_case loc env caselist;
      let cases, partial, handled =
        type_cases env ~allow_exn:true arg.exp_type
          eff_expected ty_expected loc caselist
      in
      let outer_eff = newvar Seffect in
      let inner_eff =
        List.fold_right
          (fun p ty -> newty (Teffect(p, ty)))
          handled outer_eff
      in
      unify_exp_effects arg.exp_loc env eff inner_eff;
      unify_exp_effects loc env outer_eff eff_expected;
      re {
        exp_desc = Texp_match(arg, cases, partial);
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_try(sbody, caselist) ->
      let eff = newvar Seffect in
      let body = type_expect env sbody ty_expected eff in
      let caselist = make_exception_default caselist in
      let cases, _, handled =
        type_cases env ~allow_exn:true (newvar Stype)
          eff_expected ty_expected loc caselist
      in
      let outer_eff = newvar Seffect in
      let inner_eff =
        List.fold_right
          (fun p ty -> newty (Teffect(p, ty)))
          handled outer_eff
      in
      unify_exp_effects body.exp_loc env eff inner_eff;
      unify_exp_effects loc env outer_eff eff_expected;
      re {
        exp_desc = Texp_try(body, cases);
        exp_loc = loc; exp_extra = [];
        exp_type = body.exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_tuple sexpl ->
      if List.length sexpl < 2 then
        Syntaxerr.ill_formed_ast loc "Tuples must have at least 2 components.";
      let subtypes = List.map (fun _ -> newgenvar Stype) sexpl in
      let to_unify = newgenty (Ttuple subtypes) in
      unify_exp_types loc env to_unify ty_expected;
      let expl =
        List.map2
          (fun body ty -> type_expect env body ty eff_expected)
          sexpl subtypes
      in
      re {
        exp_desc = Texp_tuple expl;
        exp_loc = loc; exp_extra = [];
        (* Keep sharing *)
        exp_type = newty (Ttuple (List.map (fun e -> e.exp_type) expl));
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_construct(lid, sarg) ->
      type_construct env loc lid sarg ty_expected
        eff_expected sexp.pexp_attributes
  | Pexp_variant(l, sarg) ->
      (* Keep sharing *)
      let ty_expected0 = instance env ty_expected in
      begin try match
        sarg, expand_head env ty_expected, expand_head env ty_expected0 with
      | Some sarg, {desc = Tvariant row}, {desc = Tvariant row0} ->
          let row = row_repr row in
          begin match row_field_repr (List.assoc l row.row_fields),
          row_field_repr (List.assoc l row0.row_fields) with
            Rpresent (Some ty), Rpresent (Some ty0) ->
              let arg = type_argument env sarg ty ty0 eff_expected in
              re { exp_desc = Texp_variant(l, Some arg);
                   exp_loc = loc; exp_extra = [];
                   exp_type = ty_expected0;
                   exp_attributes = sexp.pexp_attributes;
                   exp_env = env }
          | _ -> raise Not_found
          end
      | _ -> raise Not_found
      with Not_found ->
        let arg =
          may_map
            (fun sexp -> type_exp env sexp eff_expected)
            sarg
        in
        let arg_type = may_map (fun arg -> arg.exp_type) arg in
        rue {
          exp_desc = Texp_variant(l, arg);
          exp_loc = loc; exp_extra = [];
          exp_type= newty (Tvariant{row_fields = [l, Rpresent arg_type];
                                    row_more = newvar Stype;
                                    row_bound = ();
                                    row_closed = false;
                                    row_fixed = false;
                                    row_name = None});
          exp_attributes = sexp.pexp_attributes;
          exp_env = env }
      end
  | Pexp_record(lid_sexp_list, opt_sexp) ->
      if lid_sexp_list = [] then
        Syntaxerr.ill_formed_ast loc "Records cannot be empty.";
      let opt_exp =
        match opt_sexp with
          None -> None
        | Some sexp ->
            if !Clflags.principal then begin_def ();
            let exp = type_exp env sexp eff_expected in
            if !Clflags.principal then begin
              end_def ();
              generalize_structure exp.exp_type
            end;
            Some exp
      in
      let ty_record, opath =
        let get_path ty =
          try
            let (p0, p,_) = extract_concrete_record env ty in
            (* XXX level may be wrong *)
            Some (p0, p, ty.level = generic_level || not !Clflags.principal)
          with Not_found -> None
        in
        match get_path ty_expected with
          None ->
            begin match opt_exp with
            | None -> newvar Stype, None
            | Some exp ->
                match get_path exp.exp_type with
                  None -> newvar Stype, None
                | Some (_, p', _) as op ->
                    let decl = Env.find_type p' env in
                    begin_def ();
                    let params = instance_list env decl.type_params in
                    let ty = newconstr p' params decl.type_sort in
                    end_def ();
                    generalize_structure ty;
                    ty, op
            end
        | op -> ty_expected, op
      in
      let closed = (opt_sexp = None) in
      let lbl_exp_list =
        wrap_disambiguate "This record expression is expected to have" ty_record
          (type_label_a_list loc closed env
             (type_label_exp true env loc ty_record eff_expected)
             opath)
          lid_sexp_list
      in
      unify_exp_types loc env ty_record (instance env ty_expected);

      (* type_label_a_list returns a list of labels sorted by lbl_pos *)
      (* note: check_duplicates would better be implemented in
         type_label_a_list directly *)
      let rec check_duplicates = function
        | (_, lbl1, _) :: (_, lbl2, _) :: _ when lbl1.lbl_pos = lbl2.lbl_pos ->
          raise(Error(loc, env, Label_multiply_defined lbl1.lbl_name))
        | _ :: rem ->
            check_duplicates rem
        | [] -> ()
      in
      check_duplicates lbl_exp_list;
      let opt_exp =
        match opt_exp, lbl_exp_list with
          None, _ -> None
        | Some exp, (lid, lbl, lbl_exp) :: _ ->
            let ty_exp = instance env exp.exp_type in
            let unify_kept lbl =
              (* do not connect overridden labels *)
              if List.for_all
                  (fun (_, lbl',_) -> lbl'.lbl_pos <> lbl.lbl_pos)
                  lbl_exp_list
              then begin
                let _, ty_arg1, ty_res1 = instance_label false lbl
                and _, ty_arg2, ty_res2 = instance_label false lbl in
                unify env ty_arg1 ty_arg2;
                unify env (instance env ty_expected) ty_res2;
                unify_exp_types exp.exp_loc env ty_exp ty_res1;
              end in
            Array.iter unify_kept lbl.lbl_all;
            Some {exp with exp_type = ty_exp}
        | _ -> assert false
      in
      let num_fields =
        match lbl_exp_list with [] -> assert false
        | (_, lbl,_)::_ -> Array.length lbl.lbl_all in
      if opt_sexp = None && List.length lid_sexp_list <> num_fields then begin
        let present_indices =
          List.map (fun (_, lbl, _) -> lbl.lbl_pos) lbl_exp_list in
        let label_names = extract_label_names sexp env ty_expected in
        let rec missing_labels n = function
            [] -> []
          | lbl :: rem ->
              if List.mem n present_indices then missing_labels (n + 1) rem
              else lbl :: missing_labels (n + 1) rem
        in
        let missing = missing_labels 0 label_names in
        raise(Error(loc, env, Label_missing missing))
      end
      else if opt_sexp <> None && List.length lid_sexp_list = num_fields then
        Location.prerr_warning loc Warnings.Useless_record_with;
      let mut =
        match lbl_exp_list with
        | [] -> assert false
        | (_, lbl, _) :: _ ->
            Array.fold_left
              (fun acc lbl -> acc || lbl.lbl_mut = Mutable)
              false lbl.lbl_all
      in
      if mut then begin
        let eff = instance_def (Predef.effect_io (newvar Seffect)) in
        unify_exp_effects loc env eff eff_expected
      end;
      re {
        exp_desc = Texp_record(lbl_exp_list, opt_exp);
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_field(srecord, lid) ->
      let (record, label, _) =
        type_label_access env loc srecord lid eff_expected
      in
      let (_, ty_arg, ty_res) = instance_label false label in
      unify_exp env record ty_res;
      let eff =
        if label.lbl_mut = Mutable then
          instance_def (Predef.effect_io (newvar Seffect))
        else
          newvar Seffect
      in
      rufe eff {
        exp_desc = Texp_field(record, lid, label);
        exp_loc = loc; exp_extra = [];
        exp_type = ty_arg;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_setfield(srecord, lid, snewval) ->
      let (record, label, opath) =
        type_label_access env loc srecord lid eff_expected
      in
      let ty_record = if opath = None then newvar Stype else record.exp_type in
      let (label_loc, label, newval) =
        type_label_exp false env loc ty_record eff_expected
          (lid, label, snewval)
      in
      unify_exp env record ty_record;
      if label.lbl_mut = Immutable then
        raise(Error(loc, env, Label_not_mutable lid.txt));
      let eff = instance_def (Predef.effect_io (newvar Seffect)) in
      rufe eff {
        exp_desc = Texp_setfield(record, label_loc, label, newval);
        exp_loc = loc; exp_extra = [];
        exp_type = instance_def Predef.type_unit;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_array(sargl) ->
      let ty = newgenvar Stype in
      let to_unify = Predef.type_array ty in
      unify_exp_types loc env to_unify ty_expected;
      let argl =
        List.map (fun sarg -> type_expect env sarg ty eff_expected) sargl
      in
      let eff = instance_def (Predef.effect_io (newvar Seffect)) in
      unify_exp_effects loc env eff eff_expected;
      re {
        exp_desc = Texp_array argl;
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_ifthenelse(scond, sifso, sifnot) ->
      let cond = type_expect env scond Predef.type_bool eff_expected in
      begin match sifnot with
        None ->
          let ifso = type_expect env sifso Predef.type_unit eff_expected in
          rue {
            exp_desc = Texp_ifthenelse(cond, ifso, None);
            exp_loc = loc; exp_extra = [];
            exp_type = ifso.exp_type;
            exp_attributes = sexp.pexp_attributes;
            exp_env = env }
      | Some sifnot ->
          let ifso = type_expect env sifso ty_expected eff_expected in
          let ifnot = type_expect env sifnot ty_expected eff_expected in
          (* Keep sharing *)
          unify_exp env ifnot ifso.exp_type;
          re {
            exp_desc = Texp_ifthenelse(cond, ifso, Some ifnot);
            exp_loc = loc; exp_extra = [];
            exp_type = ifso.exp_type;
            exp_attributes = sexp.pexp_attributes;
            exp_env = env }
      end
  | Pexp_sequence(sexp1, sexp2) ->
      let exp1 = type_statement env sexp1 eff_expected in
      let exp2 = type_expect env sexp2 ty_expected eff_expected in
      re {
        exp_desc = Texp_sequence(exp1, exp2);
        exp_loc = loc; exp_extra = [];
        exp_type = exp2.exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_while(scond, sbody) ->
      let cond = type_expect env scond Predef.type_bool eff_expected in
      let body = type_statement env sbody eff_expected in
      rue {
        exp_desc = Texp_while(cond, body);
        exp_loc = loc; exp_extra = [];
        exp_type = instance_def Predef.type_unit;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_for(param, slow, shigh, dir, sbody) ->
      let low = type_expect env slow Predef.type_int eff_expected in
      let high = type_expect env shigh Predef.type_int eff_expected in
      let id, new_env =
        match param.ppat_desc with
        | Ppat_any -> Ident.create "_for", env
        | Ppat_var {txt} ->
            Env.enter_value txt {val_type = instance_def Predef.type_int;
                                 val_attributes = [];
                                 val_kind = Val_reg; Types.val_loc = loc; } env
              ~check:(fun s -> Warnings.Unused_for_index s)
        | _ ->
            raise (Error (param.ppat_loc, env, Invalid_for_loop_index))
      in
      let body = type_statement new_env sbody eff_expected in
      rue {
        exp_desc = Texp_for(id, param, low, high, dir, body);
        exp_loc = loc; exp_extra = [];
        exp_type = instance_def Predef.type_unit;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_constraint (sarg, sty) ->
      let separate = true in (* always separate, 1% slowdown for lablgtk *)
      if separate then begin_def ();
      let cty = Typetexp.transl_simple_type env false (Some Stype) sty in
      let ty = cty.ctyp_type in
      let (arg, ty') =
        if separate then begin
          end_def ();
          generalize_structure ty;
          (type_argument env sarg ty (instance env ty) eff_expected,
           instance env ty)
        end else
          (type_argument env sarg ty ty eff_expected, ty)
      in
      rue {
        exp_desc = arg.exp_desc;
        exp_loc = arg.exp_loc;
        exp_type = ty';
        exp_attributes = arg.exp_attributes;
        exp_env = env;
        exp_extra =
          (Texp_constraint cty, loc, sexp.pexp_attributes) :: arg.exp_extra;
      }
  | Pexp_coerce(sarg, sty, sty') ->
      let separate = true (* always separate, 1% slowdown for lablgtk *)
        (* !Clflags.principal || Env.has_local_constraints env *) in
      let (arg, ty',cty,cty') =
        match sty with
        | None ->
            let (cty', force) =
              Typetexp.transl_simple_type_delayed env (Some Stype) sty'
            in
            let ty' = cty'.ctyp_type in
            if separate then begin_def ();
            let arg = type_exp env sarg eff_expected in
            let gen =
              if separate then begin
                end_def ();
                let tv = newvar Stype in
                let gen = generalizable tv.level arg.exp_type in
                unify_var env tv arg.exp_type;
                gen
              end else true
            in
            begin match arg.exp_desc, !self_coercion, (repr ty').desc with
              Texp_ident(_, _, {val_kind=Val_self _}), (path,r) :: _,
              Tconstr(path',_,_,_) when Path.same path path' ->
                (* prerr_endline "self coercion"; *)
                r := loc :: !r;
                force ()
            | _ when free_variables ~env arg.exp_type = []
                  && free_variables ~env ty' = [] ->
                if not gen && (* first try a single coercion *)
                  let snap = snapshot () in
                  let ty, b = enlarge_type env ty' in
                  try
                    force (); Ctype.unify env arg.exp_type ty; true
                  with Unify _ ->
                    backtrack snap; false
                then ()
                else begin try
                  let force' = subtype env arg.exp_type ty' in
                  force (); force' ();
                  if not gen then
                    Location.prerr_warning loc
                      (Warnings.Not_principal "this ground coercion");
                with Subtype (tr1, tr2) ->
                  (* prerr_endline "coercion failed"; *)
                  raise(Error(loc, env, Not_subtype(tr1, tr2)))
                end;
            | _ ->
                let ty, b = enlarge_type env ty' in
                force ();
                begin try Ctype.unify env arg.exp_type ty with Unify trace ->
                  raise(Error(sarg.pexp_loc, env,
                        Coercion_failure(ty', full_expand env ty', trace, b)))
                end
            end;
            (arg, ty', None, cty')
        | Some sty ->
            if separate then begin_def ();
            let (cty, force) =
              Typetexp.transl_simple_type_delayed env (Some Stype) sty
            and (cty', force') =
              Typetexp.transl_simple_type_delayed env (Some Stype) sty'
            in
            let ty = cty.ctyp_type in
            let ty' = cty'.ctyp_type in
            begin try
              let force'' = subtype env ty ty' in
              force (); force' (); force'' ()
            with Subtype (tr1, tr2) ->
              raise(Error(loc, env, Not_subtype(tr1, tr2)))
            end;
            if separate then begin
              end_def ();
              generalize_structure ty;
              generalize_structure ty';
              (type_argument env sarg ty (instance env ty) eff_expected,
               instance env ty', Some cty, cty')
            end else
              (type_argument env sarg ty ty eff_expected,
               ty', Some cty, cty')
      in
      rue {
        exp_desc = arg.exp_desc;
        exp_loc = arg.exp_loc;
        exp_type = ty';
        exp_attributes = arg.exp_attributes;
        exp_env = env;
        exp_extra = (Texp_coerce (cty, cty'), loc, sexp.pexp_attributes) ::
                       arg.exp_extra;
      }
  | Pexp_send (e, met) ->
      if !Clflags.principal then begin_def ();
      let obj = type_exp env e eff_expected in
      begin try
        let (meth, exp, typ) =
          match obj.exp_desc with
            Texp_ident(path, _, {val_kind = Val_self (meths, _, _, privty)}) ->
              let (id, typ) =
                filter_self_method env met Private meths privty
              in
              if is_Tvar (repr typ) then
                Location.prerr_warning loc
                  (Warnings.Undeclared_virtual_method met);
              (Tmeth_val id, None, typ)
          | Texp_ident(path, lid, {val_kind = Val_anc (methods, cl_num)}) ->
              let method_id =
                begin try List.assoc met methods with Not_found ->
                  raise(Error(e.pexp_loc, env, Undefined_inherited_method met))
                end
              in
              begin match
                Env.lookup_value (Longident.Lident ("selfpat-" ^ cl_num)) env,
                Env.lookup_value (Longident.Lident ("self-" ^cl_num)) env
              with
                (_, ({val_kind = Val_self (meths, _, _, privty)} as desc)),
                (path, _) ->
                  let (_, typ) =
                    filter_self_method env met Private meths privty
                  in
                  let method_type = newvar Stype in
                  let (obj_ty, eff_ty, res_ty) =
                    filter_arrow env method_type ""
                  in
                  unify env obj_ty desc.val_type;
                  unify env res_ty (instance env typ);
                  let exp =
                    Texp_apply({exp_desc =
                                Texp_ident(Path.Pident method_id, lid,
                                           {val_type = method_type;
                                            val_kind = Val_reg;
                                            val_attributes = [];
                                            Types.val_loc = Location.none});
                                exp_loc = loc; exp_extra = [];
                                exp_type = method_type;
                                exp_attributes = []; (* check *)
                                exp_env = env},
                          ["",
                            Some {exp_desc = Texp_ident(path, lid, desc);
                                  exp_loc = obj.exp_loc; exp_extra = [];
                                  exp_type = desc.val_type;
                                  exp_attributes = []; (* check *)
                                  exp_env = env},
                               Required])
                  in
                  (Tmeth_name met, Some (re {exp_desc = exp;
                                             exp_loc = loc; exp_extra = [];
                                             exp_type = typ;
                                             exp_attributes = []; (* check *)
                                             exp_env = env}), typ)
              |  _ ->
                  assert false
              end
          | _ ->
              (Tmeth_name met, None,
               filter_method env met Public obj.exp_type)
        in
        if !Clflags.principal then begin
          end_def ();
          generalize_structure typ;
        end;
        let typ =
          match repr typ with
            {desc = Tpoly (ty, [])} ->
              instance env ty
          | {desc = Tpoly (ty, tl); level = l} ->
              if !Clflags.principal && l <> generic_level then
                Location.prerr_warning loc
                  (Warnings.Not_principal "this use of a polymorphic method");
              snd (instance_poly false tl ty)
          | {desc = Tvar(_, Stype)} as ty ->
              let ty' = newvar Stype in
              unify env (instance_def ty) (newty(Tpoly(ty',[])));
              (* if not !Clflags.nolabels then
                 Location.prerr_warning loc (Warnings.Unknown_method met); *)
              ty'
          | _ ->
              assert false
        in
        let eff = instance_def (Predef.effect_io (newvar Seffect)) in
        rufe eff {
          exp_desc = Texp_send(obj, meth, exp);
          exp_loc = loc; exp_extra = [];
          exp_type = typ;
          exp_attributes = sexp.pexp_attributes;
          exp_env = env }
      with Unify _ ->
        raise(Error(e.pexp_loc, env, Undefined_method (obj.exp_type, met)))
      end
  | Pexp_perform(lid, sarg) ->
      type_perform env loc lid sarg ty_expected
        eff_expected sexp.pexp_attributes
  | Pexp_new cl ->
      let (cl_path, cl_decl) = Typetexp.find_class env loc cl.txt in
      begin match cl_decl.cty_new with
          None ->
            raise(Error(loc, env, Virtual_class cl.txt))
        | Some ty ->
            let eff = instance_def (Predef.effect_io (newvar Seffect)) in
            rufe eff {
              exp_desc = Texp_new (cl_path, cl, cl_decl);
              exp_loc = loc; exp_extra = [];
              exp_type = instance_def ty;
              exp_attributes = sexp.pexp_attributes;
              exp_env = env }
        end
  | Pexp_setinstvar (lab, snewval) ->
      begin try
        let (path, desc) = Env.lookup_value (Longident.Lident lab.txt) env in
        match desc.val_kind with
          Val_ivar (Mutable, cl_num) ->
            let newval =
              type_expect env snewval (instance env desc.val_type) eff_expected
            in
            let (path_self, _) =
              Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
            in
            let eff = instance_def (Predef.effect_io (newvar Seffect)) in
            rufe eff {
              exp_desc = Texp_setinstvar(path_self, path, lab, newval);
              exp_loc = loc; exp_extra = [];
              exp_type = instance_def Predef.type_unit;
              exp_attributes = sexp.pexp_attributes;
              exp_env = env }
        | Val_ivar _ ->
            raise(Error(loc, env, Instance_variable_not_mutable(true,lab.txt)))
        | _ ->
            raise(Error(loc, env, Instance_variable_not_mutable(false,lab.txt)))
      with
        Not_found ->
          raise(Error(loc, env, Unbound_instance_variable lab.txt))
      end
  | Pexp_override lst ->
      let _ =
       List.fold_right
        (fun (lab, _) l ->
           if List.exists (fun l -> l.txt = lab.txt) l then
             raise(Error(loc, env,
                         Value_multiply_overridden lab.txt));
           lab::l)
        lst
        [] in
      begin match
        try
          Env.lookup_value (Longident.Lident "selfpat-*") env,
          Env.lookup_value (Longident.Lident "self-*") env
        with Not_found ->
          raise(Error(loc, env, Outside_class))
      with
        (_, {val_type = self_ty; val_kind = Val_self (_, vars, _, _)}),
        (path_self, _) ->
          let type_override (lab, snewval) =
            begin try
              let (id, _, _, ty) = Vars.find lab.txt !vars in
              let exp =
                type_expect env snewval (instance env ty) eff_expected
              in
              (Path.Pident id, lab, exp)
            with
              Not_found ->
                raise(Error(loc, env, Unbound_instance_variable lab.txt))
            end
          in
          let modifs = List.map type_override lst in
          let eff = instance_def (Predef.effect_io (newvar Seffect)) in
          rufe eff {
            exp_desc = Texp_override(path_self, modifs);
            exp_loc = loc; exp_extra = [];
            exp_type = self_ty;
            exp_attributes = sexp.pexp_attributes;
            exp_env = env }
      | _ ->
          assert false
      end
  | Pexp_letmodule(name, smodl, sbody) ->
      let ty = newvar Stype in
      (* remember original level *)
      begin_def ();
      Ident.set_current_time ty.level;
      let context = Typetexp.narrow () in
      let modl = !type_module env smodl in
      let (id, new_env) = Env.enter_module name.txt modl.mod_type env in
      Ctype.init_def(Ident.current_time());
      Typetexp.widen context;
      let body = type_expect new_env sbody ty_expected eff_expected in
      (* go back to original level *)
      end_def ();
      (* Unification of body.exp_type with the fresh variable ty
         fails if and only if the prefix condition is violated,
         i.e. if generative types rooted at id show up in the
         type body.exp_type.  Thus, this unification enforces the
         scoping condition on "let module". *)
      begin try
        Ctype.unify_var new_env ty body.exp_type;
      with Unify _ ->
        raise(Error(loc, env, Scoping_let_module(name.txt, body.exp_type)))
      end;
      let eff = instance_def (Predef.effect_io (newvar Seffect)) in
      unify_exp_effects loc env eff eff_expected;
      re {
        exp_desc = Texp_letmodule(id, name, modl, body);
        exp_loc = loc; exp_extra = [];
        exp_type = ty;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_assert (e) ->
      let cond = type_expect env e Predef.type_bool eff_expected in
      let exp_type =
        match cond.exp_desc with
        | Texp_construct(_, {cstr_name="false"}, _) ->
            instance env ty_expected
        | _ ->
            instance_def Predef.type_unit
      in
      rue {
        exp_desc = Texp_assert cond;
        exp_loc = loc; exp_extra = [];
        exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env;
      }
  | Pexp_lazy e ->
      let ty = newgenvar Stype in
      let to_unify = Predef.type_lazy_t ty in
      unify_exp_types loc env to_unify ty_expected;
      let eff = Predef.effect_io (newgenty Tenil) in
      let arg = type_expect env e ty eff in
      re {
        exp_desc = Texp_lazy arg;
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env;
      }
  | Pexp_object s ->
      let desc, sign, meths = !type_object env loc s in
      let eff = instance_def (Predef.effect_io (newvar Seffect)) in
      rufe eff {
        exp_desc = Texp_object (desc, (*sign,*) meths);
        exp_loc = loc; exp_extra = [];
        exp_type = sign.csig_self;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env;
      }
  | Pexp_poly(sbody, sty) ->
      if !Clflags.principal then begin_def ();
      let ty, cty =
        match sty with None -> repr ty_expected, None
        | Some sty ->
            let sty = Ast_helper.Typ.force_poly sty in
            let cty = Typetexp.transl_simple_type env false (Some Stype) sty in
            repr cty.ctyp_type, Some cty
      in
      if !Clflags.principal then begin
        end_def ();
        generalize_structure ty
      end;
      if sty <> None then
        unify_exp_types loc env (instance env ty) (instance env ty_expected);
      let exp =
        match (expand_head env ty).desc with
          Tpoly (ty', []) ->
            let exp = type_expect env sbody ty' eff_expected in
            { exp with exp_type = instance env ty }
        | Tpoly (ty', tl) ->
            (* One more level to generalize locally *)
            begin_def ();
            if !Clflags.principal then begin_def ();
            let vars, ty'' = instance_poly true tl ty' in
            if !Clflags.principal then begin
              end_def ();
              generalize_structure ty''
            end;
            let exp = type_expect env sbody ty'' eff_expected in
            end_def ();
            check_univars env false "method" exp ty_expected vars;
            { exp with exp_type = instance env ty }
        | Tvar _ ->
            let exp = type_exp env sbody eff_expected in
            let exp = {exp with exp_type = newty (Tpoly (exp.exp_type, []))} in
            unify_exp env exp ty;
            exp
        | _ -> assert false
      in
      re { exp with exp_extra =
             (Texp_poly cty, loc, sexp.pexp_attributes) :: exp.exp_extra }
  | Pexp_newtype(name, ssort, sbody) ->
      let sort = Typetexp.transl_sort ssort in
      let ty = newvar sort in
      (* remember original level *)
      begin_def ();
      (* Create a fake abstract type declaration for name. *)
      let level = get_current_level () in
      let decl = {
        type_params = [];
        type_arity = 0;
        type_sort = sort;
        type_kind = Type_abstract;
        type_private = Public;
        type_manifest = None;
        type_variance = [];
        type_newtype_level = Some (level, level);
        type_loc = loc;
        type_attributes = [];
      }
      in
      Ident.set_current_time ty.level;
      let (id, new_env) = Env.enter_type name decl env in
      Ctype.init_def(Ident.current_time());

      let body = type_exp new_env sbody eff_expected in
      (* Replace every instance of this type constructor in the resulting
         type. *)
      let seen = Hashtbl.create 8 in
      let rec replace t =
        if Hashtbl.mem seen t.id then ()
        else begin
          Hashtbl.add seen t.id ();
          match t.desc with
          | Tconstr (Path.Pident id', _, _, _) when id == id' -> link_type t ty
          | _ -> Btype.iter_type_expr replace t
        end
      in
      let ety = Subst.type_expr Subst.identity body.exp_type in
      replace ety;
      (* back to original level *)
      end_def ();
      (* lower the levels of the result type *)
      (* unify_var env ty ety; *)

      (* non-expansive if the body is non-expansive, so we don't introduce
         any new extra node in the typed AST. *)
      rue { body with exp_loc = loc; exp_type = ety;
            exp_extra =
            (Texp_newtype (name, ssort), loc, sexp.pexp_attributes) :: body.exp_extra }
  | Pexp_pack m ->
      let (p, nl, tl) =
        match Ctype.expand_head env (instance env ty_expected) with
          {desc = Tpackage (p, nl, tl)} ->
            if !Clflags.principal &&
              (Ctype.expand_head env ty_expected).level < Btype.generic_level
            then
              Location.prerr_warning loc
                (Warnings.Not_principal "this module packing");
            (p, nl, tl)
        | {desc = Tvar _} ->
            raise (Error (loc, env, Cannot_infer_signature))
        | _ ->
            raise (Error (loc, env, Not_a_packed_module ty_expected))
      in
      let (modl, tl') = !type_package env m p nl tl in
      rue {
        exp_desc = Texp_pack modl;
        exp_loc = loc; exp_extra = [];
        exp_type = newty (Tpackage (p, nl, tl'));
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_open (ovf, lid, e) ->
      let (path, newenv) = !type_open ovf env sexp.pexp_loc lid in
      let exp = type_expect newenv e ty_expected eff_expected in
      { exp with
        exp_extra = (Texp_open (ovf, path, lid, newenv), loc,
                     sexp.pexp_attributes) ::
                      exp.exp_extra;
      }
  | Pexp_extension ext ->
      raise (Error_forward (Typetexp.error_of_extension ext))

and type_function ?in_function loc attrs env ty_expected l caselist =
  let (loc_fun, ty_fun) =
    match in_function with Some p -> p
    | None -> (loc, instance env ty_expected)
  in
  let separate = !Clflags.principal || Env.has_local_constraints env in
  if separate then begin_def ();
  let (ty_arg, ty_eff, ty_res) =
    try filter_arrow env (instance env ty_expected) l
    with Unify _ ->
      match expand_head env ty_expected with
        {desc = Tarrow _} as ty ->
          raise(Error(loc, env, Abstract_wrong_label(l, ty)))
      | _ ->
          raise(Error(loc_fun, env,
                      Too_many_arguments (in_function <> None, ty_fun)))
  in
  let ty_arg =
    if is_optional l then
      let tv = newvar Stype in
      begin
        try unify env ty_arg (type_option tv)
        with Unify _ -> assert false
      end;
      type_option tv
    else ty_arg
  in
  if separate then begin
    end_def ();
    generalize_structure ty_arg;
    generalize_structure ty_res
  end;
  let cases, partial, _ =
    type_cases ~allow_exn:false ~in_function:(loc_fun,ty_fun) env
      ty_arg ty_eff ty_res loc caselist in
  let not_function ty =
    let ls, tvar = list_labels env ty in
    ls = [] && not tvar
  in
  if is_optional l && not_function ty_res then
    Location.prerr_warning (List.hd cases).c_lhs.pat_loc
      Warnings.Unerasable_optional_argument;
  re {
  exp_desc = Texp_function(l,cases, partial);
    exp_loc = loc; exp_extra = [];
    exp_type = instance env (newgenty (Tarrow(l, ty_arg, ty_eff, ty_res, Cok)));
    exp_attributes = attrs;
    exp_env = env }


and type_label_access env loc srecord lid eff_expected =
  if !Clflags.principal then begin_def ();
  let record = type_exp env srecord eff_expected in
  if !Clflags.principal then begin
    end_def ();
    generalize_structure record.exp_type
  end;
  let ty_exp = record.exp_type in
  let opath =
    try
      let (p0, p,_) = extract_concrete_record env ty_exp in
      Some(p0, p, ty_exp.level = generic_level || not !Clflags.principal)
    with Not_found -> None
  in
  let labels = Typetexp.find_all_labels env lid.loc lid.txt in
  let label =
    wrap_disambiguate "This expression has" ty_exp
      (Label.disambiguate lid env opath) labels in
  (record, label, opath)

(* Typing format strings for printing or reading.
   These formats are used by functions in modules Printf, Format, and Scanf.
   (Handling of * modifiers contributed by Thorsten Ohl.) *)

and type_format loc str env =
  let loc = {loc with Location.loc_ghost = true} in
  try
    CamlinternalFormatBasics.(CamlinternalFormat.(
      let mk_exp_loc pexp_desc = {
        pexp_desc = pexp_desc;
        pexp_loc = loc;
        pexp_attributes = [];
      } and mk_lid_loc lid = {
        txt = lid;
        loc = loc;
      } in
      let mk_constr name args =
        let lid = Longident.(Ldot(Lident "CamlinternalFormatBasics", name)) in
        let arg = match args with
          | []          -> None
          | [ e ]       -> Some e
          | _ :: _ :: _ -> Some (mk_exp_loc (Pexp_tuple args)) in
        mk_exp_loc (Pexp_construct (mk_lid_loc lid, arg)) in
      let mk_cst cst = mk_exp_loc (Pexp_constant cst) in
      let mk_int n = mk_cst (Const_int n)
      and mk_string str = mk_cst (Const_string (str, None))
      and mk_char chr = mk_cst (Const_char chr) in
      let rec mk_formatting_lit fmting = match fmting with
        | Close_box ->
          mk_constr "Close_box" []
        | Close_tag ->
          mk_constr "Close_tag" []
        | Break (org, ns, ni) ->
          mk_constr "Break" [ mk_string org; mk_int ns; mk_int ni ]
        | FFlush ->
          mk_constr "FFlush" []
        | Force_newline ->
          mk_constr "Force_newline" []
        | Flush_newline ->
          mk_constr "Flush_newline" []
        | Magic_size (org, sz) ->
          mk_constr "Magic_size" [ mk_string org; mk_int sz ]
        | Escaped_at ->
          mk_constr "Escaped_at" []
        | Escaped_percent ->
          mk_constr "Escaped_percent" []
        | Scan_indic c ->
          mk_constr "Scan_indic" [ mk_char c ]
      and mk_formatting_gen : type a b c d e f .
          (a, b, c, d, e, f) formatting_gen -> Parsetree.expression =
        fun fmting -> match fmting with
        | Open_tag (Format (fmt', str')) ->
          mk_constr "Open_tag" [ mk_format fmt' str' ]
        | Open_box (Format (fmt', str')) ->
          mk_constr "Open_box" [ mk_format fmt' str' ]
      and mk_format : type a b c d e f .
          (a, b, c, d, e, f) CamlinternalFormatBasics.fmt -> string ->
          Parsetree.expression = fun fmt str ->
        mk_constr "Format" [ mk_fmt fmt; mk_string str ]
      and mk_side side = match side with
        | Left  -> mk_constr "Left"  []
        | Right -> mk_constr "Right" []
        | Zeros -> mk_constr "Zeros" []
      and mk_iconv iconv = match iconv with
        | Int_d  -> mk_constr "Int_d"  [] | Int_pd -> mk_constr "Int_pd" []
        | Int_sd -> mk_constr "Int_sd" [] | Int_i  -> mk_constr "Int_i"  []
        | Int_pi -> mk_constr "Int_pi" [] | Int_si -> mk_constr "Int_si" []
        | Int_x  -> mk_constr "Int_x"  [] | Int_Cx -> mk_constr "Int_Cx" []
        | Int_X  -> mk_constr "Int_X"  [] | Int_CX -> mk_constr "Int_CX" []
        | Int_o  -> mk_constr "Int_o"  [] | Int_Co -> mk_constr "Int_Co" []
        | Int_u  -> mk_constr "Int_u"  []
      and mk_fconv fconv = match fconv with
        | Float_f  -> mk_constr "Float_f"  []
        | Float_pf -> mk_constr "Float_pf" []
        | Float_sf -> mk_constr "Float_sf" []
        | Float_e  -> mk_constr "Float_e"  []
        | Float_pe -> mk_constr "Float_pe" []
        | Float_se -> mk_constr "Float_se" []
        | Float_E  -> mk_constr "Float_E"  []
        | Float_pE -> mk_constr "Float_pE" []
        | Float_sE -> mk_constr "Float_sE" []
        | Float_g  -> mk_constr "Float_g"  []
        | Float_pg -> mk_constr "Float_pg" []
        | Float_sg -> mk_constr "Float_sg" []
        | Float_G  -> mk_constr "Float_G"  []
        | Float_pG -> mk_constr "Float_pG" []
        | Float_sG -> mk_constr "Float_sG" []
        | Float_F  -> mk_constr "Float_F"  []
      and mk_counter cnt = match cnt with
        | Line_counter  -> mk_constr "Line_counter"  []
        | Char_counter  -> mk_constr "Char_counter"  []
        | Token_counter -> mk_constr "Token_counter" []
      and mk_int_opt n_opt = match n_opt with
        | None ->
          let lid_loc = mk_lid_loc (Longident.Lident "None") in
          mk_exp_loc (Pexp_construct (lid_loc, None))
        | Some n ->
          let lid_loc = mk_lid_loc (Longident.Lident "Some") in
          mk_exp_loc (Pexp_construct (lid_loc, Some (mk_int n)))
      and mk_fmtty : type a b c d e f g h i j k l .
          (a, b, c, d, e, f, g, h, i, j, k, l) fmtty_rel -> Parsetree.expression =
      fun fmtty -> match fmtty with
        | Char_ty rest      -> mk_constr "Char_ty"      [ mk_fmtty rest ]
        | String_ty rest    -> mk_constr "String_ty"    [ mk_fmtty rest ]
        | Int_ty rest       -> mk_constr "Int_ty"       [ mk_fmtty rest ]
        | Int32_ty rest     -> mk_constr "Int32_ty"     [ mk_fmtty rest ]
        | Nativeint_ty rest -> mk_constr "Nativeint_ty" [ mk_fmtty rest ]
        | Int64_ty rest     -> mk_constr "Int64_ty"     [ mk_fmtty rest ]
        | Float_ty rest     -> mk_constr "Float_ty"     [ mk_fmtty rest ]
        | Bool_ty rest      -> mk_constr "Bool_ty"      [ mk_fmtty rest ]
        | Alpha_ty rest     -> mk_constr "Alpha_ty"     [ mk_fmtty rest ]
        | Theta_ty rest     -> mk_constr "Theta_ty"     [ mk_fmtty rest ]
        | Any_ty rest       -> mk_constr "Any_ty"       [ mk_fmtty rest ]
        | Reader_ty rest    -> mk_constr "Reader_ty"    [ mk_fmtty rest ]
        | Ignored_reader_ty rest ->
          mk_constr "Ignored_reader_ty" [ mk_fmtty rest ]
        | Format_arg_ty (sub_fmtty, rest) ->
          mk_constr "Format_arg_ty" [ mk_fmtty sub_fmtty; mk_fmtty rest ]
        | Format_subst_ty (sub_fmtty1, sub_fmtty2, rest) ->
          mk_constr "Format_subst_ty"
            [ mk_fmtty sub_fmtty1; mk_fmtty sub_fmtty2; mk_fmtty rest ]
        | End_of_fmtty -> mk_constr "End_of_fmtty" []
      and mk_ignored : type a b c d e f .
          (a, b, c, d, e, f) ignored -> Parsetree.expression =
      fun ign -> match ign with
        | Ignored_char ->
          mk_constr "Ignored_char" []
        | Ignored_caml_char ->
          mk_constr "Ignored_caml_char" []
        | Ignored_string pad_opt ->
          mk_constr "Ignored_string" [ mk_int_opt pad_opt ]
        | Ignored_caml_string pad_opt ->
          mk_constr "Ignored_caml_string" [ mk_int_opt pad_opt ]
        | Ignored_int (iconv, pad_opt) ->
          mk_constr "Ignored_int" [ mk_iconv iconv; mk_int_opt pad_opt ]
        | Ignored_int32 (iconv, pad_opt) ->
          mk_constr "Ignored_int32" [ mk_iconv iconv; mk_int_opt pad_opt ]
        | Ignored_nativeint (iconv, pad_opt) ->
          mk_constr "Ignored_nativeint" [ mk_iconv iconv; mk_int_opt pad_opt ]
        | Ignored_int64 (iconv, pad_opt) ->
          mk_constr "Ignored_int64" [ mk_iconv iconv; mk_int_opt pad_opt ]
        | Ignored_float (pad_opt, prec_opt) ->
          mk_constr "Ignored_float" [ mk_int_opt pad_opt; mk_int_opt prec_opt ]
        | Ignored_bool ->
          mk_constr "Ignored_bool" []
        | Ignored_format_arg (pad_opt, fmtty) ->
          mk_constr "Ignored_format_arg" [ mk_int_opt pad_opt; mk_fmtty fmtty ]
        | Ignored_format_subst (pad_opt, fmtty) ->
          mk_constr "Ignored_format_subst" [
            mk_int_opt pad_opt; mk_fmtty fmtty ]
        | Ignored_reader ->
          mk_constr "Ignored_reader" []
        | Ignored_scan_char_set (width_opt, char_set) ->
          mk_constr "Ignored_scan_char_set" [
            mk_int_opt width_opt; mk_string char_set ]
        | Ignored_scan_get_counter counter ->
          mk_constr "Ignored_scan_get_counter" [
            mk_counter counter
          ]
        | Ignored_scan_next_char ->
          mk_constr "Ignored_scan_next_char" []
      and mk_padding : type x y . (x, y) padding -> Parsetree.expression =
      fun pad -> match pad with
        | No_padding         -> mk_constr "No_padding" []
        | Lit_padding (s, w) -> mk_constr "Lit_padding" [ mk_side s; mk_int w ]
        | Arg_padding s      -> mk_constr "Arg_padding" [ mk_side s ]
      and mk_precision : type x y . (x, y) precision -> Parsetree.expression =
      fun prec -> match prec with
        | No_precision    -> mk_constr "No_precision" []
        | Lit_precision w -> mk_constr "Lit_precision" [ mk_int w ]
        | Arg_precision   -> mk_constr "Arg_precision" []
      and mk_fmt : type a b c d e f .
          (a, b, c, d, e, f) fmt -> Parsetree.expression =
      fun fmt -> match fmt with
        | Char rest ->
          mk_constr "Char" [ mk_fmt rest ]
        | Caml_char rest ->
          mk_constr "Caml_char" [ mk_fmt rest ]
        | String (pad, rest) ->
          mk_constr "String" [ mk_padding pad; mk_fmt rest ]
        | Caml_string (pad, rest) ->
          mk_constr "Caml_string" [ mk_padding pad; mk_fmt rest ]
        | Int (iconv, pad, prec, rest) ->
          mk_constr "Int" [
            mk_iconv iconv; mk_padding pad; mk_precision prec; mk_fmt rest ]
        | Int32 (iconv, pad, prec, rest) ->
          mk_constr "Int32" [
            mk_iconv iconv; mk_padding pad; mk_precision prec; mk_fmt rest ]
        | Nativeint (iconv, pad, prec, rest) ->
          mk_constr "Nativeint" [
            mk_iconv iconv; mk_padding pad; mk_precision prec; mk_fmt rest ]
        | Int64 (iconv, pad, prec, rest) ->
          mk_constr "Int64" [
            mk_iconv iconv; mk_padding pad; mk_precision prec; mk_fmt rest ]
        | Float (fconv, pad, prec, rest) ->
          mk_constr "Float" [
            mk_fconv fconv; mk_padding pad; mk_precision prec; mk_fmt rest ]
        | Bool rest ->
          mk_constr "Bool" [ mk_fmt rest ]
        | Flush rest ->
          mk_constr "Flush" [ mk_fmt rest ]
        | String_literal (s, rest) ->
          mk_constr "String_literal" [ mk_string s; mk_fmt rest ]
        | Char_literal (c, rest) ->
          mk_constr "Char_literal" [ mk_char c; mk_fmt rest ]
        | Format_arg (pad_opt, fmtty, rest) ->
          mk_constr "Format_arg" [
            mk_int_opt pad_opt; mk_fmtty fmtty; mk_fmt rest ]
        | Format_subst (pad_opt, fmtty, rest) ->
          mk_constr "Format_subst" [
            mk_int_opt pad_opt; mk_fmtty fmtty; mk_fmt rest ]
        | Alpha rest ->
          mk_constr "Alpha" [ mk_fmt rest ]
        | Theta rest ->
          mk_constr "Theta" [ mk_fmt rest ]
        | Formatting_lit (fmting, rest) ->
          mk_constr "Formatting_lit" [ mk_formatting_lit fmting; mk_fmt rest ]
        | Formatting_gen (fmting, rest) ->
          mk_constr "Formatting_gen" [ mk_formatting_gen fmting; mk_fmt rest ]
        | Reader rest ->
          mk_constr "Reader" [ mk_fmt rest ]
        | Scan_char_set (width_opt, char_set, rest) ->
          mk_constr "Scan_char_set" [
            mk_int_opt width_opt; mk_string char_set; mk_fmt rest ]
        | Scan_get_counter (cnt, rest) ->
          mk_constr "Scan_get_counter" [ mk_counter cnt; mk_fmt rest ]
        | Scan_next_char rest ->
          mk_constr "Scan_next_char" [ mk_fmt rest ]
        | Ignored_param (ign, rest) ->
          mk_constr "Ignored_param" [ mk_ignored ign; mk_fmt rest ]
        | End_of_format ->
          mk_constr "End_of_format" []
        | Custom _ ->
          (* Custom formatters have no syntax so they will never appear
             in formats parsed from strings. *)
          assert false
      in
      let legacy_behavior = not !Clflags.strict_formats in
      let Fmt_EBB fmt = fmt_ebb_of_string ~legacy_behavior str in
      mk_constr "Format" [ mk_fmt fmt; mk_string str ]
    ))
  with Failure msg ->
    raise (Error (loc, env, Invalid_format msg))

and type_label_exp create env loc ty_expected eff_expected
          (lid, label, sarg) =
  (* Here also ty_expected may be at generic_level *)
  begin_def ();
  let separate = !Clflags.principal || Env.has_local_constraints env in
  if separate then (begin_def (); begin_def ());
  let (vars, ty_arg, ty_res) = instance_label true label in
  if separate then begin
    end_def ();
    (* Generalize label information *)
    generalize_structure ty_arg;
    generalize_structure ty_res
  end;
  begin try
    unify env (instance_def ty_res) (instance env ty_expected)
  with Unify trace ->
    raise (Error(lid.loc, env, Label_mismatch(lid.txt, trace)))
  end;
  (* Instantiate so that we can generalize internal nodes *)
  let ty_arg = instance_def ty_arg in
  if separate then begin
    end_def ();
    (* Generalize information merged from ty_expected *)
    generalize_structure ty_arg
  end;
  if label.lbl_private = Private then
    if create then
      raise (Error(loc, env, Private_type ty_expected))
    else
      raise (Error(lid.loc, env, Private_label(lid.txt, ty_expected)));
  let arg =
    let snap = if vars = [] then None else Some (Btype.snapshot ()) in
    let arg =
      type_argument env sarg ty_arg (instance env ty_arg) eff_expected
    in
    end_def ();
    try
      check_univars env (vars <> []) "field value" arg label.lbl_arg vars;
      arg
    with exn when not (is_nonexpansive arg) -> try
      (* Try to retype without propagating ty_arg, cf PR#4862 *)
      may Btype.backtrack snap;
      begin_def ();
      let arg = type_exp env sarg eff_expected in
      end_def ();
      generalize_expansive env arg.exp_type;
      unify_exp env arg ty_arg;
      check_univars env false "field value" arg label.lbl_arg vars;
      arg
    with Error (_, _, Less_general _) as e -> raise e
    | _ -> raise exn    (* In case of failure return the first error *)
  in
  (lid, label, {arg with exp_type = instance env arg.exp_type})

and type_argument env sarg ty_expected' ty_expected eff_expected =
  (* ty_expected' may be generic *)
  let no_labels ty =
    let ls, tvar = list_labels env ty in
    not tvar && List.for_all ((=) "") ls
  in
  let rec is_inferred sexp =
    match sexp.pexp_desc with
      Pexp_ident _ | Pexp_apply _ | Pexp_field _ | Pexp_constraint _
    | Pexp_coerce _ | Pexp_send _ | Pexp_new _ -> true
    | Pexp_sequence (_, e) | Pexp_open (_, _, e) -> is_inferred e
    | Pexp_ifthenelse (_, e1, Some e2) -> is_inferred e1 && is_inferred e2
    | _ -> false
  in
  match expand_head env ty_expected' with
    {desc = Tarrow("",ty_arg,_,ty_res,_); level = lv} when is_inferred sarg ->
      (* apply optional arguments when expected type is "" *)
      (* we must be very careful about not breaking the semantics *)
      if !Clflags.principal then begin_def ();
      let texp = type_exp env sarg eff_expected in
      if !Clflags.principal then begin
        end_def ();
        generalize_structure texp.exp_type
      end;
      let rec make_args args ty_fun =
        match (expand_head env ty_fun).desc with
        | Tarrow (l,ty_arg,_,ty_fun,_) when is_optional l ->
            let ty = option_none (instance env ty_arg) sarg.pexp_loc in
            make_args ((l, Some ty, Optional) :: args) ty_fun
        | Tarrow (l,_,_,ty_res',_) when l = "" || !Clflags.classic ->
            List.rev args, ty_fun, no_labels ty_res'
        | Tvar _ ->  List.rev args, ty_fun, false
        |  _ -> [], texp.exp_type, false
      in
      let args, ty_fun', simple_res = make_args [] texp.exp_type in
      let warn = !Clflags.principal &&
        (lv <> generic_level || (repr ty_fun').level <> generic_level)
      and texp = {texp with exp_type = instance env texp.exp_type}
      and ty_fun = instance env ty_fun' in
      if not (simple_res || no_labels ty_res) then begin
        unify_exp env texp ty_expected;
        texp
      end else begin
      unify_exp env {texp with exp_type = ty_fun} ty_expected;
      if args = [] then texp else
      (* eta-expand to avoid side effects *)
      let var_pair name ty =
        let id = Ident.create name in
        {pat_desc = Tpat_var (id, mknoloc name); pat_type = ty;pat_extra=[];
         pat_attributes = [];
         pat_loc = Location.none; pat_env = env},
        {exp_type = ty; exp_loc = Location.none; exp_env = env;
         exp_extra = []; exp_attributes = [];
         exp_desc =
         Texp_ident(Path.Pident id, mknoloc (Longident.Lident name),
                    {val_type = ty; val_kind = Val_reg;
                     val_attributes = [];
                     Types.val_loc = Location.none})}
      in
      let eta_pat, eta_var = var_pair "eta" ty_arg in
      let func texp =
        let e =
          {texp with exp_type = ty_res; exp_desc =
           Texp_apply
             (texp,
              args @ ["", Some eta_var, Required])}
        in
        { texp with exp_type = ty_fun; exp_desc =
          Texp_function("", [case eta_pat e], Total) }
      in
      Location.prerr_warning texp.exp_loc
        (Warnings.Eliminated_optional_arguments (List.map (fun (l, _, _) -> l) args));
      if warn then Location.prerr_warning texp.exp_loc
          (Warnings.Without_principality "eliminated optional argument");
      if is_nonexpansive texp then func texp else
      (* let-expand to have side effects *)
      let let_pat, let_var = var_pair "arg" texp.exp_type in
      re { texp with exp_type = ty_fun; exp_desc =
           Texp_let (Nonrecursive,
                     [{vb_pat=let_pat; vb_expr=texp; vb_attributes=[];
                       vb_loc=Location.none;
                      }],
                     func let_var) }
      end
  | _ ->
      let texp = type_expect env sarg ty_expected' eff_expected in
      unify_exp env texp ty_expected;
      texp

and type_application loc env funct sargs eff_expected =
  (* funct.exp_type may be generic *)
  let result_type omitted ty_fun =
    List.fold_left
      (fun ty_fun (l,ty,ty_eff,lv) -> newty2 lv (Tarrow(l,ty,ty_eff,ty_fun,Cok)))
      ty_fun omitted
  in
  let has_label l ty_fun =
    let ls, tvar = list_labels env ty_fun in
    tvar || List.mem l ls
  in
  let ignored = ref [] in
  let rec type_unknown_args
      (args :
      (Asttypes.label * (unit -> Typedtree.expression) option *
         Typedtree.optional) list)
    omitted eff ty_fun = function
      [] ->
        (List.map
            (function l, None, x -> l, None, x
                | l, Some f, x -> l, Some (f ()), x)
           (List.rev args),
         instance env (result_type omitted ty_fun))
    | (l1, sarg1) :: sargl ->
        let (ty_arg, ty_eff, ty_res) =
          let ty_fun = expand_head env ty_fun in
          match ty_fun.desc with
            Tvar _ ->
              let t1 = newvar Stype in
              let t2 = newvar Seffect in
              let t3 = newvar Stype in
              let not_identity = function
                  Texp_ident(_,_,{val_kind=Val_prim
                                  {Primitive.prim_name="%identity"}}) ->
                    false
                | _ -> true
              in
              if ty_fun.level >= t1.level && not_identity funct.exp_desc then
                Location.prerr_warning sarg1.pexp_loc Warnings.Unused_argument;
              unify env ty_fun (newty (Tarrow(l1,t1,t2,t3,Clink(ref Cunknown))));
              (t1, t2, t3)
          | Tarrow (l,t1,t2,t3,_) when l = l1
            || !Clflags.classic && l1 = "" && not (is_optional l) ->
              (t1, t2, t3)
          | td ->
              let ty_fun =
                match td with Tarrow _ -> newty td | _ -> ty_fun in
              let ty_res = result_type (omitted @ !ignored) ty_fun in
              match ty_res.desc with
                Tarrow _ ->
                  if (!Clflags.classic || not (has_label l1 ty_fun)) then
                    raise (Error(sarg1.pexp_loc, env,
                                 Apply_wrong_label(l1, ty_res)))
                  else
                    raise (Error(funct.exp_loc, env, Incoherent_label_order))
              | _ ->
                  raise(Error(funct.exp_loc, env, Apply_non_function
                                (expand_head env funct.exp_type)))
        in
        let optional = if is_optional l1 then Optional else Required in
        let arg1 () =
          let arg1 = type_expect env sarg1 ty_arg eff_expected in
          if optional = Optional then
            unify_exp env arg1 (type_option (newvar Stype));
          begin try
            unify env ty_eff eff;
          with Unify trace ->
            if omitted = [] then
              raise(Error(loc, env, Expr_effect_clash(trace)))
            else
              raise(Error(sarg1.pexp_loc, env, Label_effect_clash(trace)))
          end;
          arg1
        in
        type_unknown_args ((l1, Some arg1, optional) :: args)
          omitted eff ty_res sargl
  in
  let ignore_labels =
    !Clflags.classic ||
    begin
      let ls, tvar = list_labels env funct.exp_type in
      not tvar &&
      let labels = List.filter (fun l -> not (is_optional l)) ls in
      List.length labels = List.length sargs &&
      List.for_all (fun (l,_) -> l = "") sargs &&
      List.exists (fun l -> l <> "") labels &&
      (Location.prerr_warning funct.exp_loc Warnings.Labels_omitted;
       true)
    end
  in
  let warned = ref false in
  let rec type_args args omitted eff ty_fun ty_fun0 ty_old sargs more_sargs =
    match expand_head env ty_fun, expand_head env ty_fun0 with
      {desc=Tarrow (l, ty, eff_fun, ty_fun, com); level=lv} as ty_fun',
      {desc=Tarrow (_, ty0, _, ty_fun0, _)}
      when (sargs <> [] || more_sargs <> []) && commu_repr com = Cok ->
        let may_warn loc w =
          if not !warned && !Clflags.principal && lv <> generic_level
          then begin
            warned := true;
            Location.prerr_warning loc w
          end
        in
        let unify_effect sarg0 =
          try
            unify env eff_fun eff;
          with Unify trace ->
            if omitted = [] then
              raise(Error(loc, env, Expr_effect_clash(trace)))
            else
              raise(Error(sarg0.pexp_loc, env, Label_effect_clash(trace)))
        in
        let name = label_name l
        and optional = if is_optional l then Optional else Required in
        let sargs, more_sargs, arg =
          if ignore_labels && not (is_optional l) then begin
            (* In classic mode, omitted = [] *)
            match sargs, more_sargs with
              (l', sarg0) :: _, _ ->
                raise(Error(sarg0.pexp_loc, env,
                            Apply_wrong_label(l', ty_old)))
            | _, (l', sarg0) :: more_sargs ->
                if l <> l' && l' <> "" then
                  raise(Error(sarg0.pexp_loc, env,
                              Apply_wrong_label(l', ty_fun')))
                else
                  ([], more_sargs,
                   Some (fun () ->
                           unify_effect sarg0;
                           type_argument env sarg0 ty ty0 eff_expected))
            | _ ->
                assert false
          end else try
            let (l', sarg0, sargs, more_sargs) =
              try
                let (l', sarg0, sargs1, sargs2) = extract_label name sargs in
                if sargs1 <> [] then
                  may_warn sarg0.pexp_loc
                    (Warnings.Not_principal "commuting this argument");
                (l', sarg0, sargs1 @ sargs2, more_sargs)
              with Not_found ->
                let (l', sarg0, sargs1, sargs2) =
                  extract_label name more_sargs in
                if sargs1 <> [] || sargs <> [] then
                  may_warn sarg0.pexp_loc
                    (Warnings.Not_principal "commuting this argument");
                (l', sarg0, sargs @ sargs1, sargs2)
            in
            if optional = Required && is_optional l' then
              Location.prerr_warning sarg0.pexp_loc
                (Warnings.Nonoptional_label l);
            sargs, more_sargs,
            if optional = Required || is_optional l' then
              Some (fun () ->
                      unify_effect sarg0;
                      type_argument env sarg0 ty ty0 eff_expected)
            else begin
              may_warn sarg0.pexp_loc
                (Warnings.Not_principal "using an optional argument here");
              Some (fun () ->
                      unify_effect sarg0;
                      option_some (type_argument env sarg0
                                     (extract_option_type env ty)
                                     (extract_option_type env ty0)
                                     eff_expected))
            end
          with Not_found ->
            sargs, more_sargs,
            if optional = Optional &&
              (List.mem_assoc "" sargs || List.mem_assoc "" more_sargs)
            then begin
              may_warn funct.exp_loc
                (Warnings.Without_principality "eliminated optional argument");
              ignored := (l,ty,eff_fun,lv) :: !ignored;
              Some (fun () -> option_none (instance env ty) Location.none)
            end else begin
              may_warn funct.exp_loc
                (Warnings.Without_principality "commuted an argument");
              None
            end
        in
        let omitted =
          if arg = None then (l,ty,eff_fun,lv) :: omitted else omitted
        in
        let eff = if arg = None then eff_fun else eff in
        let ty_old = if sargs = [] then ty_fun else ty_old in
        type_args ((l,arg,optional)::args) omitted eff ty_fun ty_fun0
          ty_old sargs more_sargs
    | _ ->
        match sargs with
          (l, sarg0) :: _ when ignore_labels ->
            raise(Error(sarg0.pexp_loc, env,
                        Apply_wrong_label(l, ty_old)))
        | _ ->
            type_unknown_args args omitted eff ty_fun0
              (sargs @ more_sargs)
  in
  match funct.exp_desc, sargs with
    (* Special case for ignore: avoid discarding warning *)
    Texp_ident (_, _, {val_kind=Val_prim{Primitive.prim_name="%ignore"}}),
    ["", sarg] ->
      let ty_arg, ty_eff, ty_res =
        filter_arrow env (instance env funct.exp_type) ""
      in
      let exp = type_expect env sarg ty_arg eff_expected in
      begin match (expand_head env exp.exp_type).desc with
      | Tarrow _ ->
          Location.prerr_warning exp.exp_loc Warnings.Partial_application
      | Tvar _ ->
          add_delayed_check (fun () -> check_application_result env false exp)
      | _ -> ()
      end;
      (["", Some exp, Required], ty_res)
  | _ ->
      let ty = funct.exp_type in
      if ignore_labels then
        type_args [] [] eff_expected ty (instance env ty) ty [] sargs
      else
        type_args [] [] eff_expected ty (instance env ty) ty sargs []

and type_construct env loc lid sarg ty_expected eff_expected attrs =
  let opath =
    try
      let (p0, p,_) = extract_concrete_variant env ty_expected in
      Some(p0, p, ty_expected.level = generic_level || not !Clflags.principal)
    with Not_found -> None
  in
  let constrs = Typetexp.find_all_constructors env lid.loc lid.txt in
  let constr =
    wrap_disambiguate "This variant expression is expected to have" ty_expected
      (Constructor.disambiguate lid env opath) constrs in
  Env.mark_constructor Env.Positive env (Longident.last lid.txt) constr;
  Typetexp.check_deprecated loc constr.cstr_attributes constr.cstr_name;
  let sargs =
    match sarg with
      None -> []
    | Some {pexp_desc = Pexp_tuple sel} when
        constr.cstr_arity > 1 || explicit_arity attrs
      -> sel
    | Some se -> [se] in
  if List.length sargs <> constr.cstr_arity then
    raise(Error(loc, env, Constructor_arity_mismatch
                  (lid.txt, constr.cstr_arity, List.length sargs)));
  let separate = !Clflags.principal || Env.has_local_constraints env in
  if separate then (begin_def (); begin_def ());
  let (ty_args, ty_res) = instance_constructor constr in
  let texp =
    re {
      exp_desc = Texp_construct(lid, constr, []);
      exp_loc = loc; exp_extra = [];
      exp_type = ty_res;
      exp_attributes = attrs;
      exp_env = env } in
  if separate then begin
    end_def ();
    generalize_structure ty_res;
    unify_exp env {texp with exp_type = instance_def ty_res}
                  (instance env ty_expected);
    end_def ();
    List.iter generalize_structure ty_args;
    generalize_structure ty_res;
  end;
  let ty_args0, ty_res =
    match instance_list env (ty_res :: ty_args) with
      t :: tl -> tl, t
    | _ -> assert false
  in
  let texp = {texp with exp_type = ty_res} in
  if not separate then unify_exp env texp (instance env ty_expected);
  let args =
    List.map2 (fun e (t,t0) -> type_argument env e t t0 eff_expected)
      sargs (List.combine ty_args ty_args0)
  in
  if constr.cstr_private = Private then
    raise(Error(loc, env, Private_type ty_res));
  (* NOTE: shouldn't we call "re" on this final expression? -- AF *)
  { texp with
    exp_desc = Texp_construct(lid, constr, args) }

and type_perform env loc lid sarg ty_expected eff_expected attrs =
  let ecstr = Typetexp.find_effect_constructor env lid.loc lid.txt in
  Typetexp.check_deprecated loc ecstr.ecstr_attributes ecstr.ecstr_name;
  let sargs =
    match sarg with
      None -> []
    | Some {pexp_desc = Pexp_tuple sel} when
        ecstr.ecstr_arity > 1 || explicit_arity attrs
      -> sel
    | Some se -> [se]
  in
  if List.length sargs <> ecstr.ecstr_arity then
    raise(Error(loc, env, Constructor_arity_mismatch
                  (lid.txt, ecstr.ecstr_arity, List.length sargs)));
  let separate = !Clflags.principal || Env.has_local_constraints env in
  if separate then (begin_def (); begin_def ());
  let (ty_args, ty_res) = instance_effect_constructor ecstr in
  let ty_res =
    match ty_res with
    | None -> newvar Stype
    | Some ty_res -> ty_res
  in
  if separate then begin
    end_def ();
    generalize_structure ty_res;
    unify_exp_types loc env ty_res
                    (instance env ty_expected);
    end_def ();
    List.iter generalize_structure ty_args;
    generalize_structure ty_res;
  end;
  let ty_args0, ty_res =
    match instance_list env (ty_res :: ty_args) with
    | t :: tl -> tl, t
    | _ -> assert false
  in
  if not separate then
    unify_exp_types loc env ty_res (instance env ty_expected);
  let eff = newty (Teffect(ecstr.ecstr_eff_path, newvar Seffect)) in
  unify_exp_effects loc env eff eff_expected;
  let args =
    List.map2 (fun e (t,t0) -> type_argument env e t t0 eff_expected)
      sargs (List.combine ty_args ty_args0)
  in
    re {
      exp_desc = Texp_perform(lid, ecstr, args);
      exp_loc = loc; exp_extra = [];
      exp_type = ty_res;
      exp_attributes = attrs;
      exp_env = env }

(* Typing of statements (expressions whose values are discarded) *)

and type_statement env sexp eff_expected =
  let loc = (final_subexpression sexp).pexp_loc in
  begin_def();
  let exp = type_exp env sexp eff_expected in
  end_def();
  if !Clflags.strict_sequence then
    let expected_ty = instance_def Predef.type_unit in
    unify_exp env exp expected_ty;
    exp else
  let ty = expand_head env exp.exp_type and tv = newvar Stype in
  begin match ty.desc with
  | Tarrow _ ->
      Location.prerr_warning loc Warnings.Partial_application
  | Tconstr (p, _, _, _) when Path.same p Predef.path_unit -> ()
  | Tvar _ when ty.level > tv.level ->
      Location.prerr_warning loc Warnings.Nonreturning_statement
  | Tvar _ ->
      add_delayed_check (fun () -> check_application_result env true exp)
  | _ ->
      Location.prerr_warning loc Warnings.Statement_type
  end;
  unify_var env tv ty;
  exp

(* Typing of match cases *)

and type_cases ?in_function ~allow_exn env ty_arg ty_eff ty_res loc caselist =
  (* ty_arg is _fully_ generalized *)
  let patterns = List.map (fun {pc_lhs=p} -> p) caselist in
  let erase_either =
    List.exists contains_polymorphic_variant patterns
    && contains_variant_either ty_arg
  and has_gadts = List.exists (contains_gadt env) patterns in
(*  prerr_endline ( if has_gadts then "contains gadt" else "no gadt"); *)
  let ty_arg =
    if (has_gadts || erase_either) && not !Clflags.principal
    then correct_levels ty_arg else ty_arg
  and ty_res, env =
    if has_gadts && not !Clflags.principal then
      correct_levels ty_res, duplicate_ident_types loc caselist env
    else ty_res, env
  in
  let lev, env =
    if has_gadts then begin
      (* raise level for existentials *)
      begin_def ();
      Ident.set_current_time (get_current_level ());
      let lev = Ident.current_time () in
      Ctype.init_def (lev+1000);                 (* up to 1000 existentials *)
      (lev, Env.add_gadt_instance_level lev env)
    end else (get_current_level (), env)
  in
(*  if has_gadts then
    Format.printf "lev = %d@.%a@." lev Printtyp.raw_type_expr ty_res; *)
  begin_def (); (* propagation of the argument *)
  let ty_arg' = newvar Stype in
  let pattern_force = ref [] in
(*  Format.printf "@[%i %i@ %a@]@." lev (get_current_level())
    Printtyp.raw_type_expr ty_arg; *)
  let pat_env_list =
    List.map
      (fun {pc_lhs; pc_guard; pc_rhs} ->
        let loc =
          let open Location in
          match pc_guard with
          | None -> pc_rhs.pexp_loc
          | Some g -> {pc_rhs.pexp_loc with loc_start=g.pexp_loc.loc_start}
        in
        if !Clflags.principal then begin_def (); (* propagation of pattern *)
        let scope = Some (Annot.Idef loc) in
        let (pat, ext_env, force, unpacks) =
          let partial =
            if !Clflags.principal || erase_either
            then Some false else None in
          let ty_arg = instance ?partial env ty_arg in
          type_pattern ~lev ~allow_exn env pc_lhs scope ty_arg ty_eff
        in
        pattern_force := force @ !pattern_force;
        let pat =
          if !Clflags.principal then begin
            end_def ();
            iter_pattern (fun {pat_type=t} -> generalize_structure t) pat;
            { pat with pat_type = instance env pat.pat_type }
          end else pat
        in
        (pat, (ext_env, unpacks)))
      caselist in
  (* Unify cases (delayed to keep it order-free) *)
  let patl = List.map fst pat_env_list in
  List.iter (fun pat -> unify_pat env pat ty_arg') patl;
  (* Check for polymorphic variants to close *)
  if List.exists has_variants patl then begin
    Parmatch.pressure_variants env patl;
    List.iter (iter_pattern finalize_variant) patl
  end;
  (* `Contaminating' unifications start here *)
  List.iter (fun f -> f()) !pattern_force;
  (* Post-processing and generalization *)
  List.iter (iter_pattern (fun {pat_type=t} -> unify_var env t (newvar Stype)))
    patl;
  List.iter (fun pat -> unify_pat env pat (instance env ty_arg)) patl;
  end_def ();
  List.iter (iter_pattern (fun {pat_type=t} -> generalize t)) patl;
  (* type bodies *)
  let in_function = if List.length caselist = 1 then in_function else None in
  let cases =
    List.map2
      (fun (pat, (ext_env, unpacks)) {pc_lhs; pc_guard; pc_rhs} ->
        let sexp = wrap_unpacks pc_rhs unpacks in
        let ty_res' =
          if !Clflags.principal then begin
            begin_def ();
            let ty = instance ~partial:true env ty_res in
            end_def ();
            generalize_structure ty; ty
          end
          else if contains_gadt env pc_lhs then correct_levels ty_res
          else ty_res in
(*        Format.printf "@[%i %i, ty_res' =@ %a@]@." lev (get_current_level())
          Printtyp.raw_type_expr ty_res'; *)
        let guard =
          match pc_guard with
          | None -> None
          | Some scond ->
              Some
                (type_expect ext_env (wrap_unpacks scond unpacks)
                   Predef.type_bool ty_eff)
        in
        let exp = type_expect ?in_function ext_env sexp ty_res' ty_eff in
        {
         c_lhs = pat;
         c_guard = guard;
         c_rhs = {exp with exp_type = instance env ty_res'}
        }
      )
      pat_env_list caselist
  in
  if !Clflags.principal || has_gadts then begin
    let ty_res' = instance env ty_res in
    List.iter (fun c -> unify_exp env c.c_rhs ty_res') cases
  end;
  let partial, handled = check_partial ~lev env ty_arg ty_eff loc cases in
  add_delayed_check
    (fun () ->
      List.iter (fun (pat, (env, _)) -> check_absent_variant env pat)
        pat_env_list;
      Parmatch.check_unused env cases);
  if has_gadts then begin
    end_def ();
    (* Ensure that existential types do not escape *)
    unify_exp_types loc env (instance env ty_res) (newvar Stype) ;
  end;
  cases, partial, handled

(* Typing of let bindings *)

and type_let ?(check = fun s -> Warnings.Unused_var s)
             ?(check_strict = fun s -> Warnings.Unused_var_strict s)
    env rec_flag spat_sexp_list scope allow eff_expected =
  let open Ast_helper in
  begin_def();
  if !Clflags.principal then begin_def ();

  let is_fake_let =
    match spat_sexp_list with
    | [{pvb_expr={pexp_desc=Pexp_match(
           {pexp_desc=Pexp_ident({ txt = Longident.Lident "*opt*"})},_)}}] ->
        true (* the fake let-declaration introduced by fun ?(x = e) -> ... *)
    | _ ->
        false
  in
  let check = if is_fake_let then check_strict else check in

  let spatl =
    List.map
      (fun {pvb_pat=spat; pvb_expr=sexp; pvb_attributes=_} ->
        match spat.ppat_desc, sexp.pexp_desc with
          (Ppat_any | Ppat_constraint _), _ -> spat
        | _, Pexp_coerce (_, _, sty)
        | _, Pexp_constraint (_, sty) when !Clflags.principal ->
            (* propagate type annotation to pattern,
               to allow it to be generalized in -principal mode *)
            Pat.constraint_
              ~loc:{spat.ppat_loc with Location.loc_ghost=true}
              spat
              sty
        | _ -> spat)
      spat_sexp_list in
  let nvs = List.map (fun _ -> newvar Stype) spatl in
  let (pat_list, new_env, force, unpacks) =
    type_pattern_list ~allow_exn:false env spatl scope nvs eff_expected allow in
  let is_recursive = (rec_flag = Recursive) in
  (* If recursive, first unify with an approximation of the expression *)
  if is_recursive then
    List.iter2
      (fun pat binding ->
        let pat =
          match pat.pat_type.desc with
          | Tpoly (ty, tl) ->
              {pat with pat_type =
               snd (instance_poly ~keep_names:true false tl ty)}
          | _ -> pat
        in unify_pat env pat (type_approx env binding.pvb_expr))
      pat_list spat_sexp_list;
  (* Polymorphic variant processing *)
  List.iter
    (fun pat ->
      if has_variants pat then begin
        Parmatch.pressure_variants env [pat];
        iter_pattern finalize_variant pat
      end)
    pat_list;
  (* Generalize the structure *)
  let pat_list =
    if !Clflags.principal then begin
      end_def ();
      List.map
        (fun pat ->
          iter_pattern (fun pat -> generalize_structure pat.pat_type) pat;
          {pat with pat_type = instance env pat.pat_type})
        pat_list
    end else pat_list in
  (* Only bind pattern variables after generalizing *)
  List.iter (fun f -> f()) force;
  let exp_env =
    if is_recursive then new_env else env in

  let current_slot = ref None in
  let rec_needed = ref false in
  let warn_unused =
    Warnings.is_active (check "") || Warnings.is_active (check_strict "") ||
    (is_recursive && (Warnings.is_active Warnings.Unused_rec_flag))
  in
  let pat_slot_list =
    (* Algorithm to detect unused declarations in recursive bindings:
       - During type checking of the definitions, we capture the 'value_used'
         events on the bound identifiers and record them in a slot corresponding
         to the current definition (!current_slot).
         In effect, this creates a dependency graph between definitions.

       - After type checking the definition (!current_slot = None),
         when one of the bound identifier is effectively used, we trigger
         again all the events recorded in the corresponding slot.
         The effect is to traverse the transitive closure of the graph created
         in the first step.

       We also keep track of whether *all* variables in a given pattern
       are unused. If this is the case, for local declarations, the issued
       warning is 26, not 27.
     *)
    List.map
      (fun pat ->
        if not warn_unused then pat, None
        else
          let some_used = ref false in
            (* has one of the identifier of this pattern been used? *)
          let slot = ref [] in
          List.iter
            (fun (id,_) ->
              let vd = Env.find_value (Path.Pident id) new_env in
              (* note: Env.find_value does not trigger the value_used event *)
              let name = Ident.name id in
              let used = ref false in
              if not (name = "" || name.[0] = '_' || name.[0] = '#') then
                add_delayed_check
                  (fun () ->
                    if not !used then
                      Location.prerr_warning vd.Types.val_loc
                        ((if !some_used then check_strict else check) name)
                  );
              Env.set_value_used_callback
                name vd
                (fun () ->
                  match !current_slot with
                  | Some slot ->
                      slot := (name, vd) :: !slot; rec_needed := true
                  | None ->
                      List.iter
                        (fun (name, vd) -> Env.mark_value_used env name vd)
                        (get_ref slot);
                      used := true;
                      some_used := true
                )
            )
            (Typedtree.pat_bound_idents pat);
          pat, Some slot
        )
      pat_list
  in
  let exp_list =
    List.map2
      (fun {pvb_expr=sexp; _} (pat, slot) ->
        let sexp =
          if rec_flag = Recursive then wrap_unpacks sexp unpacks else sexp in
        if is_recursive then current_slot := slot;
        match pat.pat_type.desc with
        | Tpoly (ty, tl) ->
            begin_def ();
            if !Clflags.principal then begin_def ();
            let vars, ty' = instance_poly ~keep_names:true true tl ty in
            if !Clflags.principal then begin
              end_def ();
              generalize_structure ty'
            end;
            let exp = type_expect exp_env sexp ty' eff_expected in
            end_def ();
            check_univars env true "definition" exp pat.pat_type vars;
            {exp with exp_type = instance env exp.exp_type}
        | _ -> type_expect exp_env sexp pat.pat_type eff_expected)
      spat_sexp_list pat_slot_list in
  current_slot := None;
  if is_recursive && not !rec_needed
  && Warnings.is_active Warnings.Unused_rec_flag then
    Location.prerr_warning (List.hd spat_sexp_list).pvb_pat.ppat_loc
      Warnings.Unused_rec_flag;
  List.iter2
    (fun pat exp ->
      ignore(check_partial env pat.pat_type eff_expected
               pat.pat_loc [case pat exp]))
    pat_list exp_list;
  end_def();
  List.iter2
    (fun pat exp ->
       if not (is_nonexpansive exp) then
         iter_pattern (fun pat -> generalize_expansive env pat.pat_type) pat)
    pat_list exp_list;
  List.iter
    (fun pat -> iter_pattern (fun pat -> generalize pat.pat_type) pat)
    pat_list;
  List.iter
    (fun pat ->
      iter_pattern (fun pat -> close_effects_covariant env pat.pat_type) pat)
    pat_list;
  let l = List.combine pat_list exp_list in
  let l =
    List.map2
      (fun (p, e) pvb ->
        {vb_pat=p; vb_expr=e; vb_attributes=pvb.pvb_attributes;
         vb_loc=pvb.pvb_loc;
        })
      l spat_sexp_list
  in
  (l, new_env, unpacks)

(* Typing of toplevel bindings *)

let type_binding env rec_flag spat_sexp_list eff_expected scope =
  Typetexp.reset_type_variables();
  let (pat_exp_list, new_env, unpacks) =
    type_let
      ~check:(fun s -> Warnings.Unused_value_declaration s)
      ~check_strict:(fun s -> Warnings.Unused_value_declaration s)
      env rec_flag spat_sexp_list scope false eff_expected
  in
  (pat_exp_list, new_env)

let type_let env rec_flag spat_sexp_list eff_expected scope =
  let (pat_exp_list, new_env, unpacks) =
    type_let env rec_flag spat_sexp_list scope false eff_expected in
  (pat_exp_list, new_env)

(* Typing of toplevel expressions *)

let type_expression env sexp eff_expected =
  Typetexp.reset_type_variables();
  begin_def();
  let exp = type_exp env sexp eff_expected in
  end_def();
  if is_nonexpansive exp then generalize exp.exp_type
  else generalize_expansive env exp.exp_type;
  close_effects_covariant env exp.exp_type;
  match sexp.pexp_desc with
    Pexp_ident lid ->
      (* Special case for keeping type variables when looking-up a variable *)
      let (path, desc) = Env.lookup_value lid.txt env in
      {exp with exp_type = desc.val_type}
  | _ -> exp

(* Error report *)

open Format
open Printtyp

let report_error env ppf = function
  | Polymorphic_label lid ->
      fprintf ppf "@[The record field %a is polymorphic.@ %s@]"
        longident lid "You cannot instantiate it in a pattern."
  | Constructor_arity_mismatch(lid, expected, provided) ->
      fprintf ppf
       "@[The constructor %a@ expects %i argument(s),@ \
        but is applied here to %i argument(s)@]"
       longident lid expected provided
  | Label_mismatch(lid, trace) ->
      report_unification_error ppf env trace
        (function ppf ->
           fprintf ppf "The record field %a@ belongs to the type"
                   longident lid)
        (function ppf ->
           fprintf ppf "but is mixed here with fields of type")
  | Pattern_type_clash trace ->
      report_unification_error ppf env trace
        (function ppf ->
          fprintf ppf "This pattern matches values of type")
        (function ppf ->
          fprintf ppf "but a pattern was expected which matches values of type")
  | Pattern_effect_clash trace ->
      report_unification_error ppf env trace
        (function ppf ->
           fprintf ppf "This pattern performs effect")
        (function ppf ->
           fprintf ppf "but an pattern was expected that performed")
  | Or_pattern_type_clash (id, trace) ->
      report_unification_error ppf env trace
        (function ppf ->
          fprintf ppf "The variable %s on the left-hand side of this or-pattern has type" (Ident.name id))
        (function ppf ->
          fprintf ppf "but on the right-hand side it has type")
  | Multiply_bound_variable name ->
      fprintf ppf "Variable %s is bound several times in this matching" name
  | Orpat_vars id ->
      fprintf ppf "Variable %s must occur on both sides of this | pattern"
        (Ident.name id)
  | Expr_type_clash trace ->
      report_unification_error ppf env trace
        (function ppf ->
           fprintf ppf "This expression has type")
        (function ppf ->
           fprintf ppf "but an expression was expected of type")
  | Expr_effect_clash trace ->
      report_unification_error ppf env trace
        (function ppf ->
           fprintf ppf "This expression performs effect")
        (function ppf ->
           fprintf ppf "but an expression was expected that performed")
  | Label_effect_clash trace ->
      report_unification_error ppf env trace
        (function ppf ->
           fprintf ppf "Applying this argument performs effect")
        (function ppf ->
           fprintf ppf "but an omitted parameter performs effect")
  | Apply_non_function typ ->
      reset_and_mark_loops typ;
      begin match (repr typ).desc with
        Tarrow _ ->
          fprintf ppf "@[<v>@[<2>This function has type@ %a@]"
            type_expr typ;
          fprintf ppf "@ @[It is applied to too many arguments;@ %s@]@]"
                      "maybe you forgot a `;'."
      | _ ->
          fprintf ppf "@[<v>@[<2>This expression has type@ %a@]@ %s@]"
            type_expr typ
            "This is not a function; it cannot be applied."
      end
  | Apply_wrong_label (l, ty) ->
      let print_label ppf = function
        | "" -> fprintf ppf "without label"
        | l ->
            fprintf ppf "with label %s" (prefixed_label_name l)
      in
      reset_and_mark_loops ty;
      fprintf ppf
        "@[<v>@[<2>The function applied to this argument has type@ %a@]@.\
          This argument cannot be applied %a@]"
        type_expr ty print_label l
  | Label_multiply_defined s ->
      fprintf ppf "The record field label %s is defined several times" s
  | Label_missing labels ->
      let print_labels ppf =
        List.iter (fun lbl -> fprintf ppf "@ %s" (Ident.name lbl)) in
      fprintf ppf "@[<hov>Some record fields are undefined:%a@]"
        print_labels labels
  | Label_not_mutable lid ->
      fprintf ppf "The record field %a is not mutable" longident lid
  | Wrong_name (eorp, ty, kind, p, lid) ->
      reset_and_mark_loops ty;
      fprintf ppf "@[@[<2>%s type@ %a@]@ "
        eorp type_expr ty;
      fprintf ppf "The %s %a does not belong to type %a@]"
        (if kind = "record" then "field" else "constructor")
        longident lid (*kind*) path p;
      if kind = "record" then Label.spellcheck ppf env p lid
                         else Constructor.spellcheck ppf env p lid
  | Name_type_mismatch (kind, lid, tp, tpl) ->
      let name = if kind = "record" then "field" else "constructor" in
      report_ambiguous_type_error ppf env tp tpl
        (function ppf ->
           fprintf ppf "The %s %a@ belongs to the %s type"
             name longident lid kind)
        (function ppf ->
           fprintf ppf "The %s %a@ belongs to one of the following %s types:"
             name longident lid kind)
        (function ppf ->
           fprintf ppf "but a %s was expected belonging to the %s type"
             name kind)
  | Invalid_format msg ->
      fprintf ppf "%s" msg
  | Undefined_method (ty, me) ->
      reset_and_mark_loops ty;
      fprintf ppf
        "@[<v>@[This expression has type@;<1 2>%a@]@,\
         It has no method %s@]" type_expr ty me
  | Undefined_inherited_method me ->
      fprintf ppf "This expression has no method %s" me
  | Virtual_class cl ->
      fprintf ppf "Cannot instantiate the virtual class %a"
        longident cl
  | Unbound_instance_variable v ->
      fprintf ppf "Unbound instance variable %s" v
  | Instance_variable_not_mutable (b, v) ->
      if b then
        fprintf ppf "The instance variable %s is not mutable" v
      else
        fprintf ppf "The value %s is not an instance variable" v
  | Not_subtype(tr1, tr2) ->
      report_subtyping_error ppf env tr1 "is not a subtype of" tr2
  | Outside_class ->
      fprintf ppf "This object duplication occurs outside a method definition"
  | Value_multiply_overridden v ->
      fprintf ppf "The instance variable %s is overridden several times" v
  | Coercion_failure (ty, ty', trace, b) ->
      report_unification_error ppf env trace
        (function ppf ->
           let ty, ty' = prepare_expansion (ty, ty') in
           fprintf ppf
             "This expression cannot be coerced to type@;<1 2>%a;@ it has type"
           (type_expansion ty) ty')
        (function ppf ->
           fprintf ppf "but is here used with type");
      if b then
        fprintf ppf ".@.@[<hov>%s@ %s@]"
          "This simple coercion was not fully general."
          "Consider using a double coercion."
  | Too_many_arguments (in_function, ty) ->
      reset_and_mark_loops ty;
      if in_function then begin
        fprintf ppf "This function expects too many arguments,@ ";
        fprintf ppf "it should have type@ %a"
          type_expr ty
      end else begin
        fprintf ppf "This expression should not be a function,@ ";
        fprintf ppf "the expected type is@ %a"
          type_expr ty
      end
  | Abstract_wrong_label (l, ty) ->
      let label_mark = function
        | "" -> "but its first argument is not labelled"
        |  l -> sprintf "but its first argument is labelled %s"
          (prefixed_label_name l) in
      reset_and_mark_loops ty;
      fprintf ppf "@[<v>@[<2>This function should have type@ %a@]@,%s@]"
      type_expr ty (label_mark l)
  | Scoping_let_module(id, ty) ->
      reset_and_mark_loops ty;
      fprintf ppf
       "This `let module' expression has type@ %a@ " type_expr ty;
      fprintf ppf
       "In this type, the locally bound module name %s escapes its scope" id
  | Masked_instance_variable lid ->
      fprintf ppf
        "The instance variable %a@ \
         cannot be accessed from the definition of another instance variable"
        longident lid
  | Private_type ty ->
      fprintf ppf "Cannot create values of the private type %a" type_expr ty
  | Private_label (lid, ty) ->
      fprintf ppf "Cannot assign field %a of the private type %a"
        longident lid type_expr ty
  | Not_a_variant_type lid ->
      fprintf ppf "The type %a@ is not a variant type" longident lid
  | Incoherent_label_order ->
      fprintf ppf "This function is applied to arguments@ ";
      fprintf ppf "in an order different from other calls.@ ";
      fprintf ppf "This is only allowed when the real type is known."
  | Less_general (kind, trace) ->
      report_unification_error ppf env trace
        (fun ppf -> fprintf ppf "This %s has type" kind)
        (fun ppf -> fprintf ppf "which is less general than")
  | Modules_not_allowed ->
      fprintf ppf "Modules are not allowed in this pattern."
  | Cannot_infer_signature ->
      fprintf ppf
        "The signature for this packaged module couldn't be inferred."
  | Not_a_packed_module ty ->
      fprintf ppf
        "This expression is packed module, but the expected type is@ %a"
        type_expr ty
  | Recursive_local_constraint trace ->
      report_unification_error ppf env trace
        (function ppf ->
           fprintf ppf "Recursive local constraint when unifying")
        (function ppf ->
           fprintf ppf "with")
  | Unexpected_existential ->
      fprintf ppf
        "Unexpected existential"
  | Unqualified_gadt_pattern (tpath, name) ->
      fprintf ppf "@[The GADT constructor %s of type %a@ %s.@]"
        name path tpath
        "must be qualified in this pattern"
  | Invalid_interval ->
      fprintf ppf "@[Only character intervals are supported in patterns.@]"
  | Invalid_for_loop_index ->
      fprintf ppf
        "@[Invalid for-loop index: only variables and _ are allowed.@]"
  | No_value_clauses ->
      fprintf ppf
        "None of the patterns in this 'match' expression match values."
  | Exception_pattern_below_toplevel ->
      fprintf ppf
        "@[Exception patterns must be at the top level of a match case.@]"
  | Effect_pattern_below_toplevel ->
      fprintf ppf
        "@[Effect patterns must be at the top level of a match case.@]"
  | Invalid_continuation_pattern ->
      fprintf ppf
        "@[Invalid continuation pattern: only variables and _ are allowed .@]"
  | Unexpected_continuation_pattern lid ->
      fprintf ppf
        "@[Unexpected continuation pattern: effect %a has no continuation.@]"
        longident lid
  | Missing_continuation_pattern lid ->
      fprintf ppf
        "@[Missing continuation pattern: effect %a has a continuation.@]"
        longident lid

let report_error env ppf err =
  wrap_printing_env env (fun () -> report_error env ppf err)

let () =
  Location.register_error_of_exn
    (function
      | Error (loc, env, err) ->
        Some (Location.error_of_printer loc (report_error env) err)
      | Error_forward err ->
        Some err
      | _ ->
        None
    )

let () =
  Env.add_delayed_check_forward := add_delayed_check
