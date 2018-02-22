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

(* typetexp.ml,v 1.34.4.9 2002/01/07 08:39:16 garrigue Exp *)

(* Typechecking of type expressions for the core language *)

open Asttypes
open Misc
open Parsetree
open Typedtree
open Types
open Ctype

exception Already_bound

type error =
    Unbound_type_variable of string
  | Unbound_type_constructor of Longident.t
  | Unbound_type_constructor_2 of Path.t
  (* | Unbound_effect of Longident.t *)
  | Type_arity_mismatch of Longident.t * int * int
  | Bound_type_variable of string
  | Recursive_type
  | Unbound_row_variable of Longident.t
  | Type_mismatch of (type_expr * type_expr) list
  | Alias_type_mismatch of (type_expr * type_expr) list
  | Present_has_conjunction of string
  | Present_has_no_type of string
  | Constructor_mismatch of type_expr * type_expr
  | Not_a_variant of type_expr
  | Variant_tags of string * string
  | Invalid_variable_name of string
  | Cannot_quantify of string * type_expr
  | Multiple_constraints_on_type of Longident.t
  | Repeated_method_label of string
  | Unbound_value of Longident.t
  | Unbound_constructor of Longident.t
  | Unbound_label of Longident.t
  (* | Unbound_effect_constructor of Longident.t *)
  | Unbound_module of Longident.t
  | Unbound_class of Longident.t
  | Unbound_modtype of Longident.t
  | Unbound_cltype of Longident.t
  | Ill_typed_functor_application of Longident.t
  | Illegal_reference_to_recursive_module
  | Access_functor_as_structure of Longident.t
  | Unexpected_value_type of bool
  | Unexpected_effect_type of bool
  | Unexpected_region_type of bool
  | Effect_tags of string * string


exception Error of Location.t * Env.t * error
exception Error_forward of Location.error

let string_of_cst = function
  | Const_string(s, _) -> Some s
  | _ -> None

let string_of_payload = function
  | PStr[{pstr_desc=Pstr_eval({pexp_desc=Pexp_constant c},_)}] ->
      string_of_cst c
  | _ -> None

let string_of_var name sort =
  match sort with
  | Stype -> "'" ^ name
  | Seffect -> "!" ^ name
  | Sregion -> "@" ^ name

let rec error_of_extension ext =
  match ext with
  | ({txt = ("ocaml.error"|"error") as txt; loc}, p) ->
    let rec sub_from inner =
      match inner with
      | {pstr_desc=Pstr_extension (ext, _)} :: rest ->
          error_of_extension ext :: sub_from rest
      | {pstr_loc} :: rest ->
          (Location.errorf ~loc
             "Invalid syntax for sub-error of extension '%s'." txt) ::
            sub_from rest
      | [] -> []
    in
    begin match p with
    | PStr({pstr_desc=Pstr_eval
              ({pexp_desc=Pexp_constant(Const_string(msg,_))}, _)}::
           {pstr_desc=Pstr_eval
              ({pexp_desc=Pexp_constant(Const_string(if_highlight,_))}, _)}::
           inner) ->
        Location.error ~loc ~if_highlight ~sub:(sub_from inner) msg
    | PStr({pstr_desc=Pstr_eval
              ({pexp_desc=Pexp_constant(Const_string(msg,_))}, _)}::inner) ->
        Location.error ~loc ~sub:(sub_from inner) msg
    | _ -> Location.errorf ~loc "Invalid syntax for extension '%s'." txt
    end
  | ({txt; loc}, _) ->
      Location.errorf ~loc "Uninterpreted extension '%s'." txt

let check_deprecated loc attrs s =
  List.iter
    (function
    | ({txt = "ocaml.deprecated"|"deprecated"; _}, p) ->
      begin match string_of_payload p with
      | Some txt ->
          Location.prerr_warning loc (Warnings.Deprecated (s ^ "\n" ^ txt))
      | None ->
          Location.prerr_warning loc (Warnings.Deprecated s)
      end
    | _ ->  ())
    attrs

let emit_external_warnings =
  (* Note: this is run as a preliminary pass when type-checking an
     interface or implementation.  This allows to cover all kinds of
     attributes, but the drawback is that it doesn't take local
     configuration of warnings (with '@@warning'/'@@warnerror'
     attributes) into account.  We should rather check for
     'ppwarning' attributes during the actual type-checking, making
     sure to cover all contexts (easier and more ugly alternative:
     duplicate here the logic which control warnings locally). *)
  let open Ast_mapper in
  {
    default_mapper with
    attribute = (fun _ a ->
        begin match a with
        | {txt="ocaml.ppwarning"|"ppwarning"},
          PStr[{pstr_desc=Pstr_eval({pexp_desc=Pexp_constant
                                         (Const_string (s, _))},_);
                pstr_loc}] ->
            Location.prerr_warning pstr_loc (Warnings.Preprocessor s)
        | _ -> ()
        end;
        a
      )
  }


let warning_scope = ref []

let warning_enter_scope () =
  warning_scope := (Warnings.backup ()) :: !warning_scope
let warning_leave_scope () =
  match !warning_scope with
  | [] -> assert false
  | hd :: tl ->
      Warnings.restore hd;
      warning_scope := tl

let warning_attribute attrs =
  let process loc txt errflag payload =
    match string_of_payload payload with
    | Some s ->
        begin try Warnings.parse_options errflag s
        with Arg.Bad _ ->
          Location.prerr_warning loc
            (Warnings.Attribute_payload
               (txt, "Ill-formed list of warnings"))
        end
    | None ->
        Location.prerr_warning loc
          (Warnings.Attribute_payload
             (txt, "A single string literal is expected"))
  in
  List.iter
    (function
      | ({txt = ("ocaml.warning"|"warning") as txt; loc}, payload) ->
          process loc txt false payload
      | ({txt = ("ocaml.warnerror"|"warnerror") as txt; loc}, payload) ->
          process loc txt true payload
      | _ ->
          ()
    )
    attrs

let with_warning_attribute attrs f =
  try
    warning_enter_scope ();
    warning_attribute attrs;
    let ret = f () in
    warning_leave_scope ();
    ret
  with exn ->
    warning_leave_scope ();
    raise exn

type variable_context = int * (string * type_sort, type_expr) Tbl.t

(* Local definitions *)

let instance_list = Ctype.instance_list Env.empty

(* Narrowing unbound identifier errors. *)

let rec narrow_unbound_lid_error : 'a. _ -> _ -> _ -> _ -> 'a =
  fun env loc lid make_error ->
  let check_module mlid =
    try ignore (Env.lookup_module true mlid env) with
    | Not_found ->
        narrow_unbound_lid_error env loc mlid (fun lid -> Unbound_module lid)
    | Env.Recmodule ->
        raise (Error (loc, env, Illegal_reference_to_recursive_module))
  in
  begin match lid with
  | Longident.Lident _ -> ()
  | Longident.Ldot (mlid, _) ->
      check_module mlid;
      let md = Env.find_module (Env.lookup_module true mlid env) env in
      begin match Env.scrape_alias env md.md_type with
        Mty_functor _ ->
          raise (Error (loc, env, Access_functor_as_structure mlid))
      | _ -> ()
      end
  | Longident.Lapply (flid, mlid) ->
      check_module flid;
      check_module mlid;
      raise (Error (loc, env, Ill_typed_functor_application lid))
  end;
  raise (Error (loc, env, make_error lid))

let find_component lookup make_error env loc lid =
  try
    match lid with
    | Longident.Ldot (Longident.Lident "*predef*", s) ->
        lookup (Longident.Lident s) Env.initial_safe_string
    | _ -> lookup lid env
  with Not_found ->
    narrow_unbound_lid_error env loc lid make_error
  | Env.Recmodule ->
    raise (Error (loc, env, Illegal_reference_to_recursive_module))

let find_type env loc lid =
  let (path, decl) as r =
    find_component Env.lookup_type (fun lid -> Unbound_type_constructor lid)
      env loc lid
  in
  check_deprecated loc decl.type_attributes (Path.name path);
  r

let find_constructor =
  find_component Env.lookup_constructor (fun lid -> Unbound_constructor lid)
let find_all_constructors =
  find_component Env.lookup_all_constructors
    (fun lid -> Unbound_constructor lid)
let find_label =
  find_component Env.lookup_label (fun lid -> Unbound_label lid)
let find_all_labels =
  find_component Env.lookup_all_labels (fun lid -> Unbound_label lid)

let find_class env loc lid =
  let (path, decl) as r =
    find_component Env.lookup_class (fun lid -> Unbound_class lid) env loc lid
  in
  check_deprecated loc decl.cty_attributes (Path.name path);
  r

let find_value env loc lid =
  Env.check_value_name (Longident.last lid) loc;
  let (path, decl) as r =
    find_component Env.lookup_value (fun lid -> Unbound_value lid) env loc lid
  in
  check_deprecated loc decl.val_attributes (Path.name path);
  r

(* let find_effect env loc lid =
 *   let (path, eff) as r =
 *     find_component Env.lookup_effect (fun lid -> Unbound_effect lid)
 *       env loc lid
 *   in
 *   check_deprecated loc eff.eff_attributes (Path.name path);
 *   r
 * 
 * let find_effect_constructor =
 *   find_component Env.lookup_effect_constructor
 *                  (fun lid -> Unbound_effect_constructor lid) *)

let lookup_module ?(load=false) env loc lid =
  let (path, decl) as r =
    find_component (fun lid env -> (Env.lookup_module ~load lid env, ()))
      (fun lid -> Unbound_module lid) env loc lid
  in path

let find_module env loc lid =
  let path = lookup_module ~load:true env loc lid in
  let decl = Env.find_module path env in
  check_deprecated loc decl.md_attributes (Path.name path);
  (path, decl)

let find_modtype env loc lid =
  let (path, decl) as r =
    find_component Env.lookup_modtype (fun lid -> Unbound_modtype lid)
      env loc lid
  in
  check_deprecated loc decl.mtd_attributes (Path.name path);
  r

let find_class_type env loc lid =
  let (path, decl) as r =
    find_component Env.lookup_cltype (fun lid -> Unbound_cltype lid)
      env loc lid
  in
  check_deprecated loc decl.clty_attributes (Path.name path);
  r

let unbound_constructor_error env lid =
  narrow_unbound_lid_error env lid.loc lid.txt
    (fun lid -> Unbound_constructor lid)

let unbound_label_error env lid =
  narrow_unbound_lid_error env lid.loc lid.txt
    (fun lid -> Unbound_label lid)

(* Support for first-class modules. *)

let transl_modtype_longident = ref (fun _ -> assert false)
let transl_modtype = ref (fun _ -> assert false)

let create_package_mty fake loc env (p, l) =
  let l =
    List.sort
      (fun (s1, t1) (s2, t2) ->
         if s1.txt = s2.txt then
           raise (Error (loc, env, Multiple_constraints_on_type s1.txt));
         compare s1.txt s2.txt)
      l
  in
  l,
  List.fold_left
    (fun mty (s, t) ->
      let d = {ptype_name = mkloc (Longident.last s.txt) s.loc;
               ptype_params = [];
               ptype_cstrs = [];
               ptype_sort = Type;
               ptype_kind = Ptype_abstract;
               ptype_private = Asttypes.Public;
               ptype_manifest = if fake then None else Some t;
               ptype_attributes = [];
               ptype_loc = loc} in
      Ast_helper.Mty.mk ~loc
        (Pmty_with (mty, [ Pwith_type ({ txt = s.txt; loc }, d) ]))
    )
    (Ast_helper.Mty.mk ~loc (Pmty_ident p))
    l

(* Translation of type expressions *)

let type_variables =
  ref (Tbl.empty : (string * type_sort, type_expr) Tbl.t)
let univars        = ref ([] : ((string * type_sort) * type_expr) list)
let pre_univars    = ref ([] : type_expr list)
let used_variables =
  ref (Tbl.empty : (string * type_sort, type_expr * Location.t) Tbl.t)

let reset_type_variables () =
  reset_global_level ();
  type_variables := Tbl.empty

let narrow () =
  (increase_global_level (), !type_variables)

let widen (gl, tv) =
  restore_global_level gl;
  type_variables := tv

let strict_lowercase c = (c = '_' || c >= 'a' && c <= 'z')

let validate_name = function
    None -> None
  | Some name as s ->
      if name <> "" && strict_lowercase name.[0] then s else None

let new_global_var ?name sort =
  new_global_var ?name:(validate_name name) sort
let newvar ?name sort =
  newvar ?name:(validate_name name) sort

let transl_sort = function
  | Type -> Stype
  | Effect -> Seffect
  | Region -> Sregion

let approx_type_param (styp, _) =
  match styp.ptyp_desc with
  | Ptyp_any -> Btype.newgenvar Stype
  | Ptyp_var(_, ssort) -> Btype.newgenvar (transl_sort ssort)
  | _ -> assert false

let transl_type_param env styp =
  let loc = styp.ptyp_loc in
  match styp.ptyp_desc with
    Ptyp_any ->
      let ty = new_global_var ~name:"_" Stype in
        { ctyp_desc = Ttyp_any; ctyp_type = ty; ctyp_env = env;
          ctyp_loc = loc; ctyp_attributes = styp.ptyp_attributes; }
  | Ptyp_var(name, ssort) ->
      let sort = transl_sort ssort in
      let key = (name, sort) in
      let ty =
        try
          if name <> "" && name.[0] = '_' then begin
            let s = string_of_var name sort in
            raise (Error (loc, Env.empty, Invalid_variable_name s))
          end;
          ignore (Tbl.find key !type_variables);
          raise Already_bound
        with Not_found ->
          let v = new_global_var ~name sort in
            type_variables := Tbl.add key v !type_variables;
            v
      in
        { ctyp_desc = Ttyp_var(name, ssort); ctyp_type = ty; ctyp_env = env;
          ctyp_loc = loc; ctyp_attributes = styp.ptyp_attributes; }
  | _ -> assert false

let wrap_method ty =
  match (Ctype.repr ty).desc with
    Tpoly _ -> ty
  | _ -> Ctype.newty (Tpoly (ty, []))

let new_pre_univar ?name sort =
  let v = newvar ?name sort in pre_univars := v :: !pre_univars; v

let rec swap_list = function
    x :: y :: l -> y :: x :: swap_list l
  | l -> l

let check_sort loc env expected_sort sort =
  match expected_sort, sort with
  | None, _ -> ()
  | Some Seffect, Seffect -> ()
  | Some Stype, Stype -> ()
  | Some Sregion, Sregion -> ()
  | Some Seffect, Stype ->
      raise (Error (loc, env, Unexpected_value_type true))
  | Some Seffect, Sregion ->
      raise (Error (loc, env, Unexpected_region_type false))
  | Some Stype, Seffect ->
      raise (Error (loc, env, Unexpected_effect_type true))
  | Some Stype, Sregion ->
      raise (Error (loc, env, Unexpected_region_type true))
  | Some Sregion, Seffect ->
      raise (Error (loc, env, Unexpected_effect_type false))
  | Some Sregion, Stype ->
      raise (Error (loc, env, Unexpected_value_type false))


type policy = Fixed | Extensible | Univars

let rec transl_type env policy expected_sort (styp : Parsetree.core_type) : Typedtree.core_type =
  let loc = styp.ptyp_loc in
  let ctyp ctyp_desc ctyp_type =
    { ctyp_desc; ctyp_type; ctyp_env = env;
      ctyp_loc = loc; ctyp_attributes = styp.ptyp_attributes }
  in
  match styp.ptyp_desc with
  | Ptyp_any ->
      let sort =
        match expected_sort with
        | None -> Stype
        | Some sort -> sort
      in
      let ty =
        if policy = Univars then new_pre_univar sort else
          if policy = Fixed then
            raise (Error (styp.ptyp_loc, env, Unbound_type_variable "_"))
          else newvar sort
      in
      ctyp Ttyp_any ty
  | Ptyp_var(name, ssort) ->
    let sort = transl_sort ssort in
    check_sort styp.ptyp_loc env expected_sort sort;
    let key = (name, sort) in
    let ty =
      if name <> "" && name.[0] = '_' then begin
        let s = string_of_var name sort in
        raise (Error (styp.ptyp_loc, env, Invalid_variable_name s))
      end;
      begin try
        instance env (List.assoc key !univars)
      with Not_found -> try
        instance env (fst(Tbl.find key !used_variables))
      with Not_found ->
        let v =
          if policy = Univars then new_pre_univar ~name sort
          else newvar ~name sort
        in
        used_variables :=
          Tbl.add key (v, styp.ptyp_loc) !used_variables;
        v
      end
    in
    ctyp (Ttyp_var(name, ssort)) ty
  | Ptyp_arrow(l, st1, seft, st2) ->
    check_sort styp.ptyp_loc env expected_sort Stype;
    let cty1 = transl_type env policy (Some Stype) st1 in
    let eft = transl_effect_type env policy seft in
    let cty2 = transl_type env policy (Some Stype) st2 in
    let ty =
      newty (Tarrow(l, cty1.ctyp_type, eft.eft_type, cty2.ctyp_type, Cok))
    in
    ctyp (Ttyp_arrow (l, cty1, eft, cty2)) ty
  | Ptyp_tuple stl ->
    if List.length stl < 2 then
      Syntaxerr.ill_formed_ast loc "Tuples must have at least 2 components.";
    check_sort styp.ptyp_loc env expected_sort Stype;
    let ctys = List.map (transl_type env policy (Some Stype)) stl in
    let ty = newty (Ttuple (List.map (fun ctyp -> ctyp.ctyp_type) ctys)) in
    ctyp (Ttyp_tuple ctys) ty
  | Ptyp_constr(lid, stl) ->
      let (path, decl) = find_type env styp.ptyp_loc lid.txt in
      check_sort styp.ptyp_loc env expected_sort decl.type_sort;
      let stl =
        match stl with
        | [ {ptyp_desc=Ptyp_any} as t ] when decl.type_arity > 1 ->
            List.map (fun _ -> t) decl.type_params
        | _ -> stl
      in
      if List.length stl <> decl.type_arity then
        raise(Error(styp.ptyp_loc, env,
                    Type_arity_mismatch(lid.txt, decl.type_arity,
                                        List.length stl)));
      let param_sorts =
        List.map (fun ty -> Some (Btype.type_sort ty)) decl.type_params
      in
      let args = List.map2 (transl_type env policy) param_sorts stl in
      let params = instance_list decl.type_params in
      let unify_param =
        match decl.type_manifest with
          None -> unify_var
        | Some ty ->
            if (repr ty).level = Btype.generic_level then unify_var else unify
      in
      List.iter2
        (fun (sty, cty) ty' ->
           try unify_param env ty' cty.ctyp_type with Unify trace ->
             raise (Error(sty.ptyp_loc, env, Type_mismatch (swap_list trace))))
        (List.combine stl args) params;
      let constr_args = List.map (fun ctyp -> ctyp.ctyp_type) args in
      let constr = newconstr path constr_args decl.type_sort in
      begin try
        Ctype.enforce_constraints env constr
      with Unify trace ->
        raise (Error(styp.ptyp_loc, env, Type_mismatch trace))
      end;
      ctyp (Ttyp_constr (path, lid, args)) constr
  | Ptyp_object (fields, o) ->
      check_sort styp.ptyp_loc env expected_sort Stype;
      let fields =
        List.map (fun (s, a, t) -> (s, a, transl_poly_type env policy t))
          fields
      in
      let ty = newobj (transl_fields loc env policy [] o fields) in
      ctyp (Ttyp_object (fields, o)) ty
  | Ptyp_class(lid, stl) ->
      check_sort styp.ptyp_loc env expected_sort Stype;
      let (path, decl, is_variant) =
        try
          let (path, decl) = Env.lookup_type lid.txt env in
          let rec check decl =
            match decl.type_manifest with
              None -> raise Not_found
            | Some ty ->
                match (repr ty).desc with
                  Tvariant row when Btype.static_row row -> ()
                | Tconstr (path, _, _, _) ->
                    check (Env.find_type path env)
                | _ -> raise Not_found
          in check decl;
          Location.prerr_warning styp.ptyp_loc
            (Warnings.Deprecated "old syntax for polymorphic variant type");
          (path, decl,true)
        with Not_found -> try
          let lid2 =
            match lid.txt with
              Longident.Lident s     -> Longident.Lident ("#" ^ s)
            | Longident.Ldot(r, s)   -> Longident.Ldot (r, "#" ^ s)
            | Longident.Lapply(_, _) -> fatal_error "Typetexp.transl_type"
          in
          let (path, decl) = Env.lookup_type lid2 env in
          (path, decl, false)
        with Not_found ->
          ignore (find_class env styp.ptyp_loc lid.txt); assert false
      in
      if List.length stl <> decl.type_arity then
        raise(Error(styp.ptyp_loc, env,
                    Type_arity_mismatch(lid.txt, decl.type_arity,
                                        List.length stl)));
      let args = List.map (transl_type env policy (Some Stype)) stl in
      let params = instance_list decl.type_params in
      List.iter2
        (fun (sty, cty) ty' ->
           try unify_var env ty' cty.ctyp_type with Unify trace ->
             raise (Error(sty.ptyp_loc, env, Type_mismatch (swap_list trace))))
        (List.combine stl args) params;
        let ty_args = List.map (fun ctyp -> ctyp.ctyp_type) args in
      let ty =
        try Ctype.expand_head env (newconstr path ty_args decl.type_sort)
        with Unify trace ->
          raise (Error(styp.ptyp_loc, env, Type_mismatch trace))
      in
      let ty = match ty.desc with
        Tvariant row ->
          let row = Btype.row_repr row in
          let fields =
            List.map
              (fun (l,f) -> l,
                match Btype.row_field_repr f with
                | Rpresent (Some ty) ->
                    Reither(false, [ty], false, ref None)
                | Rpresent None ->
                    Reither (true, [], false, ref None)
                | _ -> f)
              row.row_fields
          in
          let row = { row_closed = true; row_fields = fields;
                      row_bound = (); row_name = Some (path, ty_args);
                      row_fixed = false; row_more = newvar Stype } in
          let static = Btype.static_row row in
          let row =
            if static then { row with row_more = newty Tnil }
            else if policy <> Univars then row
            else { row with row_more = new_pre_univar Stype }
          in
          newty (Tvariant row)
      | Tobject (fi, _) ->
          let _, tv = flatten_fields fi in
          if policy = Univars then pre_univars := tv :: !pre_univars;
          ty
      | _ ->
          assert false
      in
      ctyp (Ttyp_class (path, lid, args)) ty
  | Ptyp_alias(st, alias, ssort) ->
      let sort = transl_sort ssort in
      check_sort styp.ptyp_loc env expected_sort sort;
      let cty =
        let key = (alias, sort) in
        try
          let t =
            try List.assoc key !univars
            with Not_found ->
              instance env (fst(Tbl.find key !used_variables))
          in
          let ty = transl_type env policy (Some sort) st in
          begin try unify_var env t ty.ctyp_type with Unify trace ->
            let trace = swap_list trace in
            raise(Error(styp.ptyp_loc, env, Alias_type_mismatch trace))
          end;
          ty
        with Not_found ->
          if !Clflags.principal then begin_def ();
          let t = newvar sort in
          used_variables :=
            Tbl.add key (t, styp.ptyp_loc) !used_variables;
          let ty = transl_type env policy (Some sort) st in
          begin try unify_var env t ty.ctyp_type with Unify trace ->
            let trace = swap_list trace in
            raise(Error(styp.ptyp_loc, env, Alias_type_mismatch trace))
          end;
          if !Clflags.principal then begin
            end_def ();
            generalize_structure t;
          end;
          let t = instance env t in
          let px = Btype.proxy t in
          begin match px.desc with
          | Tvar(None, sort) ->
              Btype.log_type px; px.desc <- Tvar (Some alias, sort)
          | Tunivar(None, sort) ->
              Btype.log_type px; px.desc <- Tunivar (Some alias, sort)
          | _ -> ()
          end;
          { ty with ctyp_type = t }
      in
      ctyp (Ttyp_alias (cty, alias, ssort)) cty.ctyp_type
  | Ptyp_variant(fields, closed, present) ->
      check_sort styp.ptyp_loc env expected_sort Stype;
      let name = ref None in
      let mkfield l f =
        newty (Tvariant {row_fields=[l,f]; row_more=newvar Stype;
                         row_bound=(); row_closed=true;
                         row_fixed=false; row_name=None}) in
      let hfields = Hashtbl.create 17 in
      let add_typed_field loc l f =
        let h = Btype.hash_variant l in
        try
          let (l',f') = Hashtbl.find hfields h in
          (* Check for tag conflicts *)
          if l <> l' then raise(Error(styp.ptyp_loc, env, Variant_tags(l, l')));
          let ty = mkfield l f and ty' = mkfield l f' in
          if equal env false [ty] [ty'] then () else
          try unify env ty ty'
          with Unify trace ->
            raise(Error(loc, env, Constructor_mismatch (ty,ty')))
        with Not_found ->
          Hashtbl.add hfields h (l,f)
      in
      let add_field = function
          Rtag (l, attrs, c, stl) ->
            name := None;
            let tl = List.map (transl_type env policy (Some Stype)) stl in
            let f = match present with
              Some present when not (List.mem l present) ->
                let ty_tl = List.map (fun cty -> cty.ctyp_type) tl in
                Reither(c, ty_tl, false, ref None)
            | _ ->
                if List.length stl > 1 || c && stl <> [] then
                  raise(Error(styp.ptyp_loc, env, Present_has_conjunction l));
                match tl with [] -> Rpresent None
                | st :: _ ->
                      Rpresent (Some st.ctyp_type)
            in
            add_typed_field styp.ptyp_loc l f;
              Ttag (l,attrs,c,tl)
        | Rinherit sty ->
            let cty = transl_type env policy (Some Stype) sty in
            let ty = cty.ctyp_type in
            let nm =
              match repr cty.ctyp_type with
                {desc=Tconstr(p, tl, _, _)} -> Some(p, tl)
              | _                        -> None
            in
            begin try
              (* Set name if there are no fields yet *)
              Hashtbl.iter (fun _ _ -> raise Exit) hfields;
              name := nm
            with Exit ->
              (* Unset it otherwise *)
              name := None
            end;
            let fl = match expand_head env cty.ctyp_type, nm with
              {desc=Tvariant row}, _ when Btype.static_row row ->
                let row = Btype.row_repr row in
                row.row_fields
            | {desc=Tvar _}, Some(p, _) ->
                raise(Error(sty.ptyp_loc, env, Unbound_type_constructor_2 p))
            | _ ->
                raise(Error(sty.ptyp_loc, env, Not_a_variant ty))
            in
            List.iter
              (fun (l, f) ->
                let f = match present with
                  Some present when not (List.mem l present) ->
                    begin match f with
                      Rpresent(Some ty) ->
                        Reither(false, [ty], false, ref None)
                    | Rpresent None ->
                        Reither(true, [], false, ref None)
                    | _ ->
                        assert false
                    end
                | _ -> f
                in
                add_typed_field sty.ptyp_loc l f)
              fl;
              Tinherit cty
      in
      let tfields = List.map add_field fields in
      let fields = Hashtbl.fold (fun _ p l -> p :: l) hfields [] in
      begin match present with None -> ()
      | Some present ->
          List.iter
            (fun l -> if not (List.mem_assoc l fields) then
              raise(Error(styp.ptyp_loc, env, Present_has_no_type l)))
            present
      end;
      let row =
        { row_fields = List.rev fields; row_more = newvar Stype;
          row_bound = (); row_closed = (closed = Closed);
          row_fixed = false; row_name = !name } in
      let static = Btype.static_row row in
      let row =
        if static then { row with row_more = newty Tnil }
        else if policy <> Univars then row
        else { row with row_more = new_pre_univar Stype }
      in
      let ty = newty (Tvariant row) in
      ctyp (Ttyp_variant (tfields, closed, present)) ty
   | Ptyp_poly(vars, st) ->
      check_sort styp.ptyp_loc env expected_sort Stype;
      begin_def();
      let new_univars =
        List.map
          (fun (name, sort) ->
            let sort = transl_sort sort in
            (name, sort), newvar ~name sort)
          vars
      in
      let old_univars = !univars in
      univars := new_univars @ !univars;
      let cty = transl_type env policy (Some Stype) st in
      let ty = cty.ctyp_type in
      univars := old_univars;
      end_def();
      generalize ty;
      let ty_list =
        List.fold_left
          (fun tyl ((name, sort), ty1) ->
            let v = Btype.proxy ty1 in
            if deep_occur v ty then begin
              match v.desc with
              | Tvar(name, sort) when v.level = Btype.generic_level ->
                  v.desc <- Tunivar(name, sort);
                  v :: tyl
              | _ ->
                let s = string_of_var name sort in
                raise (Error (styp.ptyp_loc, env, Cannot_quantify (s, v)))
            end else tyl)
          [] new_univars
      in
      let ty' = Btype.newgenty (Tpoly(ty, List.rev ty_list)) in
      unify_var env (newvar Stype) ty';
      ctyp (Ttyp_poly (vars, cty)) ty'
  | Ptyp_package (p, l) ->
      check_sort styp.ptyp_loc env expected_sort Stype;
      let l, mty = create_package_mty true styp.ptyp_loc env (p, l) in
      let z = narrow () in
      let mty = !transl_modtype env mty in
      widen z;
      let ptys = List.map (fun (s, pty) ->
                             s, transl_type env policy (Some Stype) pty
                          ) l in
      let path = !transl_modtype_longident styp.ptyp_loc env p.txt in
      let ty = newty (Tpackage (path,
                       List.map (fun (s, pty) -> s.txt) l,
                       List.map (fun (_,cty) -> cty.ctyp_type) ptys))
      in
      ctyp (Ttyp_package {
            pack_path = path;
            pack_type = mty.mty_type;
            pack_fields = ptys;
            pack_txt = p;
           }) ty
  | Ptyp_effect desc ->
      check_sort styp.ptyp_loc env expected_sort Seffect;
      let efr = transl_effect_row env policy desc in
      ctyp (Ttyp_effect efr) efr.efr_type
  | Ptyp_extension ext ->
      raise (Error_forward (error_of_extension ext))

and transl_poly_type env policy t =
  transl_type env policy (Some Stype) (Ast_helper.Typ.force_poly t)

and transl_fields loc env policy seen o =
  function
    [] ->
      begin match o, policy with
      | Closed, _ -> newty Tnil
      | Open, Univars -> new_pre_univar Stype
      | Open, _ -> newvar Stype
      end
  | (s, _attrs, ty1) :: l ->
      if List.mem s seen then raise (Error (loc, env, Repeated_method_label s));
      let ty2 = transl_fields loc env policy (s :: seen) o l in
      newty (Tfield (s, Fpresent, ty1.ctyp_type, ty2))

and transl_effect_row_with_tail env policy row tail =
  let hfields = Hashtbl.create 17 in
  let transl_effect_constructor env policy constr =
    let loc = Location.none in (* TODO: FIXME effect_constructor in parsetree.mli does not carry location information *)
    let lbl = constr.peff_label in
    let () =
      let h = Btype.hash_variant lbl in
      match Hashtbl.find hfields h with
      | lbl' ->
          if lbl <> lbl' then raise(Error(loc, env, Effect_tags(lbl, lbl')))
      | exception Not_found ->
          Hashtbl.add hfields h lbl
    in
    let transl_type env policy sty =
      let cty = transl_type env policy None sty in
      cty
    in
    { ec_label = constr.peff_label;
      ec_args = List.map (transl_type env policy) constr.peff_args;
      ec_res  = Misc.may_map (transl_type env policy) constr.peff_res;
      ec_loc = loc;
      ec_attributes = constr.peff_attributes; }
  in
  let tefr_effects =
    List.map (transl_effect_constructor env policy) row.pefr_effects
  in
  let tefr_next, row =
    match row.pefr_next with
    | None -> None, tail
    | Some styp ->
        let typ = transl_type env policy (Some Seffect) styp in
        Some typ, typ.ctyp_type
  in
  let tefr_type =
    List.fold_right
      (fun ec tail ->
        let tyec =
          { ec_label = ec.Typedtree.ec_label;
            ec_args = List.map (fun ctyp -> ctyp.ctyp_type) ec.ec_args;
            ec_res  = Misc.may_map (fun ctyp -> ctyp.ctyp_type) ec.ec_res; }
        in
        newty (Teffect(Eordinary tyec, tail)))
      tefr_effects row
  in
  { efr_effects = tefr_effects;
    efr_type = tefr_type;
    efr_next = tefr_next }

and transl_effect_row env policy row =
  let tail = newty Tenil in
  transl_effect_row_with_tail env policy row tail

and transl_tilde env loc policy =
  let name = "~" in
  let sort = Seffect in
  let key = (name, sort) in
  try
    instance env (List.assoc key !univars)
  with Not_found -> try
    instance env (fst(Tbl.find key !used_variables))
  with Not_found ->
    let v =
      if policy = Univars then new_pre_univar ~name sort
      else newvar ~name sort
    in
    used_variables :=
      Tbl.add key (v, loc) !used_variables;
    v

and transl_effect_type env policy seft =
  let tail =
    if seft.peft_tilde then
      transl_tilde env seft.peft_loc policy
    else
      newty Tenil
  in
  let teft_row, tail =
    match seft.peft_row with
    | None -> None, tail
    | Some sefr ->
       let tefr = transl_effect_row_with_tail env policy sefr tail in
       Some tefr, tefr.efr_type
  in
  let ty =
    if seft.peft_io then
      instance_def (effect_io tail)
    else
      tail
  in
  { eft_io = seft.peft_io;
    eft_tilde = seft.peft_tilde;
    eft_type = ty;
    eft_row = teft_row;
    eft_loc = Location.none (* TODO: FIXME *) }

(* Make the rows "fixed" in this type, to make universal check easier *)
let rec make_fixed_univars ty =
  let ty = repr ty in
  if ty.level >= Btype.lowest_level then begin
    Btype.mark_type_node ty;
    match ty.desc with
    | Tvariant row ->
        let row = Btype.row_repr row in
        if Btype.is_Tunivar (Btype.row_more row) then
          ty.desc <- Tvariant
              {row with row_fixed=true;
               row_fields = List.map
                 (fun (s,f as p) -> match Btype.row_field_repr f with
                   Reither (c, tl, m, r) -> s, Reither (c, tl, true, r)
                 | _ -> p)
                 row.row_fields};
        Btype.iter_row make_fixed_univars row
    | _ ->
        Btype.iter_type_expr make_fixed_univars ty
  end

let make_fixed_univars ty =
  make_fixed_univars ty;
  Btype.unmark_type ty

let create_package_mty = create_package_mty false

let globalize_used_variables env fixed =
  let r = ref [] in
  Tbl.iter
    (fun ((name, sort) as key) (ty, loc) ->
      let v = new_global_var sort in
      let snap = Btype.snapshot () in
      if try unify env v ty; true with _ -> Btype.backtrack snap; false
      then begin
        try
          r := (loc, v,  Tbl.find key !type_variables) :: !r
        with Not_found ->
          if fixed && Btype.is_Tvar (repr ty) then begin
            let s = string_of_var name sort in
            raise(Error(loc, env, Unbound_type_variable s))
          end;
          let v2 = new_global_var sort in
          r := (loc, v, v2) :: !r;
          type_variables := Tbl.add key v2 !type_variables
      end)
    !used_variables;
  used_variables := Tbl.empty;
  fun () ->
    List.iter
      (function (loc, t1, t2) ->
        try unify env t1 t2 with Unify trace ->
          raise (Error(loc, env, Type_mismatch trace)))
      !r

let transl_simple_type env fixed expected_sort styp =
  univars := []; used_variables := Tbl.empty;
  let typ =
    transl_type env (if fixed then Fixed else Extensible) expected_sort styp
  in
  globalize_used_variables env fixed ();
  make_fixed_univars typ.ctyp_type;
  typ

let transl_simple_type_univars env expected_sort styp =
  univars := []; used_variables := Tbl.empty; pre_univars := [];
  begin_def ();
  let typ = transl_type env Univars expected_sort styp in
  (* Only keep already global variables in used_variables *)
  let new_variables = !used_variables in
  used_variables := Tbl.empty;
  Tbl.iter
    (fun key p ->
      if Tbl.mem key !type_variables then
        used_variables := Tbl.add key p !used_variables)
    new_variables;
  globalize_used_variables env false ();
  end_def ();
  generalize typ.ctyp_type;
  let univs =
    List.fold_left
      (fun acc v ->
        let v = repr v in
        match v.desc with
          Tvar(name, sort) when v.level = Btype.generic_level ->
            v.desc <- Tunivar(name, sort); v :: acc
        | _ -> acc)
      [] !pre_univars
  in
  make_fixed_univars typ.ctyp_type;
    { typ with ctyp_type =
        instance env (Btype.newgenty (Tpoly (typ.ctyp_type, univs))) }

let transl_simple_type_delayed env expected_sort styp =
  univars := []; used_variables := Tbl.empty;
  let typ = transl_type env Extensible expected_sort styp in
  make_fixed_univars typ.ctyp_type;
  (typ, globalize_used_variables env false)

let transl_type_scheme env expected_sort styp =
  reset_type_variables();
  begin_def();
  let typ = transl_simple_type env false expected_sort styp in
  end_def();
  generalize typ.ctyp_type;
  typ


(* Error report *)

open Format
open Printtyp

let spellcheck ppf fold env lid =
  let cutoff =
    match String.length (Longident.last lid) with
      | 1 | 2 -> 0
      | 3 | 4 -> 1
      | 5 | 6 -> 2
      | _ -> 3
  in
  let compare target head acc =
    let (best_choice, best_dist) = acc in
    match Misc.edit_distance target head cutoff with
      | None -> (best_choice, best_dist)
      | Some dist ->
        let choice =
          if dist < best_dist then [head]
          else if dist = best_dist then head :: best_choice
          else best_choice in
        (choice, min dist best_dist)
  in
  let init = ([], max_int) in
  let handle (choice, _dist) =
    match List.rev choice with
      | [] -> ()
      | last :: rev_rest ->
        fprintf ppf "@\nHint: Did you mean %s%s%s?"
          (String.concat ", " (List.rev rev_rest))
          (if rev_rest = [] then "" else " or ")
          last
  in
  (* flush now to get the error report early, in the (unheard of) case
     where the linear search would take a bit of time; in the worst
     case, the user has seen the error, she can interrupt the process
     before the spell-checking terminates. *)
  fprintf ppf "@?";
  match lid with
    | Longident.Lapply _ -> ()
    | Longident.Lident s ->
      handle (fold (compare s) None env init)
    | Longident.Ldot (r, s) ->
      handle (fold (compare s) (Some r) env init)

let spellcheck_simple ppf fold extr =
  spellcheck ppf (fun f -> fold (fun decl x -> f (extr decl) x))

let spellcheck ppf fold =
  spellcheck ppf (fun f -> fold (fun s _ _ x -> f s x))

type cd = string list * int

let report_error env ppf = function
  | Unbound_type_variable name ->
    fprintf ppf "Unbound type parameter %s@." name
  | Unbound_type_constructor lid ->
    fprintf ppf "Unbound type constructor %a" longident lid;
    spellcheck ppf Env.fold_types env lid;
  | Unbound_type_constructor_2 p ->
    fprintf ppf "The type constructor@ %a@ is not yet completely defined"
      path p
  (* | Unbound_effect lid ->
   *   fprintf ppf "Unbound effect %a" longident lid;
   *   spellcheck ppf Env.fold_effects env lid; *)
  | Type_arity_mismatch(lid, expected, provided) ->
    fprintf ppf
      "@[The type constructor %a@ expects %i argument(s),@ \
        but is here applied to %i argument(s)@]"
      longident lid expected provided
  | Bound_type_variable name ->
    fprintf ppf "Already bound type parameter '%s" name
  | Recursive_type ->
    fprintf ppf "This type is recursive"
  | Unbound_row_variable lid ->
      (* we don't use "spellcheck" here: this error is not raised
         anywhere so it's unclear how it should be handled *)
      fprintf ppf "Unbound row variable in #%a" longident lid
  | Type_mismatch trace ->
      Printtyp.report_unification_error ppf Env.empty trace
        (function ppf ->
           fprintf ppf "This type")
        (function ppf ->
           fprintf ppf "should be an instance of type")
  | Alias_type_mismatch trace ->
      Printtyp.report_unification_error ppf Env.empty trace
        (function ppf ->
           fprintf ppf "This alias is bound to type")
        (function ppf ->
           fprintf ppf "but is used as an instance of type")
  | Present_has_conjunction l ->
      fprintf ppf "The present constructor %s has a conjunctive type" l
  | Present_has_no_type l ->
      fprintf ppf "The present constructor %s has no type" l
  | Constructor_mismatch (ty, ty') ->
      wrap_printing_env env (fun ()  ->
        Printtyp.reset_and_mark_loops_list [ty; ty'];
        fprintf ppf "@[<hov>%s %a@ %s@ %a@]"
          "This variant type contains a constructor"
          Printtyp.type_expr ty
          "which should be"
          Printtyp.type_expr ty')
  | Not_a_variant ty ->
      Printtyp.reset_and_mark_loops ty;
      fprintf ppf "@[The type %a@ is not a polymorphic variant type@]"
        Printtyp.type_expr ty
  | Variant_tags (lab1, lab2) ->
      fprintf ppf
        "@[Variant tags `%s@ and `%s have the same hash value.@ %s@]"
        lab1 lab2 "Change one of them."
  | Invalid_variable_name name ->
      fprintf ppf "The type variable name %s is not allowed in programs" name
  | Cannot_quantify (name, v) ->
      fprintf ppf
        "@[<hov>The universal type variable %s cannot be generalized:@ %s.@]"
        name
        (if Btype.is_Tvar v then "it escapes its scope" else
         if Btype.is_Tunivar v then "it is already bound to another variable"
         else "it is not a variable")
  | Multiple_constraints_on_type s ->
      fprintf ppf "Multiple constraints for type %a" longident s
  | Repeated_method_label s ->
      fprintf ppf "@[This is the second method `%s' of this object type.@ %s@]"
        s "Multiple occurences are not allowed."
  | Unbound_value lid ->
      fprintf ppf "Unbound value %a" longident lid;
      spellcheck ppf Env.fold_values env lid;
  | Unbound_module lid ->
      fprintf ppf "Unbound module %a" longident lid;
      spellcheck ppf Env.fold_modules env lid;
  | Unbound_constructor lid ->
      fprintf ppf "Unbound constructor %a" longident lid;
      spellcheck_simple ppf Env.fold_constructors (fun d -> d.cstr_name)
        env lid;
  | Unbound_label lid ->
      fprintf ppf "Unbound record field %a" longident lid;
      spellcheck_simple ppf Env.fold_labels (fun d -> d.lbl_name) env lid;
  (* | Unbound_effect_constructor lid ->
   *     fprintf ppf "Unbound effect constructor %a" longident lid;
   *     spellcheck_simple ppf Env.fold_effect_constructors (fun d -> d.ecstr_name)
   *       env lid; *)
  | Unbound_class lid ->
      fprintf ppf "Unbound class %a" longident lid;
      spellcheck ppf Env.fold_classs env lid;
  | Unbound_modtype lid ->
      fprintf ppf "Unbound module type %a" longident lid;
      spellcheck ppf Env.fold_modtypes env lid;
  | Unbound_cltype lid ->
      fprintf ppf "Unbound class type %a" longident lid;
      spellcheck ppf Env.fold_cltypes env lid;
  | Ill_typed_functor_application lid ->
      fprintf ppf "Ill-typed functor application %a" longident lid
  | Illegal_reference_to_recursive_module ->
      fprintf ppf "Illegal recursive module reference"
  | Access_functor_as_structure lid ->
      fprintf ppf "The module %a is a functor, not a structure" longident lid
  | Unexpected_value_type e ->
      fprintf ppf "This is a value type but %s type was expected"
              (if e then "an effect" else "a region")
  | Unexpected_effect_type v ->
      fprintf ppf "This is an effect type but a %s type was expected"
              (if v then "value" else "region")
  | Unexpected_region_type v ->
      fprintf ppf "This is a region type but %s type was expected"
              (if v then "a value" else "an effect")
  | Effect_tags (lab1, lab2) ->
      fprintf ppf
        "@[Effect constructors `%s@ and `%s have the same hash value.@ %s@]"
        lab1 lab2 "Change one of them."


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
