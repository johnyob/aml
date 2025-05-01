open! Import
open Ast_types
module Type_ident = Constraint.Type.Ident

type type_definition =
  { type_name : Type_name.t
  ; type_ident : Type_ident.t
  ; type_arity : int (** The number of type parameters of the type. *)
  }
[@@deriving sexp_of]

type t =
  { id_source : Identifier.source
    (** [id_source] is the identifier source for any constraint variables
      created while generating constraints *)
  ; types : type_definition Type_name.Map.t
    (** [types] is a map from (user-defined) type names to type definitions.
      Each definition has a unique [type_ident]. *)
  ; type_vars : Constraint.Type.Var.t Type_var_name.Map.t
    (** [type_vars] is a renaming from (user-defined) type variables to
      constraint type variables (unique). *)
  ; vars : Constraint.Var.t Var_name.Map.t
    (** [vars] is a renaming from (user-defined) variable names to
      constraint variables (unique). *)
  }

let empty ?(id_source = Identifier.create_source ()) () =
  { id_source
  ; type_vars = Type_var_name.Map.empty
  ; types = Type_name.Map.empty
  ; vars = Var_name.Map.empty
  }
;;

let id_source t = t.id_source [@@inline]

let add_type_def t type_def =
  { t with types = Map.set t.types ~key:type_def.type_name ~data:type_def }
;;

let find_type_def t type_name = Map.find t.types type_name
let find_type_var t type_var = Map.find t.type_vars type_var
let find_var t var = Map.find t.vars var

let rename_type_var t ~type_var ~in_ =
  let ctype_var =
    Constraint.Type.Var.create
      ~id_source:t.id_source
      ~name:(type_var : Type_var_name.t :> string)
      ()
  in
  let t = { t with type_vars = Map.set t.type_vars ~key:type_var ~data:ctype_var } in
  in_ t ctype_var
;;

let rename_var t ~var ~in_ =
  let cvar =
    Constraint.Var.create ~id_source:t.id_source ~name:(var : Var_name.t :> string) ()
  in
  let t = { t with vars = Map.set t.vars ~key:var ~data:cvar } in
  in_ t cvar
;;
