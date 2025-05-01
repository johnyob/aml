open Core
open Ast_types

type core_type = core_type_desc With_range.t

and core_type_desc =
  | Type_var of Type_var_name.With_range.t
  | Type_arrow of core_type * core_type
  | Type_eq of core_type * core_type
  | Type_bot
  | Type_constr of core_type list * Type_name.With_range.t
[@@deriving sexp_of]

type core_scheme = core_scheme_desc With_range.t

and core_scheme_desc =
  { scheme_quantifiers : Type_var_name.With_range.t list
  ; scheme_body : core_type
  }
[@@deriving sexp_of]

type expression = expression_desc With_range.t

and expression_desc =
  | Exp_var of Var_name.With_range.t
  | Exp_const of constant
  | Exp_fun of Var_name.With_range.t list * expression
  | Exp_app of expression * expression
  | Exp_let of value_binding * expression
  | Exp_forall of Type_var_name.With_range.t list * expression
  | Exp_annot of expression * core_type
  | Exp_refl
  | Exp_match of expression * core_type * expression
  | Exp_absurd
[@@deriving sexp_of]

and value_binding = value_binding_desc With_range.t

and value_binding_desc =
  { value_binding_var : Var_name.With_range.t
  ; value_binding_exp : expression
  }
[@@deriving sexp_of]

type type_declaration = type_declaration_desc With_range.t

and type_declaration_desc =
  { type_decl_name : Type_name.With_range.t
  ; type_decl_params : Type_var_name.With_range.t list
  ; type_decl_kind : type_decl_kind
  }

and type_decl_kind = Type_decl_abstract [@@deriving sexp_of]

type value_description = value_description_desc With_range.t

and value_description_desc =
  { value_name : Var_name.With_range.t
  ; value_type : core_scheme
  }
[@@deriving sexp_of]

type structure_item = structure_item_desc With_range.t

and structure_item_desc =
  | Str_value of value_binding
  | Str_primitive of value_description
  | Str_type of type_declaration
[@@deriving sexp_of]

type structure = structure_item list [@@deriving sexp_of]
