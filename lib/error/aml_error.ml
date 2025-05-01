open Core
open Grace
open Aml_ast.Ast_types

let am_running_inline_or_expect_test () =
  am_running_test || Ppx_expect_runtime.For_external.am_running_expect_test ()
;;

module Code = struct
  type t =
    | Unterminated_comment
    | Unknown_start_of_token
    | Syntax_error
    | Unbound_variable
    | Unbound_type_variable
    | Unbound_type_name
    | Type_constructor_arity_mismatch
    | Type_mismatch
    | Rigid_variable_escape
    | Scope_escape
    | Unexpected_consistent_context
    | Unknown
  [@@deriving sexp]

  let to_string = function
    | Unterminated_comment -> "E001"
    | Unknown_start_of_token -> "E002"
    | Syntax_error -> "E003"
    | Unbound_variable -> "E004"
    | Unbound_type_variable -> "E005"
    | Unbound_type_name -> "E006"
    | Type_constructor_arity_mismatch -> "E007"
    | Type_mismatch -> "E008"
    | Rigid_variable_escape -> "E009"
    | Scope_escape -> "E010"
    | Unexpected_consistent_context -> "E011"
    | Unknown -> "E???"
  ;;
end

type t = Code.t Diagnostic.t [@@deriving sexp]

exception T of t

let raise t = raise (T t) [@@always_inline]

let pp ppf t =
  let open Grace_ansi_renderer in
  let config =
    { Config.default with use_ansi = not (am_running_inline_or_expect_test ()) }
  in
  Grace_ansi_renderer.pp_diagnostic ~config ~code_to_string:Code.to_string () ppf t
;;

let handle_uncaught ~exit:should_exit f =
  try f () with
  | T err ->
    Fmt.(pf stderr "@[%a@]@." pp err);
    if should_exit && not (am_running_inline_or_expect_test ()) then exit 1
;;

(* Constructors for errors *)

let empty_primary_label ~range = Diagnostic.Label.primaryf ~range ""

let bug ~here msg =
  Diagnostic.(
    create
      ~code:Code.Unknown
      Bug
      (Message.createf "%s: %a" (Source_code_position.to_string here) Message.pp msg))
;;

let bugf ~here fmt = fmt |> Diagnostic.Message.kcreatef (bug ~here)
let bug_s ~here sexp = bugf ~here "%a" Sexp.pp_hum sexp

let unterminated_comment ~range : t =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Unterminated_comment
    Error
    "unterminated comment"
;;

let unknown_start_of_token ~range c : t =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Unknown_start_of_token
    Error
    "unknown start of token: %C"
    c
;;

let syntax_error ~range : t =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Syntax_error
    Error
    "syntax error"
;;

let not_found_in_this_scope_label ~range =
  Diagnostic.Label.primaryf ~range "not found in this scope"
;;

let pp_quoted pp ppf x = Fmt.pf ppf "`%a`" pp x
let pp_quoted_s = pp_quoted Fmt.string

let unbound_variable ~range (var_name : Var_name.t) : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_variable
    Error
    "cannot find value %a in this scope"
    pp_quoted_s
    (var_name :> string)
;;

let unbound_type ~range (type_name : Type_name.t) : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_type_name
    Error
    "cannot find type %a in this scope"
    pp_quoted_s
    (type_name :> string)
;;

let pp_type_var_name ppf (type_var : Type_var_name.t) =
  Fmt.pf ppf "'%s" (type_var :> string)
;;

let unbound_type_variable ~range type_var : t =
  Diagnostic.createf
    ~labels:[ not_found_in_this_scope_label ~range ]
    ~code:Code.Unbound_type_variable
    Error
    "cannot find type variable %a in this scope"
    (pp_quoted pp_type_var_name)
    type_var
;;

let type_constructor_arity_mismatch
      ~args_range
      ~actual_arity
      ~expected_arity
      (type_name : Type_name.With_range.t)
  : t
  =
  let open Diagnostic in
  assert (actual_arity <> expected_arity);
  let expected_arguments_label =
    Label.primaryf ~range:type_name.range "expected %d arguments" expected_arity
  in
  if actual_arity = 0
  then
    Diagnostic.createf
      ~labels:[ expected_arguments_label ]
      ~code:Code.Type_constructor_arity_mismatch
      Error
      "missing type arguments for type %a"
      pp_quoted_s
      (type_name.it :> string)
  else
    Diagnostic.createf
      ~labels:
        [ expected_arguments_label
        ; Label.secondary
            ~range:args_range
            (if actual_arity > expected_arity
             then Message.create "help: remove the unnecessary arguments"
             else Message.createf "supplied %d arguments" actual_arity)
        ]
      ~code:Code.Type_constructor_arity_mismatch
      Error
      "type takes %d arguments but %d arguments were supplied"
      expected_arity
      actual_arity
;;

let mismatched_type ~range =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Type_mismatch
    Error
    "mismatched type"
;;

let case_mismatched_type ~range ~type_head =
  let open Diagnostic in
  let head_name =
    match type_head with
    | `Arrow -> "function type"
    | `Rigid_var -> "polymorphic variable"
    | `Bot -> "void type"
    | `Constr -> "user-defined type"
  in
  Diagnostic.createf
    ~labels:[ Label.primaryf ~range "expected a type equality, found a %s" head_name ]
    ~code:Code.Type_mismatch
    Error
    "mismatched type"
;;

let rigid_variable_escape ~range =
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~code:Code.Rigid_variable_escape
    Error
    "generic type variable escapes its scope"
;;

let scope_escape ~range =
  let open Diagnostic in
  Diagnostic.createf
    ~labels:[ empty_primary_label ~range ]
    ~notes:[ Message.createf "hint: add a type annotation" ]
    ~code:Code.Scope_escape
    Error
    "type-level equality introduced by `match` escapes its scope"
;;

let unexpected_consistent_context ~range =
  let open Diagnostic in
  Diagnostic.createf
    ~labels:
      [ Label.primaryf ~range "type-level equational context is consistent at this point"
      ]
    ~code:Code.Unexpected_consistent_context
    Error
    "unexpected consistent context"
;;
