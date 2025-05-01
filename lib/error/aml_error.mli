open Core
open Grace
open Aml_ast.Ast_types

type t [@@deriving sexp]

exception T of t

val raise : t -> 'a

include Pretty_printer.S with type t := t

(** [handle_uncaught ~exit f] catches [T err] escaping [f] and prints the error
    message to stderr. 
    
    Exits with return code 1 if [exit] is [true] and [f] is not running 
    in an expect test, and returns unit otherwise. *)
val handle_uncaught : exit:bool -> (unit -> unit) -> unit

(** [bug ~here msg] constructs an internal fatal error.
    This error is only to be used to indicate a bug in Aml. *)
val bug : here:Source_code_position.t -> Diagnostic.Message.t -> t

(** [bugf ~here fmt ...] formats a message and creates an internal fatal error. *)
val bugf : here:Source_code_position.t -> ('a, t) Diagnostic.format -> 'a

val bug_s : here:Source_code_position.t -> Sexp.t -> t
val unterminated_comment : range:Range.t -> t
val unknown_start_of_token : range:Range.t -> char -> t
val syntax_error : range:Range.t -> t
val unbound_variable : range:Range.t -> Var_name.t -> t
val unbound_type : range:Range.t -> Type_name.t -> t
val unbound_type_variable : range:Range.t -> Type_var_name.t -> t

val type_constructor_arity_mismatch
  :  args_range:Range.t
  -> actual_arity:int
  -> expected_arity:int
  -> Type_name.With_range.t
  -> t

val mismatched_type : range:Range.t -> t

val case_mismatched_type
  :  range:Range.t
  -> type_head:[ `Bot | `Constr | `Arrow | `Rigid_var ]
  -> t

val rigid_variable_escape : range:Range.t -> t
val scope_escape : range:Range.t -> t
val unexpected_consistent_context : range:Range.t -> t
