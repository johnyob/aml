open Core
open Aml_std
open Grace

module Scope = Var.Make (struct
    let module_name = "Constraint.Scope"
  end)

module Type = struct
  module Ident = Var.Make (struct
      let module_name = "Type.Ident"
    end)

  module Var = Var.Make (struct
      let module_name = "Type.Var"
    end)

  type t =
    | Var of Var.t
    | Arrow of t * t
    | Eq of t * t
    | Bot
    | Constr of t list * Ident.t
    | Scope_nil
    | Scope_snoc of t * Scope.t
    | Box of t * t
  [@@deriving sexp]

  let var v = Var v
  let ( @-> ) t1 t2 = Arrow (t1, t2)
  let eq t1 t2 = Eq (t1, t2)
  let constr ts constr = Constr (ts, constr)
  let box scope t = Box (scope, t)
  let bot = Bot

  module Scope = struct
    let nil = Scope_nil
    let snoc t scope = Scope_snoc (t, scope)
  end

  module Kind = struct
    type t =
      | Scope
      | Type
    [@@deriving sexp]
  end

  type binder = Var.t * Kind.t [@@deriving sexp]
end

module Var = Var.Make (struct
    let module_name = "Constraint.Var"
  end)

type t =
  | True
  | False of Aml_error.t
  | Conj of t * t
  | Eq of Type.t * Type.t
  | Exists of Type.binder * t
  | Let of Var.t * lambda * t
  | App of Var.t * Type.t
  | Implication of Scope.t * Type.t * Type.t * t
  | Absurd of Aml_error.t
  | With_range of t * Range.t

and lambda =
  { rigid_type_vars : Type.binder list
  ; type_var : Type.Var.t
  ; body : t
  }
[@@deriving sexp]

let tt = True
let ff err = False err
let ( &~ ) t1 t2 = Conj (t1, t2)

let all ts =
  match ts with
  | [] -> tt
  | [ t ] -> t
  | ts -> List.fold ts ~init:tt ~f:( &~ )
;;

let ( =~ ) type1 type2 = Eq (type1, type2)
let exists type_var t = Exists (type_var, t)
let exists_many vars in_ = List.fold_right vars ~init:in_ ~f:exists
let ( #= ) x scheme = x, scheme
let fun_ ?(rigid_type_vars = []) type_var body = { rigid_type_vars; type_var; body }
let let_ (x, scheme) ~in_ = Let (x, scheme, in_)
let app x type_ = App (x, type_)
let with_range t ~range = With_range (t, range)
let ( @: ) scope types = scope, types
let ( @=> ) (scope, (type1, type2)) in_ = Implication (scope, type1, type2, in_)
let absurd err = Absurd err
