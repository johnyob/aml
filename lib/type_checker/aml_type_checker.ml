open! Import
open Constraint

let infer_exp exp =
  Predef.Env.wrap
  @@ fun env ->
  let exp_type = Type.Var.create ~id_source:(Env.id_source env) ~name:"exp_type0" () in
  let c = Infer.Expression.infer_exp ~env exp exp_type in
  exists (exp_type, Type) c
;;

let infer_str str = Predef.Env.wrap @@ fun env -> Infer.Structure.infer_str ~env str

let check cst =
  match Aml_constraint_solver.solve cst with
  | Ok () -> ()
  | Error { range; it } ->
    let get_range range =
      Option.value_or_thunk range ~default:(fun () ->
        Aml_error.(
          raise
          @@ bug_s
               ~here:[%here]
               [%message
                 "Expect range to be given"
                   (it : Aml_constraint_solver.Error.desc)
                   (cst : Constraint.t)]))
    in
    (match it with
     | Unsatisfiable err -> Aml_error.raise err
     | Unbound_type_var type_var ->
       Aml_error.(
         raise
         @@ bug_s
              ~here:[%here]
              [%message
                "Unbound constraint type variable"
                  (type_var : Constraint.Type.Var.t)
                  (range : Range.t option)
                  (cst : Constraint.t)])
     | Unbound_var var ->
       Aml_error.(
         raise
         @@ bug_s
              ~here:[%here]
              [%message
                "Unbound constraint variable"
                  (var : Constraint.Var.t)
                  (range : Range.t option)
                  (cst : Constraint.t)])
     | Not_rigid type_ ->
       Aml_error.(
         raise
         @@ bug_s ~here:[%here] [%message "Type is not rigid" (type_ : Constraint.Type.t)])
     | Scope_escape -> Aml_error.(raise @@ scope_escape ~range:(get_range range))
     | Cannot_unify -> Aml_error.(raise @@ mismatched_type ~range:(get_range range))
     | Rigid_variable_escape ->
       Aml_error.(raise @@ rigid_variable_escape ~range:(get_range range)))
;;
