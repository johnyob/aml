open! Import
open Constraint
open Ast_types

(* Pre-defined types have their own [id_source] since the type names cannot be parsed => no conflict possible *)
let id_source = Identifier.create_source ()
let int_ident = Type.Ident.create ~id_source ~name:"Stdlib.int" ()
let bool_ident = Type.Ident.create ~id_source ~name:"Stdlib.bool" ()
let unit_ident = Type.Ident.create ~id_source ~name:"Stdlib.unit" ()
let int = Type.(constr [] int_ident)
let bool = Type.(constr [] bool_ident)
let unit = Type.(constr [] unit_ident)

module Env = struct
  let type_def name arity ident =
    { Env.type_name = Type_name.create name; type_arity = arity; type_ident = ident }
  ;;

  let t = [ "int", 0, int_ident; "bool", 0, bool_ident; "unit", 0, unit_ident ]

  let wrap k =
    let env = Env.empty () in
    let env =
      List.fold t ~init:env ~f:(fun env (type_str, type_arity, type_ident) ->
        Env.add_type_def env (type_def type_str type_arity type_ident))
    in
    k env
  ;;
end
