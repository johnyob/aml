open! Import
module C = Constraint
module G = Generalization
module Type = G.Type
module State = G.State

module Error = struct
  type t =
    { it : desc
    ; range : Range.t option
    }

  and desc =
    | Unsatisfiable of Aml_error.t
    | Unbound_type_var of C.Type.Var.t
    | Unbound_var of C.Var.t
    | Cannot_unify
    | Rigid_variable_escape
    | Not_rigid of C.Type.t
    | Scope_escape
  [@@deriving sexp]

  exception T of t

  let create ~range it = { it; range }
  let raise ~range it = raise @@ T { it; range }
end

module Env = struct
  type t =
    { type_vars : Type.t C.Type.Var.Map.t
    ; expr_vars : Type.scheme C.Var.Map.t
    ; equations : G.Equations.t
    ; range : Range.t option
    }
  [@@deriving sexp_of]

  let raise t err = Error.raise ~range:t.range err
  let with_range t ~range = { t with range = Some range }

  let empty ~range =
    { type_vars = C.Type.Var.Map.empty
    ; expr_vars = C.Var.Map.empty
    ; equations = G.Equations.empty
    ; range
    }
  ;;

  let bind_type_var t ~var ~type_ =
    { t with type_vars = Map.set t.type_vars ~key:var ~data:type_ }
  ;;

  let bind_var t ~var ~type_ =
    { t with expr_vars = Map.set t.expr_vars ~key:var ~data:type_ }
  ;;

  let find_type_var t type_var =
    try Map.find_exn t.type_vars type_var with
    | _ -> raise t @@ Unbound_type_var type_var
  ;;

  let find_var t expr_var =
    try Map.find_exn t.expr_vars expr_var with
    | _ -> raise t @@ Unbound_var expr_var
  ;;
end

let rec rtype_of_type : env:Env.t -> C.Type.t -> G.Equations.Rigid_type.t =
  fun ~env type_ ->
  let module Rt = G.Equations.Rigid_type in
  let self = rtype_of_type ~env in
  match type_ with
  | Var type_var ->
    (match Type.inner (Env.find_type_var env type_var) with
     | Structure (Structure (Var rv)) -> Rt.rigid_var rv
     | _ -> Env.raise env @@ Not_rigid type_)
  | Scope_nil | Scope_snoc _ | Box _ -> Env.raise env @@ Not_rigid type_
  | Bot -> Rt.former Bot
  | Eq (type1, type2) -> Rt.former (Eq (self type1, self type2))
  | Constr (args, constr) -> Rt.former (Constr (List.map args ~f:self, constr))
  | Arrow (type1, type2) -> Rt.former (Arrow (self type1, self type2))
;;

let rec gtype_of_type : state:State.t -> env:Env.t -> C.Type.t -> G.Type.t =
  fun ~state ~env type_ ->
  let self = gtype_of_type ~state ~env in
  match type_ with
  | Var type_var -> Env.find_type_var env type_var
  | Bot -> G.create_former ~state Bot
  | Eq (type1, type2) -> G.create_former ~state (Eq (self type1, self type2))
  | Arrow (type1, type2) -> G.create_former ~state (Arrow (self type1, self type2))
  | Constr (args, constr) ->
    G.create_former ~state (Constr (List.map args ~f:self, constr))
  | Box (scope, type_) -> G.create_box ~state ~scope:(self scope) (self type_)
  | Scope_nil -> G.create_scope ~state G.Scope_row.nil
  | Scope_snoc _ ->
    (* Our version of [Scope_row] cannot easily encode [Scope_snoc], 
       but our generated constraints don't use it *)
    assert false
;;

let exists ~(state : State.t) ~env ~type_var =
  Env.bind_type_var env ~var:type_var ~type_:(G.create_var ~state)
;;

let unify ~(state : State.t) ~(env : Env.t) gtype1 gtype2 =
  [%log.global.debug
    "Unify" (state : State.t) (env : Env.t) (gtype1 : Type.t) (gtype2 : Type.t)];
  try G.unify ~state ~equations:env.equations gtype1 gtype2 with
  | G.Unify.Unify (_gtype1, _gtype2) -> Env.raise env Cannot_unify
  | G.Equations.Rigid_type.Not_principal ->
    Aml_error.(
      raise
      @@ bug_s
           ~here:[%here]
           [%message
             "Require principal types under boxes / used in equalities"
               (gtype1 : Type.t)
               (gtype2 : Type.t)])
;;

let add_equation ~state ~(env : Env.t) rtype1 rtype2 =
  try { env with equations = G.add_equation ~state env.equations rtype1 rtype2 } with
  | G.Equations.Rigid_type.Not_principal ->
    Aml_error.(
      raise
      @@ bug_s
           ~here:[%here]
           [%message
             "Require principal types in implciations"
               (rtype1 : G.Equations.Rigid_type.t)
               (rtype2 : G.Equations.Rigid_type.t)])
;;

let exit_region ~state ~env ~rigid_vars ~types =
  try G.exit ~state ~rigid_vars ~types with
  | G.Scope_escape _ -> Env.raise env Scope_escape
  | G.Rigid_variable_escape _ -> Env.raise env Rigid_variable_escape
;;

let rec solve : state:State.t -> env:Env.t -> C.t -> unit =
  fun ~state ~env cst ->
  [%log.global.debug "Solving constraint" (state : State.t) (env : Env.t) (cst : C.t)];
  let self ~state ?(env = env) cst = solve ~state ~env cst in
  match cst with
  | True -> ()
  | False err -> Env.raise env @@ Unsatisfiable err
  | Conj (cst1, cst2) ->
    [%log.global.debug "Solving conj lhs"];
    self ~state cst1;
    [%log.global.debug "Solving conj rhs"];
    self ~state cst2
  | Eq (type1, type2) ->
    [%log.global.debug "Decoding type1" (type1 : C.Type.t)];
    let gtype1 = gtype_of_type ~state ~env type1 in
    [%log.global.debug "Decoded type1" (gtype1 : Type.t)];
    [%log.global.debug "Decoding type2" (type2 : C.Type.t)];
    let gtype2 = gtype_of_type ~state ~env type2 in
    [%log.global.debug "Decoded type2" (gtype2 : Type.t)];
    unify ~state ~env gtype1 gtype2
  | Let (var, lambda, in_) ->
    [%log.global.debug "Solving let scheme"];
    let gscheme = gscheme_of_lambda ~state ~env lambda in
    [%log.global.debug "Binding var to scheme" (var : C.Var.t) (gscheme : Type.scheme)];
    let env = Env.bind_var env ~var ~type_:gscheme in
    [%log.global.debug "Solving let body"];
    self ~state ~env in_
  | App (var, expected_type) ->
    [%log.global.debug "Decoding expected_type" (expected_type : C.Type.t)];
    let expected_gtype = gtype_of_type ~state ~env expected_type in
    [%log.global.debug "Decoded expected_type" (expected_gtype : Type.t)];
    let var_gscheme = Env.find_var env var in
    [%log.global.debug "Instantiating scheme" (var : C.Var.t) (var_gscheme : Type.scheme)];
    let actual_gtype = G.instantiate ~state var_gscheme in
    [%log.global.debug "Scheme instance" (actual_gtype : Type.t)];
    unify ~state ~env actual_gtype expected_gtype
  | Exists ((type_var, _kind), cst) ->
    [%log.global.debug "Binding unification for type_var" (type_var : C.Type.Var.t)];
    let env = exists ~state ~env ~type_var in
    [%log.global.debug "Updated env" (env : Env.t)];
    [%log.global.debug "Solving exist body"];
    self ~state ~env cst
  | Implication (_scope, type1, type2, body) ->
    [%log.global.debug "Entered new region (impl)"];
    G.enter ~state;
    [%log.global.debug "Decoding type1" (type1 : C.Type.t)];
    let rtype1 = rtype_of_type ~env type1 in
    [%log.global.debug "Decoded type1" (rtype1 : G.Equations.Rigid_type.t)];
    [%log.global.debug "Decoding type2" (type2 : C.Type.t)];
    let rtype2 = rtype_of_type ~env type2 in
    [%log.global.debug "Decoded type2" (rtype2 : G.Equations.Rigid_type.t)];
    let env = add_equation ~state ~env rtype1 rtype2 in
    [%log.global.debug "Added equation" (env : Env.t)];
    self ~state ~env body;
    ignore
      (exit_region ~state ~env ~rigid_vars:[] ~types:[] : Type.t list * Type.scheme list)
  | Absurd err ->
    if G.Equations.is_inconsistent env.equations
    then ()
    else Env.raise env @@ Unsatisfiable err
  | With_range (t, range) -> solve ~state ~env:(Env.with_range env ~range) t

and gscheme_of_lambda ~state ~env { rigid_type_vars; type_var; body } =
  G.enter ~state;
  [%log.global.debug "Entered new region" (state : State.t)];
  let env, rigid_vars =
    List.fold_map rigid_type_vars ~init:env ~f:(fun env (type_var, _kind) ->
      [%log.global.debug "Binding rigid variable to type_var" (type_var : C.Type.Var.t)];
      let rv = G.create_rigid_var ~state in
      [%log.global.debug "Rigid variable type" (rv : Type.t)];
      let env = Env.bind_type_var env ~var:type_var ~type_:rv in
      env, rv)
  in
  let env, type_var =
    [%log.global.debug "Binding root variable" (type_var : C.Type.Var.t)];
    let var = G.create_var ~state in
    [%log.global.debug "Root varible type" (var : Type.t)];
    Env.bind_type_var env ~var:type_var ~type_:var, var
  in
  [%log.global.debug "Solving lambda's body"];
  solve ~state ~env body;
  let _generics, schemes =
    [%log.global.debug "Exiting region" (state : State.t) (env : Env.t)];
    exit_region ~state ~env ~rigid_vars ~types:[ type_var ]
  in
  let scheme = List.hd_exn schemes in
  [%log.global.debug "Scheme" (scheme : Type.scheme)];
  scheme
;;

let solve : ?range:Range.t -> C.t -> (unit, Error.t) result =
  fun ?range cst ->
  try
    let state = State.create () in
    let env = Env.empty ~range in
    solve ~state ~env cst;
    G.generalize_root_region ~state;
    Ok ()
  with
  (* Catch solver exceptions *)
  | Error.T err -> Error err
;;
