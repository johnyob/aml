open! Import
open Ast_types
open Ast
open Constraint

module Convert = struct
  let type_name ~env (type_name : Type_name.With_range.t) : Type.Ident.t * int =
    (* If the type name is shadowed, pick the closest one *)
    match Env.find_type_def env type_name.it with
    | None -> Aml_error.(raise @@ unbound_type ~range:type_name.range type_name.it)
    | Some type_def -> type_def.type_ident, type_def.type_arity
  ;;

  let assert_expected_arity_is_equal_to_actual_arity
        ~(arg_types : _ With_range.t list)
        ~(expected_arity : int)
        ~(constr_name : Type_name.With_range.t)
    =
    let actual_arity = List.length arg_types in
    if expected_arity <> actual_arity
    then (
      let args_range =
        match arg_types with
        | type_ :: arg_types ->
          List.fold arg_types ~init:type_.range ~f:(fun range type_ ->
            Range.merge range type_.range)
        | [] ->
          (* For an empty args list, the correct range is the range of the type name *)
          constr_name.range
      in
      Aml_error.(
        raise
        @@ type_constructor_arity_mismatch
             ~args_range
             ~actual_arity
             ~expected_arity
             constr_name))
  ;;

  let rec core_type ~env (type_ : Ast.core_type) : Type.t =
    match type_.it with
    | Type_var v ->
      (match Env.find_type_var env v.it with
       | Some v -> Type.var v
       | None -> Aml_error.(raise @@ unbound_type_variable ~range:v.range v.it))
    | Type_arrow (type1, type2) ->
      let type1 = core_type ~env type1
      and type2 = core_type ~env type2 in
      Type.(type1 @-> type2)
    | Type_eq (type1, type2) ->
      let type1 = core_type ~env type1
      and type2 = core_type ~env type2 in
      Type.eq type1 type2
    | Type_bot -> Type.bot
    | Type_constr (arg_types, constr_name) ->
      let type_ident, expected_arity = type_name ~env constr_name in
      assert_expected_arity_is_equal_to_actual_arity
        ~arg_types
        ~expected_arity
        ~constr_name;
      let arg_types = arg_types |> List.map ~f:(core_type ~env) in
      Type.constr arg_types type_ident
  ;;

  let core_scheme ~(env : Env.t) (scheme : Ast.core_scheme)
    : (Type.Var.t * Type.Kind.t) list * Type.t
    =
    let { scheme_quantifiers; scheme_body } = scheme.it in
    let env, quantifiers =
      List.fold_map scheme_quantifiers ~init:env ~f:(fun env type_var ->
        Env.rename_type_var env ~type_var:type_var.it ~in_:(fun env ctype_var ->
          env, (ctype_var, Type.Kind.Type)))
    in
    let body = core_type ~env scheme_body in
    quantifiers, body
  ;;
end

let scoped_rigid_type ~id_source (type_ : Type.t) : Type.binder list * Type.t =
  let scope_vars = ref [] in
  let alloc_scope_var () =
    let s = Type.Var.create ~id_source () in
    scope_vars := (s, Type.Kind.Scope) :: !scope_vars;
    s
  in
  let alloc_box type_ = Type.(box (var (alloc_scope_var ())) type_) in
  let rec loop (type_ : Type.t) =
    match type_ with
    | Var v -> alloc_box Type.(var v)
    | Arrow (type1, type2) ->
      let type1 = loop type1
      and type2 = loop type2 in
      Type.(type1 @-> type2)
    | Eq (type1, type2) ->
      let type1 = loop type1
      and type2 = loop type2 in
      Type.eq type1 type2
    | Bot -> alloc_box Type.bot
    | Constr (arg_types, type_ident) ->
      if List.is_empty arg_types
      then alloc_box Type.(constr [] type_ident)
      else (
        let arg_types = arg_types |> List.map ~f:loop in
        Type.constr arg_types type_ident)
    | Scope_nil | Scope_snoc _ | Box _ ->
      Aml_error.(
        raise @@ bug_s ~here:[%here] [%message "Type is not rigid" (type_ : Type.t)])
  in
  let scoped_type = loop type_ in
  !scope_vars, scoped_type
;;

module Expression = struct
  let exists' ~id_source ?(kind = Type.Kind.Type) f =
    let a = Type.Var.create ~id_source () in
    exists (a, kind) (f a)
  ;;

  let exists_many' ~id_source ?(kind = Type.Kind.Type) n f =
    let as_ = List.init n ~f:(fun _ -> Type.Var.create ~id_source (), kind) in
    exists_many as_ (f (List.map ~f:fst as_))
  ;;

  let exists_scoped ~id_source type_ f =
    let scope_vars, type_ = scoped_rigid_type ~id_source type_ in
    exists_many scope_vars (f type_)
  ;;

  let bind_var ~env var var_type ~in_ =
    Env.rename_var env ~var:(With_range.it var) ~in_:(fun env cvar ->
      let in_ = in_ env in
      let fun_var = Type.Var.create ~id_source:(Env.id_source env) () in
      let_ cvar#=(fun_ fun_var @@ Type.(var fun_var =~ var var_type)) ~in_)
  ;;

  let rec bind_vars ~env var_and_types ~in_ =
    match var_and_types with
    | [] -> in_ env
    | (var, var_type) :: var_and_types ->
      bind_var ~env var var_type ~in_:(fun env -> bind_vars ~env var_and_types ~in_)
  ;;

  let infer_constant ~env const const_type =
    exists' ~id_source:(Env.id_source env) ~kind:Scope
    @@ fun s ->
    Type.(
      var const_type
      =~ box (var s)
         @@
         match const with
         | Const_int _ -> Predef.int
         | Const_bool _ -> Predef.bool
         | Const_unit -> Predef.unit)
  ;;

  let rec infer_exp ~(env : Env.t) (exp : expression) (exp_type : Type.Var.t) =
    let id_source = Env.id_source env in
    with_range ~range:exp.range
    @@
    match exp.it with
    | Exp_var var ->
      (match Env.find_var env var.it with
       | Some var -> app var (Type.var exp_type)
       | None -> Aml_error.(raise @@ unbound_variable ~range:var.range var.it))
    | Exp_const const -> infer_constant ~env const exp_type
    | Exp_fun (vars, exp) ->
      exists_many' ~id_source (List.length vars)
      @@ fun as1 ->
      exists' ~id_source
      @@ fun a2 ->
      let var_and_types = List.zip_exn vars as1 in
      let c = bind_vars ~env var_and_types ~in_:(fun env -> infer_exp ~env exp a2) in
      let arr_type =
        List.fold_right as1 ~init:(Type.var a2) ~f:(fun a1 arr -> Type.(var a1 @-> arr))
      in
      Type.(var exp_type =~ arr_type) &~ c
    | Exp_app (exp1, exp2) ->
      exists' ~id_source
      @@ fun a1 ->
      exists' ~id_source
      @@ fun a2 ->
      let c1 = infer_exp ~env exp1 a2 in
      let c2 = infer_exp ~env exp2 a1 in
      Type.(var a2 =~ var a1 @-> var exp_type) &~ c1 &~ c2
    | Exp_let (value_binding, exp) ->
      infer_value_binding ~env value_binding @@ fun env -> infer_exp ~env exp exp_type
    | Exp_forall (type_vars, exp) ->
      let env, rigid_type_vars =
        List.fold_map type_vars ~init:env ~f:(fun env type_var ->
          Env.rename_type_var env ~type_var:type_var.it ~in_:(fun env ctype_var ->
            env, (ctype_var, Type.Kind.Type)))
      in
      let exp_type' = Type.Var.create ~id_source:(Env.id_source env) () in
      let c = infer_exp ~env exp exp_type' in
      let x = Var.create ~id_source:(Env.id_source env) () in
      let_ x#=(fun_ ~rigid_type_vars exp_type' c) ~in_:(app x (Type.var exp_type))
    | Exp_annot (exp, annot) -> infer_annot_exp ~env exp ~annot exp_type
    | Exp_match (match_exp, annot, case) ->
      exists' ~id_source
      @@ fun match_exp_type ->
      let c1 = infer_annot_exp ~env ~annot match_exp match_exp_type in
      let c2 = infer_case ~env case ~lhs_type:annot ~rhs_type:exp_type in
      c1 &~ c2
    | Exp_refl -> exists' ~id_source @@ fun a -> Type.(var exp_type =~ eq (var a) (var a))
    | Exp_absurd -> absurd (Aml_error.unexpected_consistent_context ~range:exp.range)

  and infer_annot_exp ~env ~annot exp exp_type =
    let annot = Convert.core_type ~env annot in
    exists_scoped ~id_source:(Env.id_source env) annot
    @@ fun annot1 ->
    exists_scoped ~id_source:(Env.id_source env) annot
    @@ fun annot2 ->
    exists' ~id_source:(Env.id_source env)
    @@ fun exp_type' ->
    let c = infer_exp ~env exp exp_type' in
    Type.(var exp_type =~ annot1) &~ Type.(var exp_type' =~ annot2) &~ c

  and infer_case ~env case ~lhs_type ~rhs_type =
    let type1, type2 =
      match lhs_type.it with
      | Type_eq (type1, type2) -> type1, type2
      | _ ->
        let type_head =
          match lhs_type.it with
          | Type_bot -> `Bot
          | Type_arrow _ -> `Arrow
          | Type_var _ -> `Rigid_var
          | Type_constr _ -> `Constr
          | Type_eq _ -> assert false
        in
        Aml_error.(raise @@ case_mismatched_type ~range:lhs_type.range ~type_head)
    in
    let scope = Scope.create ~id_source:(Env.id_source env) () in
    let type1 = Convert.core_type ~env type1
    and type2 = Convert.core_type ~env type2 in
    (scope @: (type1, type2)) @=> infer_exp ~env case rhs_type

  and infer_value_binding ~(env : Env.t) value_binding k =
    let { value_binding_var = var; value_binding_exp = exp } = value_binding.it in
    let exp_type = Type.Var.create ~id_source:(Env.id_source env) () in
    let c = infer_exp ~env exp exp_type in
    Env.rename_var env ~var:var.it ~in_:(fun env cvar ->
      let c' = k env in
      let_ cvar#=(fun_ exp_type c) ~in_:c')
  ;;
end

module Structure = struct
  let infer_prim ~env (value_desc : value_description) k =
    let { value_type; value_name } = value_desc.it in
    let id_source = Env.id_source env in
    let rigid_type_vars, type_ = Convert.core_scheme ~env value_type in
    let scope_vars, type_ = scoped_rigid_type ~id_source type_ in
    let scm_type = Type.Var.create ~id_source () in
    Env.rename_var env ~var:value_name.it ~in_:(fun env cvar ->
      let c = k env in
      let_
        cvar#=(fun_ ~rigid_type_vars scm_type
               @@ exists_many scope_vars
               @@ Type.(var scm_type =~ type_))
        ~in_:c)
  ;;

  let infer_type_decl ~(env : Env.t) (type_decl : type_declaration) =
    let { type_decl_name; type_decl_params; type_decl_kind = Type_decl_abstract } =
      type_decl.it
    in
    let type_ident = Type.Ident.create ~id_source:(Env.id_source env) () in
    let type_arity = List.length type_decl_params in
    let type_def = { Env.type_name = type_decl_name.it; type_ident; type_arity } in
    Env.add_type_def env type_def
  ;;

  let rec infer_str ~env (str : Ast.structure) =
    match str with
    | [] -> tt
    | { it = Str_type type_decl; range } :: str ->
      let env = infer_type_decl ~env type_decl in
      with_range ~range @@ infer_str ~env str
    | { it = Str_primitive value_desc; range } :: str ->
      with_range ~range @@ infer_prim ~env value_desc @@ fun env -> infer_str ~env str
    | { it = Str_value value_binding; range } :: str ->
      with_range ~range
      @@ Expression.infer_value_binding ~env value_binding
      @@ fun env -> infer_str ~env str
  ;;
end
