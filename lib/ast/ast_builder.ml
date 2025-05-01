open Grace
open Ast_types
open Ast

module type Range = sig
  val v : Range.t
end

module type S = sig
  type 'a with_range_fn

  val type_var_name : (string -> Type_var_name.With_range.t) with_range_fn
  val type_name : (string -> Type_name.With_range.t) with_range_fn
  val var_name : (string -> Var_name.With_range.t) with_range_fn

  module Type : sig
    val var : (Type_var_name.With_range.t -> core_type) with_range_fn
    val arrow : (core_type -> core_type -> core_type) with_range_fn
    val eq : (core_type -> core_type -> core_type) with_range_fn
    val bot : core_type with_range_fn
    val constr : (core_type list -> Type_name.With_range.t -> core_type) with_range_fn

    val scheme
      : (?quantifiers:Type_var_name.With_range.t list -> core_type -> core_scheme)
          with_range_fn
  end

  module Expression : sig
    val var : (Var_name.With_range.t -> expression) with_range_fn
    val const : (constant -> expression) with_range_fn
    val fun_ : (Var_name.With_range.t list -> expression -> expression) with_range_fn
    val app : (expression -> expression -> expression) with_range_fn
    val let_ : (value_binding -> in_:expression -> expression) with_range_fn

    val forall
      : (Type_var_name.With_range.t list -> expression -> expression) with_range_fn

    val annot : (expression -> core_type -> expression) with_range_fn
    val refl : expression with_range_fn

    val match_
      : (expression -> annot:core_type -> with_:expression -> expression) with_range_fn

    val absurd : expression with_range_fn
  end

  val value_binding : (Var_name.With_range.t -> expression -> value_binding) with_range_fn

  module Structure : sig
    val value : (value_binding -> structure_item) with_range_fn
    val primitive : (value_description -> structure_item) with_range_fn
    val type_ : (type_declaration -> structure_item) with_range_fn

    val type_decl
      : (name:Type_name.With_range.t
         -> params:Type_var_name.With_range.t list
         -> type_decl_kind
         -> type_declaration)
          with_range_fn

    val value_desc
      : (name:Var_name.With_range.t -> type_:core_scheme -> value_description)
          with_range_fn
  end
end

module Default : S with type 'a with_range_fn := range:Range.t -> 'a = struct
  let type_var_name ~range name = With_range.create ~range @@ Type_var_name.create name
  let var_name ~range name = With_range.create ~range @@ Var_name.create name
  let type_name ~range name = With_range.create ~range @@ Type_name.create name

  module Type = struct
    let var ~range type_var_name = With_range.create ~range @@ Type_var type_var_name
    let arrow ~range type1 type2 = With_range.create ~range @@ Type_arrow (type1, type2)
    let eq ~range type1 type2 = With_range.create ~range @@ Type_eq (type1, type2)
    let bot ~range = With_range.create ~range Type_bot

    let constr ~range arg_types constr_name =
      With_range.create ~range @@ Type_constr (arg_types, constr_name)
    ;;

    let scheme ~range ?(quantifiers = []) body =
      With_range.create ~range @@ { scheme_quantifiers = quantifiers; scheme_body = body }
    ;;
  end

  module Expression = struct
    let var ~range var_name = With_range.create ~range @@ Exp_var var_name
    let const ~range const = With_range.create ~range @@ Exp_const const
    let fun_ ~range vars exp = With_range.create ~range @@ Exp_fun (vars, exp)
    let app ~range exp1 exp2 = With_range.create ~range @@ Exp_app (exp1, exp2)

    let let_ ~range value_binding ~in_ =
      With_range.create ~range @@ Exp_let (value_binding, in_)
    ;;

    let forall ~range type_var_names exp =
      With_range.create ~range @@ Exp_forall (type_var_names, exp)
    ;;

    let annot ~range exp type_ = With_range.create ~range @@ Exp_annot (exp, type_)
    let refl ~range = With_range.create ~range @@ Exp_refl

    let match_ ~range exp ~annot ~with_ =
      With_range.create ~range @@ Exp_match (exp, annot, with_)
    ;;

    let absurd = With_range.create Exp_absurd
  end

  let value_binding ~range var exp =
    With_range.create ~range { value_binding_exp = exp; value_binding_var = var }
  ;;

  module Structure = struct
    let value ~range value_binding = With_range.create ~range @@ Str_value value_binding
    let primitive ~range value_desc = With_range.create ~range @@ Str_primitive value_desc
    let type_ ~range type_decls = With_range.create ~range @@ Str_type type_decls

    let type_decl ~range ~name ~params kind =
      With_range.create
        ~range
        { type_decl_name = name; type_decl_params = params; type_decl_kind = kind }
    ;;

    let value_desc ~range ~name ~type_ =
      With_range.create ~range { value_name = name; value_type = type_ }
    ;;
  end
end

module Make (R : Range) : S with type 'a with_range_fn := 'a = struct
  open Default

  let type_var_name = type_var_name ~range:R.v
  let var_name = var_name ~range:R.v
  let type_name = type_name ~range:R.v

  module Type = struct
    let var = Type.var ~range:R.v
    let arrow = Type.arrow ~range:R.v
    let eq = Type.eq ~range:R.v
    let bot = Type.bot ~range:R.v
    let constr = Type.constr ~range:R.v
    let scheme = Type.scheme ~range:R.v
  end

  module Expression = struct
    let var = Expression.var ~range:R.v
    let const = Expression.const ~range:R.v
    let fun_ = Expression.fun_ ~range:R.v
    let app = Expression.app ~range:R.v
    let let_ = Expression.let_ ~range:R.v
    let forall = Expression.forall ~range:R.v
    let annot = Expression.annot ~range:R.v
    let refl = Expression.refl ~range:R.v
    let match_ = Expression.match_ ~range:R.v
    let absurd = Expression.absurd ~range:R.v
  end

  let value_binding = value_binding ~range:R.v

  module Structure = struct
    let value = Structure.value ~range:R.v
    let primitive = Structure.primitive ~range:R.v
    let type_ = Structure.type_ ~range:R.v
    let type_decl = Structure.type_decl ~range:R.v
    let value_desc = Structure.value_desc ~range:R.v
  end
end
