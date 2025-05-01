open! Import

module Level : sig
  type t = private int [@@deriving equal, compare, sexp, hash]

  include Comparable.S with type t := t

  val zero : t
  val succ : t -> t
  val prev : t -> t
end = struct
  module T = struct
    type t = int [@@deriving equal, compare, sexp, hash]
  end

  include T
  include Comparable.Make (T)

  let zero = 0
  let succ t = t + 1
  let prev t = t - 1
end

module Status = struct
  type t =
    | Instance of Level.t
    | Generic
  [@@deriving equal, compare, hash, sexp]

  let merge t1 t2 =
    match t1, t2 with
    | Generic, _ | _, Generic ->
      Aml_error.raise
        (Aml_error.bug_s
           ~here:[%here]
           [%message "Cannot unify a generic structure" (t1 : t) (t2 : t)])
    | Instance lvl1, Instance lvl2 -> Instance (Level.min lvl1 lvl2)
  ;;

  let level t =
    match t with
    | Instance lvl -> Some lvl
    | Generic -> None
  ;;

  let level_exn ?here t = Option.value_exn ?here ~message:"Cannot be generic" (level t)
end

module Scope_set = struct
  (* In our solver, each scope [phi] is associated with a new level [lvl]. 
     The scope set is the maximum of these levels. 
     
     A scoped type [[Psi]tau] escapes its scope if the level of the type [l] is less 
      than the maximum of the levels of the scopes in [Phi]. See [update_level] for the check. *)
  type t = Level.t [@@deriving sexp, equal, compare, hash]

  let empty = Level.zero
  let is_empty t = Level.(t = zero)
  let union = Level.max
  let is_subset t1 t2 = Level.(t1 <= t2)
  let inter = Level.min
end

module F = Structure.Former
module R = Structure.Rigid (F)
module A = Structure.Scoped_ambivalent (R) (Scope_set)
module Rigid_var = Structure.Rigid_var
module Scope_row = A.Scope_row

module S = struct
  module Inner = Structure.First_order (A)

  type 'a t =
    { id : Identifier.t
    ; inner : 'a Inner.t
    ; status : Status.t
    }
  [@@deriving equal, compare, hash, sexp]

  let create ~id_source ~level inner =
    { id = Identifier.create id_source; status = Status.Instance level; inner }
  ;;

  type 'a ctx =
    { id_source : Identifier.source
    ; curr_level : Level.t
    ; register_type : 'a -> unit
    ; super : 'a Inner.ctx
    }

  exception Cannot_merge = Inner.Cannot_merge

  let iter t ~f = Inner.iter t.inner ~f
  let fold t ~init ~f = Inner.fold t.inner ~init ~f

  let merge ~ctx ~create:create_type ~unify t1 t2 =
    let status = Status.merge t1.status t2.status in
    let inner =
      Inner.merge
        ~ctx:ctx.super
        ~create:(fun i ->
          let t = create_type (create ~id_source:ctx.id_source ~level:ctx.curr_level i) in
          ctx.register_type t;
          t)
        ~unify:(fun ~ctx:super a1 a2 -> unify ~ctx:{ ctx with super } a1 a2)
        t1.inner
        t2.inner
    in
    { id = t1.id; status; inner }
  ;;

  let scope_set t =
    match t.inner with
    | Structure (Scope scope_row) -> scope_row.scopes
    | _ -> Scope_set.empty
  ;;
end

module Region = struct
  type 'a t = { mutable types : 'a list } [@@deriving sexp]

  let create () = { types = [] }
  let register_type t type_ = t.types <- type_ :: t.types
end

module Scheme = struct
  type 'a t = { root : 'a } [@@deriving sexp_of]

  let body t = t.root
end

module Region_stack : sig
  (** ['a t] is a stack of ['a Region.t]s *)
  type 'a t [@@deriving sexp_of]

  (** [create ()] creates a region stack with a root region *)
  val create : unit -> 'a t

  (** [push t] pushes a new region onto the stack *)
  val push : 'a t -> unit

  (** [pop t] pops a region from the stack *)
  val pop : 'a t -> unit

  (** [get_exn t lvl] returns the region at level [lvl] 

      @raises Invalid_argument if [length t > lvl] *)
  val get_exn : 'a t -> Level.t -> 'a Region.t

  (** [length t] returns the number of regions in the stack *)
  val length : 'a t -> int
end = struct
  type 'a t = ('a Region.t Dynarray.t[@sexp.opaque]) [@@deriving sexp_of]

  let get_exn t (level : Level.t) = Dynarray.get t (level :> int)
  let length t = Dynarray.length t
  let push t = Dynarray.add_last t (Region.create ())
  let pop t = Dynarray.remove_last t

  let create () =
    let t = Dynarray.create () in
    push t;
    t
  ;;
end

module Type = struct
  include Unifier.Make (S) ()
  include Type

  type region = t Region.t [@@deriving sexp_of]
  type region_stack = t Region_stack.t [@@deriving sexp_of]
  type scheme = t Scheme.t [@@deriving sexp_of]

  let id t = (structure t).id
  let inner t = (structure t).inner

  let set_inner t inner =
    let structure = structure t in
    set_structure t { structure with inner }
  ;;

  let status t = (structure t).status

  let set_status t status =
    let structure = structure t in
    set_structure t { structure with status }
  ;;

  let level t = Status.level (status t)
  let level_exn ?here t = Status.level_exn ?here (status t)
end

module Equations = struct
  module Flexible_type = Type

  module Rigid_type = struct
    module R_with_equiv = struct
      include R

      type 'a ctx =
        { mutable scopes : Scope_set.t
        ; assert_equiv :
            ctx:'a ctx
            -> create:('a t -> 'a)
            -> unify:(ctx:'a ctx -> 'a -> 'a -> unit)
            -> 'a t
            -> 'a t
            -> unit
        }

      let merge ~ctx ~create ~unify t1 t2 =
        let _, hd1 = head t1
        and _, hd2 = head t2 in
        if Head.(hd1 = hd2)
        then merge ~ctx:() ~create ~unify:(fun ~ctx:() a1 a2 -> unify ~ctx a1 a2) t1 t2
        else (
          ctx.assert_equiv ~ctx ~create ~unify t1 t2;
          t1)
      ;;
    end

    module S = Structure.First_order (R_with_equiv)
    include Unifier.Make (S) ()
    include Type
    include Make_unify (S)

    (** A rigid type is said to be principal if it contains no unification variables. *)
    exception Not_principal

    let var () = create Var
    let rigid_var rv = create (Structure (Var rv))
    let former f = create (Structure (Structure f))

    let fill_using_consistency_exn ~consistency t =
      let rec loop t =
        match structure t with
        | Var ->
          (match consistency with
           | `Consistent ->
             [%log.global.debug
               "Not principal error under consistent context (fill_using_consistency_exn)"];
             raise Not_principal
           | `Inconsistent -> set_structure t (Structure (Structure Bot)))
        | Structure s -> R_with_equiv.iter s ~f:loop
      in
      loop t
    ;;

    let to_flexible_type_exn ~(create : Flexible_type.t R.t -> Flexible_type.t) t =
      let rec loop t =
        match structure t with
        | Var ->
          [%log.global.debug
            "Not principal as type is unification variable (to_flexible_type_exn)"];
          raise Not_principal
        | Structure (Var rv) -> create (Var rv)
        | Structure (Structure former) -> create (Structure (F.map former ~f:loop))
      in
      loop t
    ;;

    module Principal = struct
      module T = struct
        type t = T of t R_with_equiv.t [@@deriving equal, compare, hash, sexp]
      end

      include T
      include Comparable.Make (T)

      let rigid_var rv = T (Var rv)
      let former f = T (Structure f)

      let rec of_rigid_type_exn rt =
        match structure rt with
        | Var ->
          [%log.global.debug
            "Not principal as type is a unification variable (of_rigid_type_exn)"];
          raise Not_principal
        | Structure (Var rv) -> rigid_var rv
        | Structure (Structure f) -> former (F.map f ~f:of_rigid_type_exn)
      ;;

      let of_former_exn f = former (F.map f ~f:of_rigid_type_exn)

      let is_scope_nil ft =
        match Flexible_type.inner ft with
        | Structure (Scope scr) -> Scope_row.is_nil scr
        | _ ->
          [%log.global.debug "Not principal as scope is not nil (is_scope_nil)"];
          raise Not_principal
      ;;

      let rec of_flexible_type_exn ft =
        match Flexible_type.inner ft with
        | Structure (Structure (Var rv)) -> rigid_var rv
        | Structure (Structure (Structure f)) -> former (F.map f ~f:of_flexible_type_exn)
        | Structure (Box (fscope, ft)) when is_scope_nil fscope -> of_flexible_type_exn ft
        | Var | Structure (Box _) ->
          [%log.global.debug
            "Not principal as flexible type is boxed / unification variable"
              (ft : Flexible_type.t)];
          raise Not_principal
        | Structure (Scope _) ->
          Aml_error.(
            raise @@ bugf ~here:[%here] "Kind error, expected a type not a scope")
      ;;

      let rec to_rigid_type (T s) =
        match s with
        | Var rv -> create (Structure (Var rv))
        | Structure former ->
          create (Structure (Structure (F.map former ~f:to_rigid_type)))
      ;;
    end

    let of_head_and_arity ~(head : R_with_equiv.Head.t) ~arity =
      match head with
      | Var rv ->
        assert (arity = 0);
        [], rigid_var rv
      | Structure Eq ->
        assert (arity = 2);
        let a1 = var () in
        let a2 = var () in
        [ a1; a2 ], former (Eq (a1, a2))
      | Structure Arrow ->
        assert (arity = 2);
        let a1 = var () in
        let a2 = var () in
        [ a1; a2 ], former (Arrow (a1, a2))
      | Structure (Constr type_ident) ->
        assert (arity >= 0);
        let as' = List.init arity ~f:(fun _ -> var ()) in
        as', former (Constr (as', type_ident))
      | Structure Bot ->
        assert (arity = 0);
        [], former Bot
    ;;
  end

  module Graph = struct
    module Node = Rigid_type.Principal

    module Adj_entry = struct
      module T = struct
        type t =
          { dst : Node.t
          ; scopes : Scope_set.t
          }
        [@@deriving equal, compare, hash, sexp]
      end

      include T
      include Comparable.Make (T)
    end

    type t = Adj_entry.Set.t Node.Map.t [@@deriving sexp]

    let empty = Node.Map.empty

    let add_edge_directed t ~src ~dst ~scopes =
      Map.update t src ~f:(function
        | None -> Adj_entry.Set.singleton { dst; scopes }
        | Some adj_entries -> Set.add adj_entries { dst; scopes })
    ;;

    let add_edge t ~n1 ~n2 ~scopes =
      t
      |> add_edge_directed ~src:n1 ~dst:n2 ~scopes
      |> add_edge_directed ~src:n2 ~dst:n1 ~scopes
    ;;

    let neighbours t n = Map.find t n |> Option.value ~default:Adj_entry.Set.empty

    (** [search ~stop ~src] performs a dfs through [t], stopping when the predicate [stop] is true. 
        It returns the scope set of the scopes encountered on the path.   *)
    let search t ~stop ~src : (Node.t * Scope_set.t) option =
      let visited = Hash_set.create (module Node) in
      let rec loop curr ~scopes =
        if stop curr
        then Some (curr, scopes)
        else (
          let neighbours =
            neighbours t curr
            |> Set.filter ~f:(fun entry -> not (Hash_set.mem visited entry.dst))
          in
          Set.find_map neighbours ~f:(fun entry ->
            Hash_set.add visited entry.dst;
            loop entry.dst ~scopes:(Scope_set.union scopes entry.scopes)))
      in
      loop src ~scopes:Scope_set.empty
    ;;

    let mem_path t ~src ~dst =
      let stop n = Node.(n = dst) in
      search t ~stop ~src |> Option.map ~f:snd
    ;;
  end

  type t =
    { equality_graph : Graph.t
    ; status : status
    }

  and status =
    | Consistent
    | Inconsistent of Scope_set.t
  [@@deriving sexp]

  let empty = { status = Consistent; equality_graph = Graph.empty }

  let is_inconsistent t =
    match t.status with
    | Consistent -> false
    | Inconsistent _ -> true
  ;;

  let expand_rigid_var t rv =
    let stop (Rigid_type.Principal.T s) =
      match s with
      | Structure _ -> true
      | Var _ -> false
    in
    Graph.search t.equality_graph ~stop ~src:(Rigid_type.Principal.rigid_var rv)
    |> Option.map ~f:(fun (drt, scopes) -> Rigid_type.Principal.to_rigid_type drt, scopes)
  ;;

  module type Assert_equiv = sig
    module R := Rigid_type.R_with_equiv

    (** A normalized equivalence is one that is fully expanded with respect to the equation graph. *)
    val assert_normalized_equiv
      :  scopes:Scope_set.t
      -> Rigid_type.Principal.t
      -> Rigid_type.Principal.t
      -> unit

    val use_scopes : Rigid_type.t R.ctx -> scopes:Scope_set.t -> Rigid_type.t R.ctx
    val assert_inconsistent : unit -> unit
  end

  let assert_equiv t (module Ae : Assert_equiv) ~ctx ~create ~unify s1 s2 =
    let module Prt = Rigid_type.Principal in
    let open Rigid_type.R_with_equiv in
    [%log.global.debug "Assert equiv" (s1 : Rigid_type.t R.t) (s2 : Rigid_type.t R.t)];
    match s1, s2 with
    | Var rv1, Var rv2 ->
      let prt1 = Prt.rigid_var rv1 in
      let prt2 = Prt.rigid_var rv2 in
      (match Graph.mem_path !t.equality_graph ~src:prt1 ~dst:prt2 with
       | None -> Ae.assert_normalized_equiv ~scopes:ctx.scopes prt1 prt2
       | Some scopes ->
         (* consume the scopes, but cannot propagate down the tree *)
         ignore (Ae.use_scopes ctx ~scopes : _ ctx))
    | Var rv, Structure f | Structure f, Var rv ->
      (match expand_rigid_var !t rv with
       | None ->
         [%log.global.debug
           "Added equation (var, struct)" (rv : Rigid_var.t) (f : Rigid_type.t F.t)];
         Ae.assert_normalized_equiv
           ~scopes:ctx.scopes
           (Prt.rigid_var rv)
           (Prt.of_former_exn f)
       | Some (rt, scopes) ->
         let ctx = Ae.use_scopes ctx ~scopes in
         unify ~ctx rt (create (Structure f)))
    | Structure _, Structure _ -> Ae.assert_inconsistent ()
  ;;

  let add_equation t rt1 rt2 ~scopes =
    match t.status with
    | Inconsistent incon_scopes when Scope_set.is_subset incon_scopes scopes -> t
    | _ ->
      let t = ref t in
      let update f = t := f !t in
      let module Assert_equiv = struct
        let assert_normalized_equiv ~scopes:scopes' drt1 drt2 =
          update
          @@ fun t ->
          { t with
            equality_graph =
              Graph.add_edge
                t.equality_graph
                ~n1:drt1
                ~n2:drt2
                ~scopes:(Scope_set.union scopes' scopes)
          }
        ;;

        let use_scopes ctx ~scopes =
          Rigid_type.R_with_equiv.{ ctx with scopes = Scope_set.union ctx.scopes scopes }
        ;;

        let assert_inconsistent () =
          update
          @@ fun t ->
          match t.status with
          | Consistent -> { t with status = Inconsistent scopes }
          | Inconsistent scopes' ->
            { t with status = Inconsistent (Scope_set.inter scopes' scopes) }
        ;;
      end
      in
      let assert_equiv = assert_equiv t (module Assert_equiv) in
      [%log.global.debug "Add equation (unify)" (rt1 : Rigid_type.t) (rt2 : Rigid_type.t)];
      Rigid_type.unify ~ctx:{ scopes = Scope_set.empty; assert_equiv } rt1 rt2;
      !t
  ;;

  let check_equiv t rt1 rt2 =
    let open Rigid_type.R_with_equiv in
    let module Assert_equiv = struct
      let assert_normalized_equiv ~scopes:_ _drt1 _drt2 = raise Cannot_merge

      let use_scopes ctx ~scopes =
        ctx.scopes <- Scope_set.union ctx.scopes scopes;
        ctx
      ;;

      let assert_inconsistent () = raise Cannot_merge
    end
    in
    let assert_equiv = assert_equiv (ref t) (module Assert_equiv) in
    try
      let ctx = { scopes = Scope_set.empty; assert_equiv } in
      Rigid_type.unify ~ctx rt1 rt2;
      Some (`Consistent, ctx.scopes)
    with
    | Rigid_type.Unify _ ->
      (match t.status with
       | Consistent -> None
       | Inconsistent scopes -> Some (`Inconsistent, scopes))
  ;;

  let check_equiv_using_input
        (type r1 r2)
        t
        ~create_type
        (ei1 : (Type.t, r1) A.Equiv_input.t)
        (ei2 : (Type.t, r2) A.Equiv_input.t)
    : (Scope_set.t * r1 * r2) option
    =
    let module Prt = Rigid_type.Principal in
    let fill_and_convert_args ~consistency args =
      [%log.global.debug
        "Check equiv (filling and converting args)" (args : Rigid_type.t list)];
      List.iter args ~f:(Rigid_type.fill_using_consistency_exn ~consistency);
      List.map args ~f:(Rigid_type.to_flexible_type_exn ~create:create_type)
    in
    match ei1, ei2 with
    | Type type1, Type type2 ->
      [%log.global.debug
        "Check equiv (Type, Type)" (type1 : Flexible_type.t) (type2 : Flexible_type.t)];
      let prt1 = Prt.of_flexible_type_exn type1 in
      let prt2 = Prt.of_flexible_type_exn type2 in
      check_equiv t (Prt.to_rigid_type prt1) (Prt.to_rigid_type prt2)
      |> Option.map ~f:(fun (_, scopes) -> scopes, (), ())
    | Type type_, Head { head; arity } ->
      [%log.global.debug
        "Check equiv (Type, Head)"
          (type_ : Flexible_type.t)
          (head : R.Head.t)
          (arity : int)];
      let prt = Prt.of_flexible_type_exn type_ in
      let rt_args, rt = Rigid_type.of_head_and_arity ~head ~arity in
      check_equiv t (Prt.to_rigid_type prt) rt
      |> Option.map ~f:(fun (consistency, scopes) ->
        scopes, (), fill_and_convert_args ~consistency rt_args)
    | Head { head; arity }, Type type_ ->
      [%log.global.debug
        "Check equiv (Head, Type)"
          (type_ : Flexible_type.t)
          (head : R.Head.t)
          (arity : int)];
      let prt = Prt.of_flexible_type_exn type_ in
      let rt_args, rt = Rigid_type.of_head_and_arity ~head ~arity in
      check_equiv t (Prt.to_rigid_type prt) rt
      |> Option.map ~f:(fun (consistency, scopes) ->
        scopes, fill_and_convert_args ~consistency rt_args, ())
    | Head h1, Head h2 ->
      [%log.global.debug
        "Check equiv (Head, Head)"
          (h1.arity : int)
          (h1.head : R.Head.t)
          (h2.arity : int)
          (h2.head : R.Head.t)];
      let rt1_args, rt1 = Rigid_type.of_head_and_arity ~head:h1.head ~arity:h1.arity in
      let rt2_args, rt2 = Rigid_type.of_head_and_arity ~head:h2.head ~arity:h2.arity in
      check_equiv t rt1 rt2
      |> Option.map ~f:(fun (consistency, scopes) ->
        ( scopes
        , fill_and_convert_args ~consistency rt1_args
        , fill_and_convert_args ~consistency rt2_args ))
  ;;
end

module State = struct
  type t =
    { id_source : (Identifier.source[@sexp.opaque])
    ; region_stack : Type.region_stack
    ; mutable curr_level : Level.t
    }
  [@@deriving sexp_of]

  let create () =
    { id_source = Identifier.create_source ()
    ; region_stack = Region_stack.create ()
    ; curr_level = Level.zero
    }
  ;;
end

open State
module Unify = Type.Make_unify (S)

module Young_region = struct
  type t =
    { region : Type.region
    ; level : Level.t
    ; mem : Type.t -> bool
      (** Returns [true] if given type is a member of the current region *)
    ; rigid_vars : Type.t list
      (** The list of rigid variables bound in the young region *)
    }
  [@@deriving sexp_of]

  let create ~state ~rigid_vars =
    let region = Region_stack.get_exn state.region_stack state.curr_level in
    let mem =
      let set =
        Hash_set.of_list (module Identifier) (region.types |> List.map ~f:Type.id)
      in
      fun type_ -> Hash_set.mem set (Type.id type_)
    in
    { region; level = state.curr_level; mem; rigid_vars }
  ;;
end

let region ~state ~level = Region_stack.get_exn state.region_stack level

let register_type ~state ~level type_ =
  Region.(register_type (region ~state ~level) type_)
;;

let create_type ~state inner =
  let type_ =
    Type.create (S.create ~id_source:state.id_source ~level:state.curr_level inner)
  in
  register_type ~state ~level:state.curr_level type_;
  type_
;;

let create_var ~state = create_type ~state Var
let create_scope ~state scope_set = create_type ~state (Structure (Scope scope_set))
let create_box ~state ~scope type_ = create_type ~state (Structure (Box (scope, type_)))

let create_rigid_var ~state =
  let rv = Rigid_var.create ~id_source:state.id_source () in
  create_type ~state (Structure (Structure (Var rv)))
;;

let create_former ~state former =
  create_type ~state (Structure (Structure (Structure former)))
;;

let unify ~state ~equations type1 type2 =
  let equiv ei1 ei2 =
    let create_type rigid = create_type ~state (Structure (Structure rigid)) in
    Equations.check_equiv_using_input equations ~create_type ei1 ei2
  in
  let unifier_ctx : _ S.ctx =
    { id_source = state.id_source
    ; curr_level = state.curr_level
    ; register_type = register_type ~state ~level:state.curr_level
    ; super = { super = (); equiv }
    }
  in
  Unify.unify ~ctx:unifier_ctx type1 type2
;;

exception Scope_escape of Type.t

let update_level type_ level =
  let structure = Type.structure type_ in
  match structure.status with
  | Generic ->
    Aml_error.(raise @@ bugf ~here:[%here] "Cannot update level of a generic type")
  | Instance level' ->
    if Level.(level < level')
    then (
      if Level.(level < S.scope_set structure) then raise (Scope_escape type_);
      Type.set_structure type_ { structure with status = Instance level })
;;

let update_levels (young_region : Young_region.t) =
  let visited = Hash_set.create (module Identifier) in
  let rec loop type_ lvl =
    let lvl' = Type.level_exn ~here:[%here] type_ in
    let id = Type.id type_ in
    if Hash_set.mem visited id
    then assert ((* Previously visited *) Level.(lvl' <= lvl))
    else (
      (* Visiting current node *)
      Hash_set.add visited id;
      (* Updating level of current node *)
      update_level type_ lvl;
      (* Handle children *)
      if young_region.mem type_
      then
        (* [type_] is in the current region, visit all the children *)
        Type.structure type_ |> S.iter ~f:(fun type_ -> loop type_ lvl)
      else (* [type_] is in an old region*) assert (Level.(lvl' < young_region.level)))
  in
  young_region.region.types
  |> List.sort ~compare:(Comparable.lift Level.compare ~f:(Type.level_exn ~here:[%here]))
  |> List.iter ~f:(fun type_ -> loop type_ (Type.level_exn ~here:[%here] type_))
;;

exception Rigid_variable_escape of Type.t

let scope_check_rigid_vars (young_region : Young_region.t) =
  match
    List.find young_region.rigid_vars ~f:(fun var ->
      Level.(Type.level_exn ~here:[%here] var < young_region.level))
  with
  | None -> ()
  | Some var -> raise (Rigid_variable_escape var)
;;

let is_dangerous ~rigid_vars type_ =
  let visited = Hash_set.create (module Identifier) in
  let exception Dangerous in
  let rec loop type_ =
    let id = Type.id type_ in
    if not (Hash_set.mem visited id)
    then (
      Hash_set.add visited id;
      if Hash_set.mem rigid_vars id then raise Dangerous;
      Type.structure type_ |> S.iter ~f:loop)
  in
  try
    loop type_;
    false
  with
  | Dangerous -> true
;;

let close_scope scope =
  let structure = Type.structure scope in
  match structure.inner with
  | Var ->
    Type.set_structure scope { structure with inner = Structure (Scope Scope_row.nil) }
  | Structure (Scope scope_row) ->
    assert (Scope_set.(equal empty scope_row.scopes));
    Type.set_structure scope { structure with inner = Structure (Scope Scope_row.nil) }
  | _ -> assert false
;;

let close_dangerous_scopes ~rigid_vars type_ =
  match Type.inner type_ with
  | Structure (Box (scope, box_type)) when is_dangerous ~rigid_vars box_type ->
    close_scope scope;
    Type.unsafe_link ~src:type_ ~dst:box_type
  | _ -> ()
;;

let generalize_young_region ~state (young_region : Young_region.t) =
  let rigid_vars =
    Hash_set.of_list (module Identifier) (List.map young_region.rigid_vars ~f:Type.id)
  in
  let young_level = young_region.level in
  let generics =
    young_region.region.types
    |> List.filter ~f:(fun type_ ->
      Type.is_representative type_
      &&
      let level = Type.level_exn ~here:[%here] type_ in
      if Level.(level < young_level)
      then (
        register_type ~state ~level type_;
        false)
      else (
        assert (Level.(level = young_level));
        close_dangerous_scopes ~rigid_vars type_;
        Type.set_status type_ Generic;
        true))
  in
  generics
;;

let enter ~state =
  state.curr_level <- Level.succ state.curr_level;
  Region_stack.push state.region_stack
;;

let update_levels_check_rigids_and_generalize_young_region ~state ~rigid_vars =
  let young_region = Young_region.create ~state ~rigid_vars in
  update_levels young_region;
  scope_check_rigid_vars young_region;
  generalize_young_region ~state young_region
;;

let exit ~state ~rigid_vars ~types =
  let generics =
    update_levels_check_rigids_and_generalize_young_region ~state ~rigid_vars
  in
  (* flexize rigid variables *)
  List.iter rigid_vars ~f:(fun type_ -> Type.set_inner type_ Var);
  let create_scheme = fun root -> Scheme.{ root } in
  Region_stack.pop state.region_stack;
  state.curr_level <- Level.prev state.curr_level;
  generics, List.map types ~f:create_scheme
;;

let instantiate ~state ({ root } : Type.t Scheme.t) =
  let copies = Hashtbl.create (module Identifier) in
  let rec loop type_ =
    let structure = Type.structure type_ in
    match structure.status with
    | Instance _ -> type_
    | Generic ->
      (try Hashtbl.find_exn copies structure.id with
       | Not_found_s _ ->
         let copy = create_var ~state in
         Hashtbl.set copies ~key:structure.id ~data:copy;
         Type.set_inner copy (S.Inner.copy ~f:loop structure.inner);
         copy)
  in
  loop root
;;

let add_equation ~state equations type1 type2 =
  let scopes = state.curr_level in
  Equations.add_equation equations ~scopes type1 type2
;;

let generalize_root_region ~state =
  assert (Level.(state.curr_level = zero));
  ignore
    (update_levels_check_rigids_and_generalize_young_region ~state ~rigid_vars:[]
     : Type.t list)
;;
