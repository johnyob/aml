open! Import

module type S = Aml_unifier.Structure.S

module type S_with_head = sig
  include S

  module Head : sig
    type t [@@deriving sexp, equal, compare, hash]
  end

  (** [head t] returns the head of [t] along with all the children of [t]'s head. *)
  val head : 'a t -> 'a list * Head.t
end

module Type_ident = Constraint.Type.Ident

module Rigid_var = Var.Make (struct
    let module_name = "Rigid_var"
  end)

module Former = struct
  type 'a t =
    | Arrow of 'a * 'a
    | Eq of 'a * 'a
    | Constr of 'a list * Type_ident.t
    | Bot
  [@@deriving equal, compare, hash, sexp]

  type 'a ctx = unit

  exception Cannot_merge

  let iter t ~f =
    match t with
    | Arrow (t1, t2) | Eq (t1, t2) ->
      f t1;
      f t2
    | Constr (ts, _) -> List.iter ts ~f
    | Bot -> ()
  ;;

  let map t ~f =
    match t with
    | Arrow (t1, t2) -> Arrow (f t1, f t2)
    | Eq (t1, t2) -> Eq (f t1, f t2)
    | Constr (ts, constr) -> Constr (List.map ts ~f, constr)
    | Bot -> Bot
  ;;

  let copy t ~f = map t ~f

  let fold t ~f ~init =
    match t with
    | Arrow (t1, t2) | Eq (t1, t2) -> f t2 (f t1 init)
    | Constr (ts, _) -> List.fold_right ts ~f ~init
    | Bot -> init
  ;;

  let merge ~ctx ~create:_ ~unify t1 t2 =
    match t1, t2 with
    | Arrow (t11, t12), Arrow (t21, t22) | Eq (t11, t12), Eq (t21, t22) ->
      unify ~ctx t11 t21;
      unify ~ctx t12 t22;
      t1
    | Constr (ts1, constr1), Constr (ts2, constr2) when Type_ident.(constr1 = constr2) ->
      (match List.iter2 ts1 ts2 ~f:(unify ~ctx) with
       | Ok () -> t1
       | Unequal_lengths -> assert false)
    | Bot, Bot -> t1
    | _ -> raise Cannot_merge
  ;;

  module Head = struct
    module T = struct
      type t =
        | Arrow
        | Eq
        | Constr of Type_ident.t
        | Bot
      [@@deriving sexp, equal, compare, hash]
    end

    include T
    include Comparable.Make (T)
  end

  let head t =
    match t with
    | Arrow (t1, t2) -> [ t1; t2 ], Head.Arrow
    | Eq (t1, t2) -> [ t1; t2 ], Eq
    | Constr (ts, constr) -> ts, Constr constr
    | Bot -> [], Bot
  ;;
end

module Rigid (S : S_with_head) = struct
  type 'a t =
    | Var of Rigid_var.t
    | Structure of 'a S.t
  [@@deriving equal, compare, hash, sexp]

  exception Cannot_merge = S.Cannot_merge

  type 'a ctx = 'a S.ctx

  let iter t ~f =
    match t with
    | Var _rv -> ()
    | Structure s -> S.iter s ~f
  ;;

  let fold t ~f ~init =
    match t with
    | Var _rv -> init
    | Structure s -> S.fold s ~f ~init
  ;;

  let copy t ~f =
    match t with
    | Var rv -> Var rv
    | Structure s -> Structure (S.copy s ~f)
  ;;

  let merge ~ctx ~create ~unify t1 t2 =
    match t1, t2 with
    | Var rv1, Var rv2 -> if Rigid_var.(rv1 = rv2) then t1 else raise Cannot_merge
    | Var _, Structure _ | Structure _, Var _ -> raise Cannot_merge
    | Structure s1, Structure s2 ->
      let create s = create (Structure s) in
      Structure (S.merge ~ctx ~create ~unify s1 s2)
  ;;

  module Head = struct
    module T = struct
      type t =
        | Var of Rigid_var.t
        | Structure of S.Head.t
      [@@deriving sexp, equal, compare, hash]
    end

    include T
    include Comparable.Make (T)
  end

  let head t =
    match t with
    | Var rv -> [], Head.Var rv
    | Structure s ->
      let as', hs = S.head s in
      as', Structure hs
  ;;
end

module Scoped_ambivalent
    (S : S_with_head)
    (Scope_set : sig
       type t [@@deriving sexp, equal, compare, hash]

       val empty : t
       val union : t -> t -> t
     end) =
struct
  exception Cannot_merge = S.Cannot_merge

  module Scope_row = struct
    type t =
      { scopes : Scope_set.t
      ; is_closed : bool
      }
    [@@deriving equal, compare, hash, sexp]

    let open_ scopes = { scopes; is_closed = false }
    let nil = { scopes = Scope_set.empty; is_closed = true }
    let is_nil t = t.is_closed && Scope_set.(equal t.scopes empty)

    let merge t1 t2 =
      if t1.is_closed && t2.is_closed
      then (
        if not (Scope_set.equal t1.scopes t2.scopes) then raise Cannot_merge;
        t1)
      else (
        let scopes = Scope_set.union t1.scopes t2.scopes in
        { scopes; is_closed = t1.is_closed || t2.is_closed })
    ;;
  end

  type 'a t =
    | Scope of Scope_row.t
    | Box of 'a * 'a
    | Structure of 'a S.t
  [@@deriving equal, compare, hash, sexp]

  module Equiv_input = struct
    type ('a, 'r) t =
      | Type : 'a -> ('a, unit) t
      (** A rigid type as an input to [equiv], returns nothing *)
      | Head :
          { head : S.Head.t
          ; arity : int
          }
          -> ('a, 'a list) t
      (** A structure head as an input to [equiv], returns the set of rigid children 
          used in the equivalence *)
    [@@deriving sexp_of]
  end

  type 'a ctx =
    { super : 'a S.ctx
    ; equiv :
        'r1 'r2.
        ('a, 'r1) Equiv_input.t
        -> ('a, 'r2) Equiv_input.t
        -> (Scope_set.t * 'r1 * 'r2) option
      (** [equiv ei1 ei2] returns the scope [scs] and types s.t [sc |- ei1 == ei2]
          See [Equiv_input] for a description of the return types.  
          If the two inputs are not equivalent under the current context, then [None] is returned.     
      *)
    }

  let iter t ~f =
    match t with
    | Scope _ -> ()
    | Box (scr, t) ->
      f scr;
      f t
    | Structure s -> S.iter s ~f
  ;;

  let copy t ~f =
    match t with
    | Scope scr -> Scope scr
    | Box (scr, t) -> Box (f scr, f t)
    | Structure s -> Structure (S.copy s ~f)
  ;;

  let fold t ~f ~init =
    match t with
    | Scope _ -> init
    | Box (sc, t) -> f sc (f t init)
    | Structure s -> S.fold s ~f ~init
  ;;

  let merge (type a) ~ctx ~create ~unify (t1 : a t) (t2 : a t) =
    (* [a1 =~ a2] unifies the variables [a1] and [a2] *)
    let ( =~ ) = unify ~ctx in
    (* [a =~- s] imposes the structure [s] on the variable [a] *)
    let[@always_inline] ( =~- ) a s = a =~ create s in
    (* [ei1 ==? ei2] asserts that [ei1] and [ei2] are equivalent using [ctx.equiv]. 
       If they are not, then it raises [Cannot_merge] *)
    let ( ==? ) ei1 ei2 =
      match ctx.equiv ei1 ei2 with
      | Some r -> r
      | None -> raise Cannot_merge
    in
    (* [impose_scopes ~scope_row as rts] imposes the structure [[scope_row]rt_i] on 
       every variable [a_i]. *)
    let impose_scopes ~scope_row as' rts =
      match List.iter2 as' rts ~f:(fun a rt -> a =~- Box (scope_row, rt)) with
      | Ok () -> ()
      | Unequal_lengths -> assert false
    in
    match t1, t2 with
    | Scope scr1, Scope scr2 -> Scope (Scope_row.merge scr1 scr2)
    | Box (scr, rt), Structure s | Structure s, Box (scr, rt) ->
      let as', hs = S.head s in
      if List.is_empty as'
      then (
        (* The structure [s] has no children, meaning we cannot apply 
           distributivity of scopes. This implies [scr] must be [empty]. *)
        (* assert that [empty |- rt == [] hs] *)
        let scopes, (), rts = Type rt ==? Head { head = hs; arity = 0 } in
        assert (List.is_empty rts);
        if not Scope_set.(equal scopes empty) then raise Cannot_merge;
        (* assert [scr = emptyset] *)
        scr =~- Scope Scope_row.nil)
      else (
        (* assert that [scopes |- rt == rts hs] *)
        let scopes, (), rts = Type rt ==? Head { head = hs; arity = List.length as' } in
        (* assert [exists 's. scr = 'a, scopes] *)
        scr =~- Scope (Scope_row.open_ scopes);
        (* Every child [a_i] of the structure [s] must be a scoped 
           ambivalent type of the form [[scr]rt_i] *)
        impose_scopes ~scope_row:scr as' rts);
      (* We favour [Structure] over [Box] because [Structure] is more 
         intuitive for programmers. *)
      Structure s
    | Box (scr1, rt1), Box (scr2, rt2) ->
      (* assert that [scopes |- rt1 == rt2] *)
      let scopes, (), () = Type rt1 ==? Type rt2 in
      (* assert that [scr1 = scr2] *)
      scr1 =~ scr2;
      (* assert that [exists 's. scr1 = scr2 = 's, scopes] *)
      scr1 =~- Scope (Scope_row.open_ scopes);
      (* Pick arbitrary structure, could alternatively be [t2] *)
      t1
    | Structure s1, Structure s2 ->
      let as1, hs1 = S.head s1
      and as2, hs2 = S.head s2 in
      (* If the heads are equal or we cannot apply distributivity of scopes, 
         then equate the structures as usual. *)
      if S.Head.equal hs1 hs2 || List.is_empty as1 || List.is_empty as2
      then
        Structure
          (S.merge
             ~ctx:ctx.super
             ~create:(fun s -> create (Structure s))
             ~unify:(fun ~ctx:super a1 a2 -> unify ~ctx:{ ctx with super } a1 a2)
             s1
             s2)
      else (
        let scopes, rts1, rts2 =
          Head { head = hs1; arity = List.length as1 }
          ==? Head { head = hs2; arity = List.length as2 }
        in
        let scr = create (Scope (Scope_row.open_ scopes)) in
        (* Every child of [s1] (and [s2] resp.) must be a scoped ambivalent 
           type of the form [[scr]rt1_i] ([[scr]rt2_i] resp.) *)
        impose_scopes ~scope_row:scr as1 rts1;
        impose_scopes ~scope_row:scr as2 rts2;
        (* Pick arbitrary structure, could alternatively be [t2] *)
        t1)
    | Scope _, (Structure _ | Box _) | (Structure _ | Box _), Scope _ ->
      (* Kind mismatch *)
      raise Cannot_merge
  ;;
end

module First_order (S : S) = struct
  type 'a t =
    | Var
    | Structure of 'a S.t
  [@@deriving equal, compare, hash, sexp]

  type 'a ctx = 'a S.ctx

  exception Cannot_merge = S.Cannot_merge

  let iter t ~f =
    match t with
    | Var -> ()
    | Structure s -> S.iter s ~f
  ;;

  let fold t ~f ~init =
    match t with
    | Var -> init
    | Structure s -> S.fold s ~f ~init
  ;;

  let copy t ~f =
    match t with
    | Var -> Var
    | Structure s -> Structure (S.copy s ~f)
  ;;

  let merge ~ctx ~create ~unify t1 t2 =
    match t1, t2 with
    | Var, t | t, Var -> t
    | Structure s1, Structure s2 ->
      let create s = create (Structure s) in
      Structure (S.merge ~ctx ~create ~unify s1 s2)
  ;;
end
