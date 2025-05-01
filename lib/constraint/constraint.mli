open Aml_std
open Grace

(** A set of variables for scopes *)
module Scope : Var.S

(** The module [Type] provides the concrete representation of types
    (using constraint type variables) in constraints. *)
module Type : sig
  module Ident : Var.S
  module Var : Var.S

  (** [t] represents the type [tau]. *)
  type t =
    | Var of Var.t (** [ɑ] *)
    | Arrow of t * t (** [tau1 -> tau2] *)
    | Eq of t * t (** [tau1 = tau2] *)
    | Bot (** [bot] *)
    | Constr of t list * Ident.t (** [(tau1, ..., taun) F] *)
    | Scope_nil (** [emptyset] *)
    | Scope_snoc of t * Scope.t (** [Phi, phi] *)
    | Box of t * t (** [[Phi]tau] *)
  [@@deriving sexp]

  val var : Var.t -> t
  val ( @-> ) : t -> t -> t
  val eq : t -> t -> t
  val bot : t
  val constr : t list -> Ident.t -> t
  val box : t -> t -> t

  module Scope : sig
    val nil : t
    val snoc : t -> Scope.t -> t
  end

  module Kind : sig
    (** [t] is kinded, either representing a [Scope] or a traditional [Type]. *)
    type t =
      | Scope
      | Type
    [@@deriving sexp]
  end

  type binder = Var.t * Kind.t [@@deriving sexp]
end

module Var : Var.S

(** [t] is a constraint *)
type t =
  | True (** [true] *)
  | False of Aml_error.t (** [false] *)
  | Conj of t * t (** [C1 /\ C2] *)
  | Eq of Type.t * Type.t (** [tau1 = tau2] *)
  | Exists of Type.binder * t (** [exists a :: k. C]*)
  | Let of Var.t * lambda * t (** [let x = lambda in C] *)
  | App of Var.t * Type.t (** [x tau] *)
  | Implication of Scope.t * Type.t * Type.t * t (** [phi : tau1 = tau2 => C]*)
  | Absurd of Aml_error.t (** [absurd] *)
  | With_range of t * Range.t (** [C^ell] *)

(** [lambda] is a rigid constraint abstraction [forall overline(a :: kappa). λb. C] *)
and lambda =
  { rigid_type_vars : Type.binder list
  ; type_var : Type.Var.t
  ; body : t
  }
[@@deriving sexp]

val tt : t
val ff : Aml_error.t -> t
val ( &~ ) : t -> t -> t
val all : t list -> t
val ( =~ ) : Type.t -> Type.t -> t
val exists : Type.binder -> t -> t
val exists_many : Type.binder list -> t -> t
val ( #= ) : Var.t -> lambda -> Var.t * lambda
val fun_ : ?rigid_type_vars:Type.binder list -> Type.Var.t -> t -> lambda
val let_ : Var.t * lambda -> in_:t -> t
val app : Var.t -> Type.t -> t
val with_range : t -> range:Range.t -> t

type equation_binder := Scope.t * (Type.t * Type.t)

val ( @: ) : Scope.t -> Type.t * Type.t -> equation_binder
val ( @=> ) : equation_binder -> t -> t
val absurd : Aml_error.t -> t
