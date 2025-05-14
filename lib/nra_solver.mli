type t
type variable
type term

val create : unit -> t
val create_variable : t -> string -> variable

module Term : sig
  val variable : variable -> term
  val real : string -> term
  val minus : term -> term
  val add : term -> term -> term
  val sub : term -> term -> term
  val mul : term -> term -> term
  val div : term -> term -> term
end

val assert_eq : t -> term -> term -> unit
val assert_neq : t -> term -> term -> unit
val assert_lt : t -> term -> term -> unit
val assert_leq : t -> term -> term -> unit
val assert_gt : t -> term -> term -> unit
val assert_geq : t -> term -> term -> unit

type solve_result =
  | Sat  (** The problem is satisfiable. *)
  | Unsat  (** The problem is not satisfiable. *)
  | Unknown
      (** The problem was not solved. The goal is to implement a {b complete}
          solver, so this should never happen once the project is complete. *)

val solve : t -> solve_result

module Covering : module type of Covering
module Real : module type of Real
module Constraint : module type of Constraint
module Z_poly : module type of Z_poly
