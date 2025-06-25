type t
type variable = Libpoly.Variable.t
type term

val create : unit -> t
val create_variable : t -> string -> variable

module Term : sig
  val variable : t -> variable -> term
  val real : t -> string -> term
  val minus : t -> term -> term
  val add : t -> term -> term -> term
  val sub : t -> term -> term -> term
  val mul : t -> term -> term -> term
  val div : t -> term -> term -> term
end

val assert_eq : t -> term -> term -> unit
val assert_neq : t -> term -> term -> unit
val assert_lt : t -> term -> term -> unit
val assert_leq : t -> term -> term -> unit
val assert_gt : t -> term -> term -> unit
val assert_geq : t -> term -> term -> unit

(*
  let t = create () in
  let x = create_variable t "x" in
  let y = create_variable t "y" in
  let p = Term.(add t (variable x) (variable y)) in
  let q = Term.(mul t (variable x) (variable y)) in
  assert_eq t p q; (* p = q *)
  assert_neq t p q; (* p <> q *)
  solve t
*)

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
module Polynomes : module type of Polynomes
