type t
type variable = Polynomes.Var.t
type term = Polynomes.t
type sigma = Equal | Less
type contraint = Polynomes.t * sigma

val create : unit -> t
val create_variable : t -> string -> variable
val variables : t -> variable array
val t_to_poly_ctx : t -> Polynomes.ctx
val t_to_constraints : t -> contraint Dynarray.t
val pp : t Fmt.t

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

type res =
  | Sat of (Polynomes.Var.t * Real.t) list
  | Unsat of Covering.intervalPoly list

val evaluate_contraint :
  t -> contraint -> Polynomes.Assignment.t -> Real.t -> bool

val pp_array_of_constraints : Format.formatter -> contraint array -> unit

val get_unsat_intervals :
  t -> contraint array -> Polynomes.Assignment.t -> Covering.intervalPoly list

val construct_characterization :
  t -> Polynomes.Assignment.t -> Covering.intervalPoly list -> Polynomes.Set.t

val interval_from_charachterization :
  t ->
  variable ->
  Polynomes.Assignment.t ->
  Real.t ->
  Polynomes.Set.t ->
  Covering.intervalPoly

val get_unsat_cover : t -> res
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
  | Sat of (Polynomes.Var.t * Real.t) list  (** The problem is satisfiable. *)
  | Unsat  (** The problem is not satisfiable. *)
  | Unknown
      (** The problem was not solved. The goal is to implement a {b complete}
          solver, so this should never happen once the project is complete. *)

val solve : t -> solve_result
val sat_to_assignment : Format.formatter -> t -> solve_result -> unit
val show_sat_or_unsat : t -> solve_result -> string

module Covering : module type of Covering
module Real : module type of Real
module Constraint : module type of Constraint
module Z_poly : module type of Z_poly
module Polynomes : module type of Polynomes
