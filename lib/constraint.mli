type sigma = Equal | Less
type contraint = Polynomes.t * sigma

type res =
  | Sat of (Polynomes.Var.t * Real.t) list
  | Unsat of Covering.intervalPoly list

val array_filtrer2 : contraint array -> (contraint -> bool) -> contraint array
val list_coefficients : Polynomes.ctx -> contraint -> Polynomes.t list
val is_poly_non_constant : Polynomes.ctx -> Polynomes.t -> bool
val is_poly_nul : Polynomes.ctx -> contraint -> Polynomes.Assignment.t -> bool

val evaluate_contraint :
  Polynomes.ctx -> contraint -> Polynomes.Assignment.t -> Real.t -> bool

val get_unsat_intervals :
  Polynomes.ctx ->
  contraint array ->
  Polynomes.Assignment.t ->
  Covering.intervalPoly list

val pp_constraint : Format.formatter -> contraint -> unit
val pp_array_of_constraints : Format.formatter -> contraint array -> unit

val get_unsat_cover :
  Polynomes.ctx -> contraint array -> Polynomes.Var.t array -> res

val sat_to_assignment : Format.formatter -> res -> unit
val show_sat_or_unsat : res -> string

(************************************************************************************************)

(************************************************************************************************)
