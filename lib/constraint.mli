type sigma = Equal | Less
type contraint = Polynomes.t * sigma

type res =
  | Sat of (Polynomes.Var.t * Real.t) list
  | Unsat of Covering.intervalPoly list

val array_filtrer :
  contraint array ->
  Polynomes.Assignment.t ->
  (contraint -> Polynomes.Assignment.t -> bool) ->
  contraint array

val array_filtrer2 : contraint array -> (contraint -> bool) -> contraint array
val sorts_array : Real.t array -> Real.t array
val list_coefficients : contraint -> Polynomes.t list
val is_poly_non_constant : Polynomes.t -> bool
val is_poly_nul : contraint -> Polynomes.Assignment.t -> bool
val evaluate_contraint : contraint -> Polynomes.Assignment.t -> Real.t -> bool
val val_pick : Covering.interval -> Real.t

val get_unsat_intervals :
  contraint array -> Polynomes.Assignment.t -> Covering.intervalPoly list

val pp_constraint : Format.formatter -> contraint -> unit
val pp_array_of_constraints : Format.formatter -> contraint array -> unit
val get_unsat_cover : contraint array -> Polynomes.Var.t array -> res
val sat_to_assignment : Format.formatter -> res -> unit
val show_sat_or_unsat : res -> string

(************************************************************************************************)

(************************************************************************************************)
