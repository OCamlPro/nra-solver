type sigma = Equal | Less
type contraint = Polynomes.t * sigma

val array_filtrer :
  contraint array ->
  Polynomes.Assignment.t ->
  (contraint -> Polynomes.Assignment.t -> bool) ->
  contraint array

val sorts_array : Real.t array -> Real.t array
val is_poly_constant : contraint -> Polynomes.Assignment.t -> bool
val evaluate_contraint : contraint -> Polynomes.Assignment.t -> Real.t -> bool
val val_pick : Covering.interval -> Real.t

val list_intervals :
  contraint ->
  Polynomes.Assignment.t ->
  Covering.interval list ->
  Covering.interval list ->
  Covering.interval list

val get_unsat_intervals :
  contraint array -> Polynomes.Assignment.t -> Covering.interval list

val pp_constraint : Format.formatter -> contraint -> unit
val pp_array_of_constraints : Format.formatter -> contraint array -> unit

(************************************************************************************************)

(************************************************************************************************)
