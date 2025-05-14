type sigma = Equal | Less
type polyn = Z_poly.t array
type contraint = polyn * sigma

val pp_constraint : Format.formatter -> contraint -> unit
val is_poly_nul : contraint -> Real.t array -> bool
val specialize_poly : contraint -> Real.t array -> Real.Poly.t
val array_filtrer : Real.t array -> (Real.t -> bool) -> Real.t array
val sorts_array : Real.t array -> Real.t array
val real_roots : Real.Poly.t -> Real.t array
val num_roots : Real.Poly.t -> int
val evaluate_contraint : contraint -> Real.t array -> Real.t -> bool
val val_pick : Covering.interval -> Real.t

exception Break of Covering.interval list

val list_intervals :
  contraint ->
  Real.t array ->
  Covering.interval list ->
  Covering.interval list ->
  Covering.interval list

val get_unsat_intervals :
  contraint array -> Real.t array -> Covering.interval list

val mk_poly : (int list * int) list -> Z_poly.t
val mk_constraint : (int list * int) list array -> sigma -> contraint

(************************************************************************************************)

(************************************************************************************************)

type degres =
  int list (* Une liste d'entiers représentant les degrés de chaque variable *)

type monome_multi_variable = Real.t * degres
type polynome_multi_variable = monome_multi_variable list
type comparaison = Inferieur | Egal
type constraints = polynome_multi_variable * comparaison

val substituer_monome :
  monome_multi_variable -> Real.t list -> monome_multi_variable option

val substituer_polynome :
  polynome_multi_variable -> Real.t list -> polynome_multi_variable

val pp_monome : Format.formatter -> monome_multi_variable -> unit
val pp_poly : Format.formatter -> polynome_multi_variable -> unit
val show_poly : polynome_multi_variable -> string
