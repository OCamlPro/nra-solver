type bound = Finite of Real.t | Pinf | Ninf

val compare_bound : bound -> bound -> int
val max_bound : bound -> bound -> bound
val min_bound : bound -> bound -> bound


type interval =
  | Open of bound * bound
  | Exact of Real.t  (** Represents a non-empty interval. *)

  type intervalPoly = {
    interval : interval;
    u_bound : bound; 
    l_bound : bound;
    u_set : Polynomes.Set.t;
    l_set : Polynomes.Set.t;
    p_set : Polynomes.Set.t ;
    p_orthogonal_set : Polynomes.Set.t;
  }

val make_open : bound -> bound -> interval
val make_exact : Real.t -> interval
val pp_interval : Format.formatter -> interval -> unit
val pp_intervals : Format.formatter -> interval list -> unit
val pp_debug_intervals : Format.formatter -> interval list -> unit
val show_intervals : interval list -> string
val pp_bound : Format.formatter -> bound -> unit
val is_covering : interval list -> bool
val is_good_covering : interval list -> bool
val compute_good_covering : interval list -> interval list
val sample_outside : interval list -> Real.t option
val sample_interval :bound -> bound -> Real.t  
val compare_interval : interval -> interval -> int
val equal_interval : interval -> interval -> bool
val sort_intervals1 : interval list -> interval list
val interval_to_intervalPoly : interval -> Polynomes.t -> intervalPoly
val intervalpoly_to_interval : intervalPoly list -> interval list 
val compute_cover : intervalPoly list -> intervalPoly list 

val length : interval -> Real.t
(** [length i] computes the length of the interval [i]. raise invalide argument
    if the length is infinity *)

val inter : interval -> interval -> interval option
(** [inter i1 i2] computes the intersection of [i1] and [i2]. Returns [None] if
    the intersection is empty. *)
val pointsToIntervals : Real.t array -> interval list
val pointsToIntervals2 : Real.t list -> interval list 
