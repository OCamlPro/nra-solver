type bound = Finite of Real.t | Pinf | Ninf

val compare_bound : bound -> bound -> int

type interval = Open of bound * bound | Exact of Real.t

val make_open : bound -> bound -> interval
val make_exact : Real.t -> interval
val pp_interval : Format.formatter -> interval -> unit
val pp_intervals : Format.formatter -> interval list -> unit
val pp_bound : Format.formatter -> bound -> unit
val is_covering : interval list -> bool
val is_good_covering : interval list -> bool
val compute_good_covering : interval list -> interval list
val sample_outside : interval list -> Real.t option
val compare_interval : interval -> interval -> int
val equal_interval : interval -> interval -> bool
val sort_intervals1 : interval list -> interval list
