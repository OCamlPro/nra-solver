type t

val normalize  : t -> t 
val l_coeff : t -> Z_poly.t 
val required_coefficient : Real.t array -> t -> Z_poly.t list  
val pp : Format.formatter -> t -> unit 
val mk_poly : (int list * int) list -> Z_poly.t 
val mk_poly_array : (int list * int) list array -> t
val p : t