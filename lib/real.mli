type t

val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val of_int : int -> t
val floor : t -> Z.t
val ceil : t -> Z.t
val neg : t -> t
val add : t -> t -> t
val sub : t -> t -> t
val sqrt : t -> t
val div : t -> t -> t
