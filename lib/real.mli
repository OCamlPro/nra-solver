type t
type real = t

val compare : t -> t -> int
val pp : Format.formatter -> t -> unit
val show : t -> string
val of_int : int -> t
val is_real : t -> bool
val to_q : t -> Q.t option
val floor : t -> Z.t
val ceil : t -> Z.t
val neg : t -> t
val add : t -> t -> t
val sub : t -> t -> t
val sqrt : t -> t
val div : t -> t -> t
val max : t -> t -> t
val min : t -> t -> t
val pow : t -> Q.t -> t
val mul : t -> t -> t
val of_z : Z.t -> t

module Syntax : sig
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( ~$ ) : int -> t
  val ( < ) : t -> t -> bool
  val ( <= ) : t -> t -> bool
  val ( > ) : t -> t -> bool
  val ( >= ) : t -> t -> bool
  val ( = ) : t -> t -> bool
end

module Poly : sig
  type t

  val create : real array -> t
  val evaluate : t -> real -> real
  val add : t -> t -> t
  val mul : t -> t -> t
  val sub : t -> t -> t
  val roots : t -> real array
  val to_string : t -> string
  val pp : Format.formatter -> t -> unit
end
