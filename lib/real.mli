type t = Libpoly.Value.t

include module type of Libpoly.Value with type t := t

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

val max : t -> t -> t
val min : t -> t -> t
val pp : Format.formatter -> t -> unit
val pp_array_of_real : Format.formatter -> t array -> unit
val real_array_ro_string : t array -> string 
