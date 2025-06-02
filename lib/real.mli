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

  val pp : Format.formatter -> t -> unit 


