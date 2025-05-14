module Index : sig
  type t = int array

  val compare : t -> t -> int

  (*val gen : t QCheck2.Gen.t*)
  val pp : t Fmt.t
end

type t
(** Type of integer multivariate polynomial. *)

val zero : t
(** Zero polynomial. *)

val make : (Index.t * Z.t) list -> t
val evaluate : t -> Real.t array -> Real.t
val equal : t -> t -> bool
val pp : Format.formatter -> t -> unit
