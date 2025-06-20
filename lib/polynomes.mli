type t

module Var : sig
  type t

  val create : string -> t
  val compare : t -> t -> int
  val of_index : int -> t
  val get_name : t -> string
end

module Assignment : sig
  type t

  val to_libpoly_assignment : t -> Libpoly.Assignment.t
  val empty : t
  val add : Var.t -> Real.t -> t -> t
  val pp_assignment : Format.formatter -> t -> unit
  val to_list : t -> (Var.t * Real.t) list
  val of_list : (Var.t * Real.t) list -> t
end

val to_string : t -> string
val string_of_polynomial_list : t list -> string
val pp : Format.formatter -> t -> unit
val create : unit -> t
val resultant : t -> t -> t
val gcd : t -> t -> t
val sgn : t -> Assignment.t -> int
val evaluate : t -> Assignment.t -> Real.t
val add : t -> t -> t
val sub : t -> t -> t
val neg : t -> t
val mul : t -> t -> t
val div : t -> t -> t
val roots_isolate : t -> Assignment.t -> Real.t array
val reductum : t -> t
val derivative : t -> t
val primitive : t -> t
val disc : t -> t
val eq : t -> t -> int
val is_constant : t -> int
val is_zero : t -> int
val top_variable : t -> Var.t
val degree : t -> int
val get_coefficient : t -> int -> t
val mult_list_polynomes : int -> t list -> t
val mk_assignment : Var.t list -> int list -> Assignment.t
val mk_monomes : Var.t list -> int * int list -> t
val mk_polynomes : Var.t list -> (int * int list) list -> t

(*module Syntax : sig
    val ( ~$ ) : Var.t -> t
    val ( ~$$ ) : Z.t -> t
    val ( + ) : t -> t -> t
    val ( * ) : t -> t -> t
  end*)

(*

let x = Var.create "x" in 
let y = Var.create "y" in

let p = Poly.Syntax.(~$$50 * ~$x + ~$x * ~$y)

*)
module Set : Stdlib.Set.S with type elt = t
module Map : Stdlib.Map.S with type key = t

val required_coefficient : Assignment.t -> t -> Set.t
val required_coefficients : Assignment.t -> Set.t -> Set.t
val to_list : Set.t -> t list
val of_list : t list -> Set.t
