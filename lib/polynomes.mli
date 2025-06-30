type t
type ctx

val create_context : unit -> ctx

module Var : sig
  type t

  val create : ctx -> string -> t
  val compare : ctx -> t -> t -> int
  val pp : ctx -> t Fmt.t
end

module Assignment : sig
  type t

  val to_libpoly_assignment : ctx -> t -> Libpoly.Assignment.t
  val empty : t
  val add : Var.t -> Real.t -> t -> t
  val pp_assignment : ctx -> Format.formatter -> t -> unit
  val to_list : t -> (Var.t * Real.t) list
  val of_list : (Var.t * Real.t) list -> t
end

val of_int : ctx -> int -> t
val create_simple : ctx -> Libpoly.Integer.t -> Var.t -> int -> t
val to_string : t -> string
val string_of_polynomial_list : t list -> string
val pp : Format.formatter -> t -> unit
val create : ctx -> t
val resultant : ctx -> t -> t -> t
val gcd : ctx -> t -> t -> t
val sgn : ctx -> t -> Assignment.t -> int
val evaluate : ctx -> t -> Assignment.t -> Real.t
val zero : ctx -> t
val add : ctx -> t -> t -> t
val sub : ctx -> t -> t -> t
val neg : ctx -> t -> t
val mul : ctx -> t -> t -> t
val div : ctx -> t -> t -> t
val roots_isolate : ctx -> t -> Assignment.t -> Real.t array
val reductum : ctx -> t -> t
val derivative : ctx -> t -> t
val primitive : ctx -> t -> t
val disc : ctx -> t -> t
val equal : t -> t -> bool
val is_constant : t -> bool
val is_zero : t -> bool
val top_variable : t -> Var.t
val degree : t -> int
val get_coefficient : ctx -> t -> int -> t
val mult_list_polynomes : ctx -> int -> t list -> t
val mk_assignment : Var.t list -> int list -> Assignment.t
val mk_monomes : ctx -> Var.t list -> int * int list -> t
val mk_polynomes : ctx -> Var.t list -> (int * int list) list -> t

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

val required_coefficient : ctx -> Assignment.t -> t -> Set.t
val required_coefficients : ctx -> Assignment.t -> Set.t -> Set.t
val to_list : Set.t -> t list
val of_list : t list -> Set.t
