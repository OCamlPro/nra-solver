include Libpoly.Value

let pp ppf (x : t) = Format.fprintf ppf "%s" (to_string x)

let pp_array_of_real ppf (real_array : t array) =
  let len = Array.length real_array in
  if len = 0 then
    Format.fprintf ppf
      "[]" (* Or just "" if you prefer empty output for empty array *)
  else (
    Format.fprintf ppf "@[<v>";
    (* Open a vertical box for nice formatting *)
    Array.iteri
      (fun i v ->
        pp ppf v;
        if i < len - 1 then
          Format.fprintf ppf "@\n" (* Print a newline for all but the last *))
      real_array;
    Format.fprintf ppf "@]" (* Close the vertical box *))

module Var = Libpoly.Variable
module Integer = Libpoly.Integer
module Rational = Libpoly.Rational
module Dyadic_rational = Libpoly.Dyadic_rational
module Ring = Libpoly.Ring
module AlgebraicNumber = Libpoly.AlgebraicNumber

(* --- Define global context components --- *)
let var_db = Var.Db.create ()
let var_order = Var.Order.create ()

(* Define the polynomial context using the created db and order *)
let poly_ctx =
  Libpoly.Polynomial.Context.create
    ~ring:Ring.lp_Z (* Use the default integer ring *)
    var_db var_order
(* ---------------------------------------- *)

type real = t

let view = view
let sgn = sgn
let of_int = of_int
let of_z = of_z
let of_q = of_q
let inv = inv
let to_string = to_string
let is_integer = is_integer
let is_rational = is_rational
let to_rational_opt = to_rational_opt
let of_rational = of_rational
let pow = pow
let neg = neg
let to_q_opt = to_q_opt
let add = add
let mul = mul
let sub = sub
let div = div
let compare = compare
let max x y = if compare x y < 0 then y else x
let min x y = if compare x y < 0 then x else y

module Syntax = struct
  let ( + ) = add
  let ( - ) = sub
  let ( * ) = mul
  let ( / ) = div
  let ( ~$ ) = of_int
  let ( < ) x y = compare x y < 0
  let ( <= ) x y = compare x y <= 0
  let ( > ) x y = compare x y > 0
  let ( >= ) x y = compare x y >= 0
  let ( = ) x y = compare x y = 0
end
