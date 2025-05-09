module CA = Flint.CA

let ctx = CA.CTX.mk ()

module Poly = struct
  module P = Flint.CA_poly

  type t = P.t

  let create = P.create ~ctx
  let evaluate = P.evaluate ~ctx
  let add = P.add ~ctx
  let mul = P.mul ~ctx
  let pp = P.pp ~ctx
  let sub = P.sub ~ctx
  let roots = P.roots ~ctx
  let to_string = P.to_string ~ctx
end

type t = CA.t
type real = t

let pp = CA.pp ~ctx
let is_real = CA.is_real ~ctx
let show = Fmt.to_to_string pp
let floor = CA.floor ~ctx
let ceil = CA.ceil ~ctx
let of_int = CA.of_int ~ctx
let of_z = CA.of_z ~ctx
let pow = CA.pow ~ctx
let to_q = CA.to_q ~ctx
let neg = CA.neg ~ctx
let add = CA.add ~ctx
let mul = CA.mul ~ctx
let sub = CA.sub ~ctx
let sqrt = CA.sqrt ~ctx
let div = CA.div ~ctx
let compare = CA.compare ~ctx
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
