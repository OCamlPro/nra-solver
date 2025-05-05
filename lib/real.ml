module CA = Flint.CA

type t = CA.t

let ctx = CA.CTX.mk ()
let pp = CA.pp ~ctx
let show = Fmt.to_to_string pp
let floor = CA.floor ~ctx
let ceil = CA.ceil ~ctx
let of_int = CA.of_int ~ctx
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
