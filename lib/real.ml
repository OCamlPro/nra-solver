module CA = Flint.CA

type t = CA.t

let ctx = CA.CTX.mk ()
let pp = CA.pp ~ctx
let floor = CA.floor ~ctx
let ceil = CA.ceil ~ctx
let of_int = CA.of_int ~ctx
let neg = CA.neg ~ctx
let add = CA.add ~ctx
let sub = CA.sub ~ctx
let sqrt = CA.sqrt ~ctx
let div = CA.div ~ctx
let compare = CA.compare ~ctx
let ( - ) = sub
