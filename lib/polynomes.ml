module Poly = Flint.FMPZ_poly

type t = Poly.t

let num_real_roots = Poly.num_real_roots
let num_real_roots_sturm = Poly.num_real_roots_sturm
let gcd = Poly.gcd
let is_squarefree = Poly.is_squarefree
