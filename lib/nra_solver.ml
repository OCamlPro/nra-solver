type sigma = Equal | Less
type contraint = Libpoly.Polynomial.t * sigma

type t = {
  poly_ctx : Libpoly.Polynomial.Context.t;
  var_db : Libpoly.Variable.Db.t;
  var_order : Libpoly.Variable.Order.t;
  mutable constraints : contraint list;
  tbl : (int, Libpoly.Variable.t) Hashtbl.t;
}

type term = Libpoly.Polynomial.t
type variable = Libpoly.Variable.t

let create () =
  let var_db = Libpoly.Variable.Db.create () in
  let var_order = Libpoly.Variable.Order.create () in
  {
    var_db;
    var_order;
    poly_ctx =
      Libpoly.Polynomial.Context.create
        ~ring:Libpoly.Ring.lp_Z (* Use the default integer ring *)
        var_db var_order;
    constraints = [];
    tbl = Hashtbl.create 17;
  }

(* Associate an unique identifier to each variable because we could create
   multiple variables with the same name. *)

let create_variable t =
  let cnt = ref 0 in
  fun name ->
    let var = Libpoly.Variable.Db.new_variable t.var_db name in
    incr cnt;
    Format.printf "thamtoth: %d -> %s@." !cnt
      (Libpoly.Variable.Db.get_name t.var_db var);
    Hashtbl.add t.tbl !cnt var;
    var

let zero_poly t = Libpoly.Polynomial.create ~ctx:t.poly_ctx

let create_simple t coeff var exponent =
  Libpoly.Polynomial.create_simple ~ctx:t.poly_ctx coeff var exponent

module Term = struct
  let variable t v = create_simple t (Libpoly.Integer.of_z (Z.of_int 1)) v 1
  let real t s = variable t (create_variable t s)
  let add t p q = Libpoly.Polynomial.add ~ctx:t.poly_ctx p q
  let sub t p q = Libpoly.Polynomial.sub ~ctx:t.poly_ctx p q
  let mul t p q = Libpoly.Polynomial.mul ~ctx:t.poly_ctx p q
  let minus t p = sub t (zero_poly t) p
  let div t p q = Libpoly.Polynomial.div ~ctx:t.poly_ctx p q
end

let assert_eq t p q =
  let r = Term.(sub t p q) in
  t.constraints <- (r, Equal) :: t.constraints

let assert_neq t p q = let r = Term.(sub t p q) in (* p <> q    <-> -(p-q)^2 < 0 *)
let r' =  Term.mul t r r    in 
 let r'' = Term.minus t r'  in 
t.constraints <- (r'', Less) :: t.constraints

let assert_lt t p q = let r = Term.(sub t p q) in
t.constraints <- (r, Less) :: t.constraints

let assert_leq t p q = let r = Term.(sub t q p) in (* p <= q <->  q - p >= 0 <-> il existe x tq  q - p = x^2*)
 let r' = Term.variable t (create_variable t "x") in 
  let r'' = Term.add t r' r in 
t.constraints <- (r'', Equal) :: t.constraints


let assert_gt t p q = let r = Term.(sub t q p) in
t.constraints <- (r, Less) :: t.constraints


let assert_geq t p q = let r = Term.(sub t p q) in (* p >= q <->  p - q >= 0 <-> il existe x tq  p - q = x^2*)
let r' = Term.variable t (create_variable t "x") in 
 let r'' = Term.add t r' r in 
t.constraints <- (r'', Equal) :: t.constraints

type solve_result = Sat | Unsat | Unknown

let solve _ = Unknown

module Covering = Covering
module Real = Real
module Constraint = Constraint
module Z_poly = Z_poly
module Polynomes = Polynomes
