type t = {
  poly_ctx : Libpoly.Polynomial.Context.t;
  var_db : Libpoly.Variable.Db.t;
  var_order : Libpoly.Variable.Order.t;
  constraints : Constraint.contraint Queue.t;
  tbl : (int, Libpoly.Variable.t) Hashtbl.t;
}

type variable = Libpoly.Variable.t
type term = unit

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
    constraints = Queue.create ();
    tbl = Hashtbl.create 17
  }

(* Associate an unique identifier to each variable because we could create
   multiple variables with the same name. *)
  
let create_variable t = 
  let cnt = ref 0 in
  fun name ->
    let var = Libpoly.Variable.Db.new_variable t.var_db name in
    incr cnt;
    Format.printf "thamtoth: %d -> %s@." !cnt (Libpoly.Variable.Db.get_name t.var_db var);
    Hashtbl.add t.tbl !cnt var;
    var

module Term = struct
  let variable _ = ()
  let real _ = ()
  let minus _ = ()
  let add _ _ = ()
  let sub _ _ = ()
  let mul _ _ = ()
  let div _ _ = ()
end

let assert_eq t p q = 
  let r = Term.(sub p q) in
  ()
let assert_neq _ _ _ = ()
let assert_lt _ _ _ = ()
let assert_leq _ _ _ = ()
let assert_gt _ _ _ = ()
let assert_geq _ _ _ = ()

type solve_result = Sat | Unsat | Unknown

let solve _ = Unknown

module Covering = Covering
module Real = Real
module Constraint = Constraint
module Z_poly = Z_poly
module Polynomes = Polynomes
