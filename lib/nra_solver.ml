type t = unit
type variable = { id : int; name : string }
type term = unit

let create () = ()

(* Associate an unique identifier to each variable because we could create
   multiple variables with the same name. *)

let fresh =
  let cnt = ref 0 in
  fun () ->
    incr cnt;
    !cnt

let create_variable () name = { id = fresh (); name }

module Term = struct
  let variable _ = ()
  let real _ = ()
  let minus _ = ()
  let add _ _ = ()
  let sub _ _ = ()
  let mul _ _ = ()
  let div _ _ = ()
end

let assert_eq _ _ _ = ()
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
