module P = Libpoly.Polynomial

type t = Libpoly.Polynomial.t

type ctx = {
  poly_ctx : Libpoly.Polynomial.Context.t;
  var_db : Libpoly.Variable.Db.t;
  var_order : Libpoly.Variable.Order.t;
}

(* ---------------------------------------- *)

let create_context () =
  let var_db = Libpoly.Variable.Db.create () in
  let var_order = Libpoly.Variable.Order.create () in
  (* Define the polynomial context using the created db and order *)
  let poly_ctx =
    Libpoly.Polynomial.Context.create
      ~ring:Libpoly.Ring.lp_Z (* Use the default integer ring *)
      var_db var_order
  in
  { poly_ctx; var_db; var_order }

module Var = struct
  type t = Libpoly.Variable.t

  let pp ctx ppf v =
    let s = Libpoly.Variable.Db.get_name ctx.var_db v in
    Fmt.pf ppf "%s" s

  let create ctx name = Libpoly.Variable.Db.new_variable ctx.var_db name
  let compare ctx = Libpoly.Variable.Order.compare_variables ctx.var_order
end

let of_int ctx i =
  let m =
    Libpoly.Polynomial.Monomial.create ~ctx:ctx.poly_ctx
      (Libpoly.Integer.of_z (Z.of_int i))
      []
  in
  Libpoly.Polynomial.of_list ~ctx:ctx.poly_ctx [ m ]

   

let one ctx = of_int ctx 1
let zero ctx = of_int ctx 0

module Assignment = struct
  type t = (Libpoly.Variable.t * Real.t) list

  let of_list l = l
  let to_list l = l

  let to_libpoly_assignment ctx (t : t) : Libpoly.Assignment.t =
    let r = Libpoly.Assignment.create ctx.var_db in
    List.iter (fun (x, v) -> Libpoly.Assignment.add r x v) t;
    r

  let empty = []
  let add x v l = (x, v) :: l

  let pp_assignment ctx ppf (assign : t) : unit =
    let libpoly_assign = to_libpoly_assignment ctx assign in

    let s = Libpoly.Assignment.to_string libpoly_assign in

    Format.fprintf ppf "%s" s
end

let equal = P.Context.equal

let create_monomial ctx coeff vars =
  P.Monomial.create ~ctx:ctx.poly_ctx coeff vars

let evaluate ctx t a = P.evaluate t @@ Assignment.to_libpoly_assignment ctx a
let sgn ctx t a = P.sgn t @@ Assignment.to_libpoly_assignment ctx a

let resultant ctx p q =
  (*let str1 = P.to_string p in
  Format.printf " premier poly pour calcule de resultant :%s  @." str1;
  let str2 = P.to_string q in
  Format.printf "dexieme poly pour calcule de resultant : %s   @." str2;*)
  P.resultant ~ctx:ctx.poly_ctx p q

let gcd ctx p1 p2 = P.gcd ~ctx:ctx.poly_ctx p1 p2
let of_list ctx monomials = P.of_list ~ctx:ctx.poly_ctx monomials
let fold = P.fold
let create_simple ctx = P.create_simple ~ctx:ctx.poly_ctx

let create ctx =
  P.create ~ctx:ctx.poly_ctx (* No argument needed now for zero poly *)

let zero ctx = create ctx
let app1 f ctx = f ~ctx:ctx.poly_ctx

(*j'ai enlevé le ctx*)
let add = app1 P.add
let mul = app1 P.mul
let sub = app1 P.sub
let div = app1 P.div
let neg = app1 P.neg
let reductum = app1 P.reductum
let derivative = app1 P.derivative
let primitive = app1 P.pp

(* FIXME *)
(*j'ai enlevé le ctx*)
let degree = P.degree
let is_constant p = P.is_constant p = 1
let is_zero p = P.is_zero p = 1

let disc ctx p =
  if degree p = 1 then of_int ctx 1 else resultant ctx p (derivative ctx p)

let top_variable = P.top_variable
let equal p q = P.eq p q = 1
let get_coefficient ctx = P.get_coefficient ~ctx:ctx.poly_ctx

let roots_isolate ctx p assignment =
  P.roots_isolate p @@ Assignment.to_libpoly_assignment ctx assignment

let to_string = P.to_string
let pp ppf (p : t) = Format.fprintf ppf "%s" (to_string p)

let string_of_polynomial_list (polys : t list) : string =
  let poly_strings = List.map to_string polys in
  "[" ^ String.concat "; " poly_strings ^ "]"

let mk_assignment (variables : Var.t list) (l : int list) : Assignment.t =
  let l =
    List.fold_left2 (fun acc v n -> (v, Real.of_int n) :: acc) [] variables l
  in
  Assignment.of_list l

let rec mult_list_polynomes ctx (n : int) (l : t list) : t =
  match l with
  | [] -> of_int ctx n
  | p :: l -> mul ctx p (mult_list_polynomes ctx n l)

let mk_monomes ctx (variables : Var.t list) ((coeff, degres) : int * int list) =
  let l =
    List.fold_left2
      (fun acc v d ->
        if d = 0 then acc
        else create_simple ctx (Libpoly.Integer.of_z (Z.of_int 1)) v d :: acc)
      [] variables degres
  in

  mult_list_polynomes ctx coeff l

(*
let degres_array = Array.of_list degres in
let n = List.length degres in 
  let rec loop i acc =
  if i >= n then acc else 
    if (degres_array.(i) = 0) then (loop (i + 1) acc)  
    
    else loop (i + 1) 
              ((create_simple (Libpoly.Integer.of_z (Z.of_int 1))    (create_variable (i + 1)) degres_array.(i)) :: acc )
  in let l = loop 0 [] in 
  mult_list_polynomes coeff l*)

module Set = struct
  include Set.Make (struct
    type nonrec t = t

    let compare = P.compare
  end)

  let singleton p =
    (*assert (eq p zero_poly <> 1);*)
    singleton p

  let add p s =
    (*assert (eq p zero_poly <> 1);*)
    add p s
end

module Map = Map.Make (struct
  type nonrec t = t

  let compare = P.compare
end)

let to_list t = List.of_seq @@ Set.to_seq t
let of_list l = Set.of_seq @@ List.to_seq l

let rec mk_polynomes ctx (variables : Var.t list) (l : (int * int list) list) :
    t =
  match l with
  | [] -> zero ctx
  | m :: l ->
      add ctx (mk_monomes ctx variables m) (mk_polynomes ctx variables l)

exception Break of Set.t

(*****************************************************    Algo 6 *******************************************************************************************************)
let required_coefficient ctx (s : Assignment.t) (p : t) =
  let result = ref Set.empty in
  let q = ref p in

  try
    while not @@ equal !q (zero ctx) do
      let m = degree !q in
      (*Format.printf " %d le degré de yz + 1 @. " m ; *)
      let lc = get_coefficient ctx !q m in
      (*Format.printf " %s le coeff dom de  yz + 1 @. " (to_string lc )  ;*)
      result := Set.add lc !result;
      if sgn ctx lc s <> 0 then raise (Break !result) else q := reductum ctx !q
    done;
    !result
  with Break l -> l

let required_coefficients ctx (s : Assignment.t) (p : Set.t) : Set.t =
  Set.fold
    (fun elt acc -> Set.union (required_coefficient ctx s elt) acc)
    p Set.empty

(**************************************************************************************************************************************************************************)
