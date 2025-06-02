module P = Libpoly.Polynomial 
 
type t = Libpoly.Polynomial.t
exception Break of t list 

(* --- Define global context components --- *)
let var_db = Libpoly.Variable.Db.create ()
let var_order = Libpoly.Variable.Order.create ()

(* Define the polynomial context using the created db and order *)
let poly_ctx =
  Libpoly.Polynomial.Context.create
    ~ring:Libpoly.Ring.lp_Z (* Use the default integer ring *)
    var_db var_order
(* ---------------------------------------- *)



module Var = struct 
  type t = Libpoly.Variable.t
  let create =
     
    Libpoly.Variable.Db.new_variable var_db 
  let compare = Libpoly.Variable.Order.compare_variables var_order
  end 


let one = 
  let m = Libpoly.Polynomial.Monomial.create ~ctx:poly_ctx (Libpoly.Integer.of_z (Z.of_int 1)) [] in
  Libpoly.Polynomial.of_list ~ctx:poly_ctx[ m ]

let zero = 
    let m = Libpoly.Polynomial.Monomial.create ~ctx:poly_ctx (Libpoly.Integer.of_z (Z.of_int 0)) [] in
    Libpoly.Polynomial.of_list ~ctx:poly_ctx[ m ]

module Assignment = struct
  module M = struct
    include Map.Make (struct
    type t = Var.t
   let compare = Var.compare
  end)
    let of_list l = of_seq @@ List.to_seq l
    let to_list t = List.of_seq @@ to_seq t
  end
  type t = Real.t M.t

  let v1 = Var.create "v1"
  let v2 = Var.create "v2"
  let v3 = Var.create "v3"


  let of_list (l : (Var.t * Real.t) list ) = M.of_list l
  let to_list = M.to_list

  
  let assign : t =
  M.of_list [ (v1, Real.of_int 4); (v2, Real.of_int 5); (v3, Real.of_int 6) ]





  let empty_assignment = Libpoly.Assignment.create var_db

  let to_libpoly_assignment (t : t) : Libpoly.Assignment.t =
    let r = Libpoly.Assignment.create var_db in
    M.iter (fun x v -> Libpoly.Assignment.add r x v) t;
    r
    let empty = M.empty
   let add = M.add



   let pp_assignment ppf (assign : t) : unit =
     
    let libpoly_assign = to_libpoly_assignment assign in
     
    let s = Libpoly.Assignment.to_string libpoly_assign in
     
    Format.fprintf ppf "%s" s
end


let create_context = P.Context.create
let equal = P.Context.equal
let create_monomial coeff vars = P.Monomial.create ~ctx:poly_ctx coeff vars
let evaluate t a = P.evaluate t @@ Assignment.to_libpoly_assignment a
let sgn t a = P.sgn t @@ Assignment.to_libpoly_assignment a
let resultant p1 p2 = P.resultant ~ctx:poly_ctx p1 p2
let gcd p1 p2 = P.gcd ~ctx:poly_ctx p1 p2
let of_list monomials = P.of_list ~ctx:poly_ctx monomials
let fold = P.fold

let create_simple coeff var exponent =
  P.create_simple ~ctx:poly_ctx coeff var exponent

let create () =
  P.create ~ctx:poly_ctx (* No argument needed now for zero poly *)

let zero_poly = create () 

let add p1 p2 = P.add ~ctx:poly_ctx p1 p2
let mul p1 p2 = P.mul ~ctx:poly_ctx p1 p2
let sub p1 p2 = P.sub ~ctx:poly_ctx p1 p2
let div p1 p2 = P.div ~ctx:poly_ctx p1 p2
let neg p = P.neg ~ctx:poly_ctx p
let reductum p = P.reductum ~ctx:poly_ctx p 
let top_variable = P.top_variable 
let eq = P.eq 
let degree = P.degree 
let get_coefficient p k = P.get_coefficient ~ctx:poly_ctx p k


 
let roots_isolate p assignment =
  P.roots_isolate p @@ Assignment.to_libpoly_assignment assignment

let to_string = P.to_string

let pp ppf (p : t) =
  Format.fprintf ppf "%s" (to_string p) 



 
  
  

(*****************************************************    Algo 6 *******************************************************************************************************)
let required_coefficient (s: Assignment.t) (p : t ) =
   let result = ref [] in 
   let q = ref p in 
   let zero_poly = create() in 
  try 
   while (eq !q zero_poly <> 0) do 
    let m = degree !q in 
    let lc = get_coefficient !q m in 
    result := lc :: !result; 
    if  ( sgn lc s) <>  0  then 
      raise  (Break !result)
    else q := reductum !q 
  done;
  !result 
with Break l -> l 

let required_coefficients ( s : Assignment.t  ) ( p : t list  ) : t list  =
    let rec loop l acc  = 
      match l  with 
      |[] -> acc 
      |q :: l ->
          loop l (required_coefficient s q ) @ acc   
      in loop p [] 

(**************************************************************************************************************************************************************************)

 

let mk_assignment (variables : Var.t list )( l : int list ) : Assignment.t = 
  let l = 
    List.fold_left2 
               (fun acc v n -> 
               ( (v , Real.of_int n):: acc))
                     []
                     variables 
                     l in 
    Assignment.M.of_list l




let rec mult_list_polynomes ( n : int ) (l : t list) : t = 
  match l with 
  |[]-> one
  |p ::l -> mul p ( mult_list_polynomes n l) 


let   mk_monomes (variables : Var.t list)(( coeff , degres) : int * (int list))  = 
let l = 
List.fold_left2 
           (fun acc v d -> if d = 0 then acc
           else 
           ((create_simple (Libpoly.Integer.of_z (Z.of_int 1)) v d) :: acc))
                 []
                 variables 
                 degres in 


mult_list_polynomes coeff l 


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

 
  

let rec mk_polynomes (variables : Var.t list )( l : (int * (int list)) list  ) : t = 
match l with
 |[] ->  zero
 |m :: l -> add (mk_monomes variables m) (mk_polynomes variables l)
 

 
 
  