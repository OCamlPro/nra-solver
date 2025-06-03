type sigma = Equal | Less
type contraint = (Polynomes.t) * sigma

let rec mult (l : Real.t list) : Real.t =
  match l with
  | [] -> Real.of_int 1
  | x :: l ->
      Format.printf "%a@." Real.pp x;
      Real.mul (mult l) x

let array_filtrer (arr : contraint array) ( s : Polynomes.Assignment.t )(f : contraint -> Polynomes.Assignment.t -> bool) : contraint array =
  let n = Array.length arr in
  let j = ref 0 in
  for i = 0 to n - 1 do
    if f arr.(i) s then (
      arr.(!j) <- arr.(i);
      incr j)
  done;
  Array.sub arr 0 !j

let sorts_array (arr : Real.t array) : Real.t array =
  let copie = Array.copy arr in
  Array.sort Real.compare copie;
  copie


  let pp_constraint ppf (p, s) =
    Format.fprintf ppf "(" ;
    Polynomes.pp ppf p;  
   match s with
    | Equal -> Format.fprintf ppf " = 0)"
    | Less  -> Format.fprintf ppf " < 0)"

  let pp_array_of_constraints ppf (constraints : contraint array) =
  let len = Array.length constraints in
  if len = 0 then
    Format.fprintf ppf "[]" (* Or just "" if you prefer empty output for empty array *)
  else begin
    Format.fprintf ppf "@[<v>"; (* Open a vertical box for nice formatting *)
    Array.iteri (fun i c ->
      pp_constraint ppf c;
      if i < len - 1 then
        Format.fprintf ppf "@\n" (* Print a newline for all but the last *)
    ) constraints;
    Format.fprintf ppf "@]" (* Close the vertical box *)
  end

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#********** Algorithme 3 **************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
 let list_coefficients ( c : contraint ) : Polynomes.t list = 
 let (p , _) = c in 
 let d = Polynomes.degree p in 
 let rec loop i acc = 
  if i >= d then acc else
    loop (i + 1) ((Polynomes.get_coefficient p i) :: acc) in
    loop 0 []  


 let is_poly_nul ( c : contraint) ( s : Polynomes.Assignment.t ) = 
  let coeff_list = list_coefficients c in 
  let  zero_poly = Polynomes.create() in 
  let b = 
  List.exists ( fun p -> Polynomes.eq p zero_poly <> 1  ) coeff_list in 
  match b with 
   |true -> false 
   |false -> true 


  let is_poly_constant  ( c : contraint) ( s : Polynomes.Assignment.t ) = 
  let coeff_list = list_coefficients c in 
  let  zero_poly = Polynomes.create() in 
  let liste_sans_premier_elem = List.tl coeff_list in 
  let b = 
    List.exists ( fun p -> Polynomes.eq p zero_poly <> 1  ) liste_sans_premier_elem in 
    match b with 
     |true -> false 
     |false -> true

  
  



let evaluate_contraint (c : contraint) (s : Polynomes.Assignment.t)  ( v : Real.t ) =
  

  let (arr_p, s') = c in
  if  is_poly_nul c s then 
    match s' with 
    |Equal -> true 
    |Less -> false 
else 

  let x = Polynomes.top_variable arr_p in 
  let new_s = Polynomes.Assignment.add x v s in 
  match s' with
    | Equal ->
        let n = Polynomes.sgn arr_p new_s in 
        if n = 0 then true
        else false
    | Less ->
      let n = Polynomes.sgn arr_p new_s in 
      if n < 0 then true
      else false

let val_pick (i : Covering.interval) : Real.t =
  match i with Covering.Open (l, u) -> Covering.sample_interval l u | Exact a -> a

exception Break of Covering.interval list

let rec list_intervals c s (l : Covering.interval list) acc =

  match l with
  | [] -> acc
  | a :: l' ->
      let r = val_pick a in
      if evaluate_contraint c s  r then list_intervals c s l'  acc
      else list_intervals c s l'  (a :: acc)

let get_unsat_intervals (c : contraint array) (s : Polynomes.Assignment.t ) : Covering.interval list =
  let n = Array.length c in  
  let rec loop i acc = 
    if i < 0 then acc 
    else (if (is_poly_nul c.(i) s  ) then ( if (evaluate_contraint c.(i) s (Real.of_int 0)) then (loop (i - 1) acc) else  [Covering.Open ( Covering.Ninf , Covering.Pinf )]) 
  else 
    let ( p , _) = c.(i) in 
    let roots = Polynomes.roots_isolate p s in
    let regions = Covering.pointsToIntervals roots in 
    let acc = list_intervals c.(i) s regions  acc in
    loop (i - 1) acc) in 
  loop (n-1) [] 

let u = Polynomes.Var.create "u"
let v = Polynomes.Var.create "v"
let w = Polynomes.Var.create "w"
let s = Polynomes.mk_assignment [u ; v] [0 ; (-1)]
let v_list = [u ; v ; w]


let p1_test = Polynomes.mk_polynomes v_list [(1 , [1; 0; 4]) ; (1 , [0; 1; 0]) ]
let p2_test = Polynomes.mk_polynomes v_list [(1 , [0; 0; 1]) ; (1 , [0; 0; 0])  ]

let c1_test = (p1_test , Less)
let c2_test = (p2_test , Less)

let res_test = get_unsat_intervals [|c1_test ; c2_test|] s

let x = Polynomes.Var.create "x"
let y = Polynomes.Var.create "y"
let z = Polynomes.Var.create "z"

let variables = [x ; y]  
let p1 = Polynomes.mk_polynomes variables [(-1 , [2 ; 0]) ; ( 4 , [0 ; 0]) ; (4 , [0 ; 1])]
let p2 = Polynomes.mk_polynomes variables [(-1, [2 ; 0]) ; ( 3 , [0 ; 0]) ; ( 2 , [1 ; 0]) ; (-4 , [0 ; 1])]
let p3 = Polynomes.mk_polynomes variables [(1 , [1 ; 0]) ; ( 2 , [0 ; 0]) ; (-4 , [0 ; 1])]
  
let c1 = ( p1 ,  Less)
let c2 = ( p2 ,  Less)
let c3 = ( p3 ,  Less)
let s = Polynomes.Assignment.of_list [( x , Real.of_int 0)]

let result = get_unsat_intervals [|c1 ; c2 ; c3|] s 


  
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
