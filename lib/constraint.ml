module Index = struct
  type t = int array

  exception Break of int

  let compare (l1 : t) (l2 : t) : int =
    let n = Array.length l1 in
    let m = Array.length l2 in
    let c = Int.compare n m in
    if c <> 0 then c
    else
      try
        for i = 0 to n - 1 do
          let c = Int.compare l1.(i) l2.(i) in
          if c <> 0 then raise (Break c)
        done;
        0
      with Break c -> c
end

let rec mult (l : Real.t list) : Real.t =
  match l with
  | [] -> Real.of_int 1
  | x :: l ->
      Format.printf "%a@." Real.pp x;
      Real.mul (mult l) x

module Z_poly = struct
  module M = Map.Make (Index)

  type t = Z.t M.t

  (** 17x^2 y + 3y + 5 *)
  let _ : t =
    M.of_list
      [
        ([| 0; 1 |], Z.of_int 3);
        ([| 2; 1 |], Z.of_int 17);
        ([| 0; 0 |], Z.of_int 5);
      ]

  let evaluate_monome (degres : Index.t) (coef : Z.t) (valeurs : Real.t array) :
      Real.t =
    if Array.length degres <> Array.length valeurs then
      failwith
        "La longueur de la liste des degrés doit être égale à la longueur de \
         la list de valeurs "
    else
      let n = Array.length degres in
      let coeff = Real.of_z coef in
      let l = ref [ coeff ] in
      for i = 0 to n - 1 do
        let x = Real.pow valeurs.(i) (Q.of_int degres.(i)) in
        l := x :: !l
      done;
      let new_coeff = mult !l in
      new_coeff

  let evaluate_polynome (p : t) (l : Real.t array) : Real.t =
    M.fold
      (fun (i : Index.t) (c : Z.t) acc -> Real.add acc (evaluate_monome i c l))
      p (Real.of_int 0)

  let pp _ = assert false
end

type sigma = Egal | Less
type polyn = Z_poly.t array
type contraint = polyn * sigma

let is_poly_nul (c : contraint) (s : Real.t array) : bool =
  let p, _ = c in
  let arr = Array.map (fun poly -> Z_poly.evaluate_polynome poly s) p in
  Array.for_all (fun x -> Real.compare x (Real.of_int 0) = 0) arr


let specialize_poly (c : contraint) (s : Real.t array) : Real.Poly.t =
  let p, _ = c in
  let arr = Array.map (fun poly -> Z_poly.evaluate_polynome poly s) p in
  Real.Poly.create arr

let array_filtrer (arr : Real.t array) (f : Real.t -> bool) : Real.t array =
  let n = Array.length arr in
  let j = ref 0 in
  for i = 0 to n - 1 do
    if f arr.(i) then (
      arr.(!j) <- arr.(i);
      incr j)
  done;
  Array.sub arr 0 !j
let sorts_array (arr : Real.t array) : Real.t array =
  let copie = Array.copy arr in
  Array.sort Real.compare copie;
  copie

let real_roots (p : Real.Poly.t) : Real.t array =
  let l = Real.Poly.roots p in
  let l' = array_filtrer l Real.is_real in 
  sorts_array l'
  

let num_roots (p : Real.Poly.t) : int = Array.length (real_roots p)

let evaluate_contraint ((arr_p, s') : contraint) (s : Real.t array) (r : Real.t) =
  let c = (arr_p, s') in
  if (is_poly_nul c s) then 
    match s' with 
    |Egal -> true 
    |Less -> false 
else 
  match s' with
  | Egal ->
      let p = specialize_poly c s in
      if Real.compare (Real.Poly.evaluate p r) (Real.of_int 0) = 0 then true
      else false
  | Less ->
      let p = specialize_poly c s in
      if Real.compare (Real.Poly.evaluate p r) (Real.of_int 0) < 0 then true
      else false

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#********** Algorithme 3 **************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)

let val_pick (i : Covering.interval) : Real.t =
  match i with Open (l, u) -> Covering.sample_interval l u | Exact a -> a

exception Break of Covering.interval list

let rec list_intervals c s (l : Covering.interval list)
    (acc : Covering.interval list) =
  match l with
  | [] -> acc
  | a :: l' ->
      let r = val_pick a in
      if evaluate_contraint c s r then list_intervals c s l' acc
      else list_intervals c s l' (a :: acc)

let get_unsat_intervals (c : contraint array) (s : Real.t array) :
    Covering.interval list =
  let n = Array.length c in
  let rec loop i acc =
    if i < 0 then acc
    else
    if (is_poly_nul c.(i) s) then 
      (let b = evaluate_contraint c.(i) s (Real.of_int 1) in
      if not b then [ Covering.Open (Covering.Ninf, Covering.Pinf) ]
      else loop (i - 1) acc)
    else 
      let p = specialize_poly c.(i) s in
      let roots = real_roots p in
      if (Array.length roots = 0)  then
        let b = evaluate_contraint c.(i) s (Real.of_int 1) in
        if not b then [ Covering.Open (Covering.Ninf, Covering.Pinf) ]
        else loop (i - 1) acc
      else
        let regions = Covering.pointsToIntervals roots in
        let acc = list_intervals c.(i) s regions acc in
        loop (i - 1) acc
  in
  loop (n - 1) []

(*let get_unsat_intervals (c : contraint array) (s : Real.t array) :
    Covering.interval list =
  let intervals = ref [] in
  let n = Array.length c in
  try
    for i = 0 to n - 1 do
      let p = morph_poly c.(i) s in
      let roots = real_roots p in
      if Array.length roots = 0 then (
        let b = evaluate_contraint c.(i) s (Real.of_int 1) in
        if not b then
          raise (Break [ Covering.Open (Covering.Ninf, Covering.Pinf) ]))
      else
        let regions = Covering.pointsToIntervals roots in
        intervals := list_intervals c.(i) s regions !intervals
    done;
    !intervals
  with Break l -> l*)


  let mk_poly (specs : (int * int) list) : Z_poly.t =
    Z_poly.M.of_list (List.map (fun (d, c) -> ([| d |], Z.of_int c)) specs)
  
  let mk_constraint (poly_specs : (int * int) list array) (sigma : sigma) : contraint =
    (Array.map mk_poly poly_specs, sigma)
  
  let c4 = mk_constraint [| [(2, 1); (0, 4)]; [(0, 4)] |] Less
  let c2 = mk_constraint [| [(2, -1); (1, 2); (0, 3)]; [(0, -4)] |] Less
  let c3 = mk_constraint [| [(1, 1); (0, 2)]; [(0, -4)] |] Less
  
  let c_array = [| c1 ; c2 ; c3 |]
  
let p1c1 : Z_poly.t =
  Z_poly.M.of_list [ ([| 2 |], Z.of_int 1); ([| 0 |], Z.of_int (-4)) ]

let p2c1 : Z_poly.t = Z_poly.M.of_list [ ([| 0 |], Z.of_int 4) ]

let p1c2 : Z_poly.t =
  Z_poly.M.of_list
    [ ([| 2 |], Z.of_int (-1)); ([| 1 |], Z.of_int 2); ([| 0 |], Z.of_int 3) ]

let p2c2 : Z_poly.t = Z_poly.M.of_list [ ([| 0 |], Z.of_int (-4)) ]

let p1c3 : Z_poly.t =
  Z_poly.M.of_list [ ([| 1 |], Z.of_int 1); ([| 0 |], Z.of_int (2)) ]

let p2c3 : Z_poly.t = Z_poly.M.of_list [ ([| 0 |], Z.of_int (-4)) ]

let c1 = ([| p1c1 ; p2c1|], Less) 
let c2 = ([| p1c2 ; p2c2|], Less)
let c3 = ([| p1c3 ; p2c3|], Less)


let c_array = [| c1 ; c2 ; c3|] 

let result = get_unsat_intervals c_array [|Real.of_int 0|]



(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)

type degres =
  int list (* Une liste d'entiers représentant les degrés de chaque variable *)

type monome_multi_variable = Real.t * degres
type polynome_multi_variable = monome_multi_variable list

let (example : polynome_multi_variable) =
  [
    (Real.Syntax.(~$2), [ 2; 0; 0 ]);
    (* 2x^2  + y + 7y + 6*)
    (Real.Syntax.(~$1), [ 0; 1; 0 ]);
    (Real.Syntax.(~$7), [ 0; 0; 7 ]);
    (Real.Syntax.(~$6), [ 0; 0; 0 ]);
  ]

type comparaison = Inferieur | Egal
type constraints = polynome_multi_variable * comparaison

let (exemple : constraints) =
  ( [
      (Real.Syntax.(~$2), [ 2; 0; 0 ]);
      (Real.Syntax.(~$1), [ 0; 1; 0 ]);
      (Real.Syntax.(~$7), [ 0; 0; 7 ]);
      (Real.Syntax.(~$6), [ 0; 0; 0 ]);
    ],
    Inferieur )
(* 2x^2  + y + 7y + 6 < 0*)

type set_const = constraints list

let rec mult (l : Real.t list) : Real.t =
  match l with
  | [] -> Real.of_int 1
  | x :: l ->
      Format.printf "%a@." Real.pp x;
      Real.mul (mult l) x

let rec addition (l : Real.t option list) : Real.t =
  match l with
  | [] -> Real.of_int 0
  | x :: l -> (
      match x with
      | Some x_val -> Real.add (addition l) x_val
      | None -> Real.add (addition l) (Real.of_int 0))

let substituer_monome ((coeff, degres) : monome_multi_variable)
    (valeurs : Real.t list) : monome_multi_variable option =
  if List.length degres <> List.length valeurs + 1 then
    failwith
      "La longueur de la liste des degrés doit être égale à la longueur de \n\
      \    la liste des valeurs de substitution + 1. car je veux remplacer \
       toutes les variables sauf la derniere"
  else
    let list_degree = Array.of_list degres in
    let n = List.length degres in
    let list_valeur = Array.of_list valeurs in
    let l = ref [ coeff ] in
    for i = 0 to n - 2 do
      let x = Real.pow list_valeur.(i) (Q.of_int list_degree.(i)) in
      Format.printf "%a@." Real.pp x;
      l := x :: !l
    done;
    let new_coeff = mult !l in
    Format.printf "%a@." Real.pp new_coeff;

    let nouveau_degres =
      let rec construire_nouveaux_degres m =
        if m > 0 then
          0 :: construire_nouveaux_degres (m - 1)
        else [ List.nth degres (List.length degres - 1) ]
      in
      construire_nouveaux_degres (List.length degres - 1) (* reccursion a l'envers if length *)
    in
    if Real.compare new_coeff (Real.of_int 0) = 0 then None
      (* Le monôme s'annule après substitution *)
    else Some (new_coeff, nouveau_degres)

let substituer_polynome (poly : polynome_multi_variable)
    (variables : Real.t list) : polynome_multi_variable =
  let substituted_monomes =
    List.map (fun monome -> substituer_monome monome variables) poly
  in
  List.filter_map (fun x -> x) substituted_monomes

let pp_monome ppf ((coeff, degres) : monome_multi_variable) =
  let pp_degre ppf (degre, indice) =
    if degre = 1 then Format.fprintf ppf "v%d" (indice + 1)
    else if degre > 0 then Format.fprintf ppf "v%d^%d" (indice + 1) degre
  in
  Format.fprintf ppf "%a" Real.pp coeff;
  List.iteri
    (fun i degre ->
      if degre > 0 then Format.fprintf ppf " %a" pp_degre (degre, i))
    degres

let pp_poly ppf (p : polynome_multi_variable) =
  let pp_sep ppf () = Format.fprintf ppf "+" in
  Format.pp_print_list ~pp_sep pp_monome ppf p

let show_poly = Fmt.to_to_string pp_poly

let tri_monomes (p : polynome_multi_variable) : polynome_multi_variable =
  List.sort
    (fun (_, d1) (_, d2) ->
      compare (List.hd (List.rev d1)) (List.hd (List.rev d2)))
    p

let combiner_monomes_meme_degre_final (p : polynome_multi_variable) :
    polynome_multi_variable =
  let groupes = Hashtbl.create 10 in
  List.iter
    (fun (coeff, degres) ->
      match List.rev degres with
      | dernier_degre :: _ ->
          let somme_actuelle =
            match Hashtbl.find_opt groupes dernier_degre with
            | Some s -> s
            | None -> Real.of_int 0
          in
          Hashtbl.replace groupes dernier_degre (Real.add somme_actuelle coeff)
      | [] ->
          Format.eprintf "Attention : Monôme avec une liste de degrés vide.@.")
    p;
  Hashtbl.fold (fun degre somme acc -> (somme, [ degre ]) :: acc) groupes []

let (example_combiner : polynome_multi_variable) =
  [
    (Real.Syntax.(~$2), [ 0; 0; 2 ]);
    (Real.Syntax.(~$3), [ 0; 0; 1 ]);
    (Real.Syntax.(~$5), [ 0; 0; 2 ]);
    (Real.Syntax.(~$(-1)), [ 0; 0; 0 ]);
    (Real.Syntax.(~$4), [ 0; 0; 0 ]);
    (Real.Syntax.(~$6), [ 0; 0; 1 ]);
  ]
