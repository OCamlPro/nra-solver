type sigma = Equal | Less
type contraint = Polynomes.t * sigma

let rec mult (l : Real.t list) : Real.t =
  match l with
  | [] -> Real.of_int 1
  | x :: l ->
      Format.printf "%a@." Real.pp x;
      Real.mul (mult l) x

let array_filtrer (arr : contraint array) (s : Polynomes.Assignment.t)
    (f : contraint -> Polynomes.Assignment.t -> bool) : contraint array =
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
  Format.fprintf ppf "(";
  Polynomes.pp ppf p;
  match s with
  | Equal -> Format.fprintf ppf " = 0)"
  | Less -> Format.fprintf ppf " < 0)"

let pp_array_of_constraints ppf (constraints : contraint array) =
  let len = Array.length constraints in
  if len = 0 then
    Format.fprintf ppf
      "[]" (* Or just "" if you prefer empty output for empty array *)
  else (
    Format.fprintf ppf "@[<v>";
    (* Open a vertical box for nice formatting *)
    Array.iteri
      (fun i c ->
        pp_constraint ppf c;
        if i < len - 1 then
          Format.fprintf ppf "@\n" (* Print a newline for all but the last *))
      constraints;
    Format.fprintf ppf "@]" (* Close the vertical box *))

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#********** Algorithme 3 **************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
let list_coefficients (c : contraint) : Polynomes.t list =
  let p, _ = c in
  let d = Polynomes.degree p in
  let rec loop i acc =
    if i >= d then acc else loop (i + 1) (Polynomes.get_coefficient p i :: acc)
  in
  loop 0 []

let list_coefficients_poly (p : Polynomes.t) : Polynomes.t list =
  let d = Polynomes.degree p in
  let rec loop i acc =
    if i >= d then acc else loop (i + 1) (Polynomes.get_coefficient p i :: acc)
  in
  loop 0 []

let is_poly_nul (c : contraint) (s : Polynomes.Assignment.t) =
  let coeff_list = list_coefficients c in
  let zero_poly = Polynomes.create () in
  let b = List.exists (fun p -> Polynomes.eq p zero_poly <> 1) coeff_list in
  match b with true -> false | false -> true

let is_poly_non_constant (p : Polynomes.t) =
  let coeff_list = list_coefficients_poly p in
  let zero_poly = Polynomes.create () in
  let liste_sans_premier_elem = List.tl coeff_list in
  List.exists (fun p -> Polynomes.eq p zero_poly <> 1) liste_sans_premier_elem

let evaluate_contraint (c : contraint) (s : Polynomes.Assignment.t) (v : Real.t)
    =
  let arr_p, s' = c in
  if is_poly_nul c s then match s' with Equal -> true | Less -> false
  else
    let x = Polynomes.top_variable arr_p in
    let new_s = Polynomes.Assignment.add x v s in
    match s' with
    | Equal ->
        let n = Polynomes.sgn arr_p new_s in
        if n = 0 then true else false
    | Less ->
        let n = Polynomes.sgn arr_p new_s in
        if n < 0 then true else false

let val_pick (i : Covering.interval) : Real.t =
  match i with
  | Covering.Open (l, u) -> Covering.sample_interval l u
  | Exact a -> a

exception Break of Covering.interval list

let rec list_intervals c s (p : Polynomes.t) (l : Covering.interval list) acc =
  match l with
  | [] -> acc
  | a :: l' ->
      let r = val_pick a in
      if evaluate_contraint c s r then list_intervals c s p l' acc
      else list_intervals c s p l' (Covering.interval_to_intervalPoly a p :: acc)

let get_unsat_intervals (c : contraint array) (s : Polynomes.Assignment.t) :
    Covering.intervalPoly list =
  let n = Array.length c in
  let zero_poly = Polynomes.create () in
  let rec loop i acc =
    if i < 0 then acc
    else if is_poly_nul c.(i) s then
      if evaluate_contraint c.(i) s (Real.of_int 0) then loop (i - 1) acc
      else
        [
          Covering.interval_to_intervalPoly
            (Covering.Open (Covering.Ninf, Covering.Pinf))
            zero_poly;
        ]
    else
      let p, _ = c.(i) in
      let roots = Polynomes.roots_isolate p s in
      let regions = Covering.pointsToIntervals roots in
      let acc = list_intervals c.(i) s p regions acc in
      loop (i - 1) acc
  in
  loop (n - 1) []

let u = Polynomes.Var.create "u"
let v = Polynomes.Var.create "v"
let w = Polynomes.Var.create "w"
let s = Polynomes.mk_assignment [ u; v ] [ 0; -1 ]
let v_list = [ u; v; w ]

let p1_test =
  Polynomes.mk_polynomes v_list [ (1, [ 1; 0; 4 ]); (1, [ 0; 1; 0 ]) ]

let p2_test =
  Polynomes.mk_polynomes v_list [ (1, [ 0; 0; 1 ]); (1, [ 0; 0; 0 ]) ]

let c1_test = (p1_test, Less)
let c2_test = (p2_test, Less)
let res_test = get_unsat_intervals [| c1_test; c2_test |] s
let x = Polynomes.Var.create "x"
let y = Polynomes.Var.create "y"
let z = Polynomes.Var.create "z"
let variables = [ x; y ]

let p1 =
  Polynomes.mk_polynomes variables
    [ (-1, [ 2; 0 ]); (4, [ 0; 0 ]); (4, [ 0; 1 ]) ]

let p2 =
  Polynomes.mk_polynomes variables
    [ (-1, [ 2; 0 ]); (3, [ 0; 0 ]); (2, [ 1; 0 ]); (-4, [ 0; 1 ]) ]

let p3 =
  Polynomes.mk_polynomes variables
    [ (1, [ 1; 0 ]); (2, [ 0; 0 ]); (-4, [ 0; 1 ]) ]

let c1 = (Polynomes.mk_polynomes variables
[ (-1, [ 2; 0 ]); (4, [ 0; 0 ]); (4, [ 0; 1 ]) ]
, Less)
let c2 = (Polynomes.mk_polynomes variables
[ (-1, [ 2; 0 ]); (3, [ 0; 0 ]); (2, [ 1; 0 ]); (-4, [ 0; 1 ]) ]

, Less)
let c3 = (Polynomes.mk_polynomes variables
[ (1, [ 1; 0 ]); (2, [ 0; 0 ]); (-4, [ 0; 1 ]) ]

, Less)
let s = Polynomes.Assignment.of_list [ (x, Real.of_int 0) ]
let result = get_unsat_intervals [| c1; c2; c3 |] s

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#******** Algorithm 4 *****************************************************************)

let discriminant_set (p_set : Polynomes.Set.t) : Polynomes.Set.t =
  Polynomes.Set.map Polynomes.disc p_set

let rec union_poly_sets (l : Polynomes.Set.t list) : Polynomes.Set.t =
  match l with
  | [] -> Polynomes.Set.empty
  | x :: l -> Polynomes.Set.union x (union_poly_sets l)

let resultant_lower_prime (l : Covering.bound) (s : Polynomes.Assignment.t)
    (p : Polynomes.t (*of lower bound L*)) (q_set : Polynomes.Set.t) =
  let q_list = Polynomes.to_list q_set in
  let rec loop res acc =
    match res with
    | [] -> acc
    | q :: res ->
        let roots = Polynomes.roots_isolate q s in
        let b =
          List.exists
            (fun a -> Covering.compare_bound (Finite a) l <= 0)
            (Array.to_list roots)
        in
        if b then loop res (Polynomes.Set.add (Polynomes.resultant p q) acc)
        else loop res acc
  in
  loop q_list Polynomes.Set.empty

let resultant_lower (l : Covering.bound) (s : Polynomes.Assignment.t)
    (p_set : Polynomes.Set.t) (q_set : Polynomes.Set.t) =
  let p_list = Polynomes.to_list p_set in
  let rec loop res acc =
    match res with
    | [] -> acc
    | p :: res ->
        loop res (Polynomes.Set.union (resultant_lower_prime l s p q_set) acc)
  in
  loop p_list Polynomes.Set.empty

let resultant_upper_prime (u : Covering.bound) (s : Polynomes.Assignment.t)
    (p : Polynomes.t (*of lower bound U*)) (q_set : Polynomes.Set.t) =
  let q_list = Polynomes.to_list q_set in
  let rec loop res acc =
    match res with
    | [] -> acc
    | q :: res ->
        let roots = Polynomes.roots_isolate q s in
        let b =
          List.exists
            (fun a -> Covering.compare_bound (Finite a) u >= 0)
            (Array.to_list roots)
        in
        if b then loop res (Polynomes.Set.add (Polynomes.resultant p q) acc)
        else loop res acc
  in
  loop q_list Polynomes.Set.empty

let resultant_upper (l : Covering.bound) (s : Polynomes.Assignment.t)
    (p_set : Polynomes.Set.t) (q_set : Polynomes.Set.t) =
  let p_list = Polynomes.to_list p_set in
  let rec loop res acc =
    match res with
    | [] -> acc
    | p :: res ->
        loop res (Polynomes.Set.union (resultant_upper_prime l s p q_set) acc)
  in
  loop p_list Polynomes.Set.empty

let construct_characterization (s : Polynomes.Assignment.t)
    (i_list : Covering.intervalPoly list) : Polynomes.Set.t =
  let good_cover = Covering.compute_cover i_list in
  let rec loop (l : Covering.intervalPoly list) (acc : Polynomes.Set.t) =
    match l with
    | [] -> acc
    | x :: l ->
        loop l
          (union_poly_sets
             [
               discriminant_set x.p_set;
               x.p_orthogonal_set;
               Polynomes.required_coefficients s x.p_set;
               resultant_lower x.l_bound s x.l_set x.p_set;
               resultant_upper x.u_bound s x.u_set x.p_set;
             ])
  in
  let l = loop good_cover Polynomes.Set.empty in
  let l' = Polynomes.Set.map (fun p -> Polynomes.primitive p) l in
  Polynomes.Set.filter is_poly_non_constant l'

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*******************Algorithme 5******************************************)

let list_max (compare_fn : 'a -> 'a -> int) (lst : 'a list) : 'a =
  match lst with
  | [] -> assert false
  | hd :: tl ->
      let max_val =
        List.fold_left
          (fun current_max elem ->
            if compare_fn elem current_max > 0 then elem
              (* If elem is greater than current_max, update *)
            else current_max)
          hd (* Start with the first element as the initial max *)
          tl
      in
      max_val

let list_min (compare_fn : 'a -> 'a -> int) (lst : 'a list) : 'a =
  match lst with
  | [] -> assert false
  | hd :: tl ->
      let min_val =
        List.fold_left
          (fun current_min elem ->
            if compare_fn elem current_min < 0 then elem
              (* If 'elem' is smaller than 'current_min', it's the new minimum *)
            else current_min)
          hd (* Start with the first element as the initial minimum *)
          tl
      in
      min_val

let compute_list_roots (p_set : Polynomes.Set.t) (s : Polynomes.Assignment.t) :
    Real.t list list =
  (* [roots de p1 ; .... ; roots de pn]*)
  let rec loop l acc =
    match l with
    | [] -> acc
    | x :: l ->
        let roots = Polynomes.roots_isolate x s in
        loop l (Array.to_list roots :: acc)
  in
  loop (Polynomes.to_list p_set) []

let compute_map_roots (p_set : Polynomes.Set.t) (s : Polynomes.Assignment.t) :
    Real.t array Polynomes.Map.t =
  Polynomes.Set.fold
    (fun p acc -> Polynomes.Map.add p (Polynomes.roots_isolate p s) acc)
    p_set Polynomes.Map.empty

let compute_l (m : Real.t array Polynomes.Map.t) b =
  Polynomes.Map.fold
    (fun _ roots acc ->
      Array.fold_left
        (fun acc r ->
          if Covering.compare_bound (Finite r) b <= 0 then
            Covering.max_bound (Finite r) acc
          else acc)
        acc roots)
    m Covering.Ninf

let compute_u (m : Real.t array Polynomes.Map.t) b =
  Polynomes.Map.fold
    (fun _ roots acc ->
      Array.fold_left
        (fun acc r ->
          if Covering.compare_bound (Finite r) b >= 0 then
            Covering.min_bound (Finite r) acc
          else acc)
        acc roots)
    m Covering.Pinf

let compute_roots (l : Real.t list list) =
  let rec loop res acc =
    match res with [] -> acc | x :: res -> loop res (x @ acc)
  in
  let l' = loop l [] in
  let l'' = List.map (fun x -> Covering.Finite x) l' in
  [ Covering.Ninf ] @ l'' @ [ Covering.Pinf ]

let set_function (m : Real.t array Polynomes.Map.t) (l : Covering.bound) =
  Polynomes.Map.fold
    (fun p r acc ->
      let b =
        Array.exists
          (fun x -> Covering.compare_bound (Covering.Finite x) l = 0)
          r
      in
      if b then Polynomes.Set.add p acc else acc)
    m Polynomes.Set.empty

let bound_to_real b =
  match b with Covering.Finite a -> a | Pinf | Ninf -> assert false

let interval_from_charachterization (v : Polynomes.Var.t)
    (s : Polynomes.Assignment.t) (si : Real.t) (p_set : Polynomes.Set.t) :
    Covering.intervalPoly =
  let pi = Polynomes.Set.filter (fun x -> Polynomes.top_variable x = v) p_set in
  let p_orthogonal =
    Polynomes.Set.filter
      (fun x -> if Polynomes.Set.mem x pi then false else true)
      p_set
  in
  let roots_list = compute_map_roots p_set s in

  let lower_bound = compute_l roots_list (Finite si) in
  let upper_bound = compute_u roots_list (Finite si) in
  let l_set_result = set_function roots_list lower_bound in
  let u_set_result = set_function roots_list upper_bound in
  if Covering.compare_bound upper_bound lower_bound = 0 then
    Covering.
      {
        interval = Covering.Exact (bound_to_real lower_bound);
        l_bound = lower_bound;
        u_bound = upper_bound;
        u_set = u_set_result;
        l_set = l_set_result;
        p_set = pi;
        p_orthogonal_set = p_orthogonal;
      }
  else
    Covering.
      {
        interval = Covering.Open (lower_bound, upper_bound);
        l_bound = lower_bound;
        u_bound = upper_bound;
        u_set = u_set_result;
        l_set = l_set_result;
        p_set = pi;
        p_orthogonal_set = p_orthogonal;
      }

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************** Algorithme 2 ********************************************)

type res =
  | Sat of (Polynomes.Var.t * Real.t) list
  | Unsat of Covering.intervalPoly list

let get_unsat_cover (c : contraint array) (variables : Polynomes.Var.t array) (n : int) : res =
  let rec loop (s : (Polynomes.Var.t * Real.t) list) acc =
    let i = List.length s in
    let si = Covering.sample_outside (Covering.intervalpoly_to_interval acc) in

    match si with
    | None -> Unsat acc
    | Some x -> (
        let vi = variables.(i) in
        let s' = (vi, x) :: s in
        if i = (n-1) then Sat s'
        else
          let acc = get_unsat_intervals c (Polynomes.Assignment.of_list s') in
          let f = loop s' acc in
          match f with
          | Sat s'' -> Sat s''
          | Unsat i ->
              let r =
                construct_characterization (Polynomes.Assignment.of_list s') i
              in
              let new_i =
                interval_from_charachterization vi
                  (Polynomes.Assignment.of_list s)
                  x r
              in
                loop s' (new_i :: acc))
  in
  loop [] (get_unsat_intervals c (Polynomes.Assignment.of_list []))

  let resultat = get_unsat_cover [| c1; c2; c3 |] [|x ; y |] 1 

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
