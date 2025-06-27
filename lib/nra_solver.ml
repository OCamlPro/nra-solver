type sigma = Equal | Less
type contraint = Polynomes.t * sigma

type t = {
  poly_ctx : Polynomes.ctx;
  var_db : Libpoly.Variable.Db.t;
  var_order : Libpoly.Variable.Order.t;
  constraints : contraint Dynarray.t;
  tbl : (int, Polynomes.Var.t) Hashtbl.t;
  vars : Polynomes.Var.t array;
}

type term = Polynomes.t
type variable = Polynomes.Var.t

let create () =
  let var_db = Libpoly.Variable.Db.create () in
  let var_order = Libpoly.Variable.Order.create () in
  {
    var_db;
    var_order;
    poly_ctx =
      Polynomes.create_context
        ~ring:Libpoly.Ring.lp_Z (* Use the default integer ring *)
        var_db var_order;
    constraints = Dynarray.create ();
    tbl = Hashtbl.create 17;
    vars = [||];
  }

(* Associate an unique identifier to each variable because we could create
   multiple variables with the same name. *)

let create_variable t = Polynomes.Var.create t.var_db t.tbl
let zero_poly t = Polynomes.create ~ctx:t.poly_ctx

let create_simple t coeff var exponent =
  Polynomes.create_simple ~ctx:t.poly_ctx coeff var exponent

module Term = struct
  let variable t v = create_simple t (Libpoly.Integer.of_z (Z.of_int 1)) v 1
  let real t s = variable t (create_variable t s)
  let add t p q = Polynomes.add ~ctx:t.poly_ctx p q
  let sub t p q = Polynomes.sub ~ctx:t.poly_ctx p q
  let mul t p q = Polynomes.mul ~ctx:t.poly_ctx p q
  let minus t p = sub t (zero_poly t) p
  let div t p q = Polynomes.div ~ctx:t.poly_ctx p q
end

let assert_eq t p q =
  let r = Term.(sub t p q) in
  Dynarray.add_last t.constraints (r, Equal)

let assert_neq t p q =
  let r = Term.(sub t p q) in
  (* p <> q    <-> -(p-q)^2 < 0 *)
  let r' = Term.mul t r r in
  let r'' = Term.minus t r' in
  Dynarray.add_last t.constraints (r'', Less)

let assert_lt t p q =
  let r = Term.(sub t p q) in
  Dynarray.add_last t.constraints (r, Less)

let assert_leq t p q =
  let r = Term.(sub t q p) in
  (* p <= q <->  q - p >= 0 <-> il existe x tq  q - p = x^2*)
  let r' = Term.variable t (create_variable t "x") in
  let r'' = Term.add t r' r in
  Dynarray.add_last t.constraints (r'', Equal)

let assert_gt t p q =
  let r = Term.(sub t q p) in
  Dynarray.add_last t.constraints (r, Less)

let assert_geq t p q =
  let r = Term.(sub t p q) in
  (* p >= q <->  p - q >= 0 <-> il existe x tq  p - q = x^2*)
  let r' = Term.variable t (create_variable t "x") in
  let r'' = Term.add t r' r in
  Dynarray.add_last t.constraints (r'', Equal)

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#********** Algorithme 3 **************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
let array_filtrer2 (arr : contraint array) (f : contraint -> bool) :
    contraint array =
  let n = Array.length arr in
  let j = ref 0 in
  for i = 0 to n - 1 do
    if f arr.(i) then (
      arr.(!j) <- arr.(i);
      incr j)
  done;
  Array.sub arr 0 !j

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

let list_coefficients t (c : contraint) : Polynomes.t list =
  let p, _ = c in
  let d = Polynomes.degree p in
  let rec loop i acc =
    if i > d then acc
    else loop (i + 1) (Polynomes.get_coefficient ~ctx:t.poly_ctx p i :: acc)
  in
  loop 0 []

let is_poly_nul t (c : contraint) (s : Polynomes.Assignment.t) =
  let coeff_list = list_coefficients t c in
  let b = List.exists (fun p -> Polynomes.sgn p s <> 0) coeff_list in
  match b with true -> false | false -> true

let evaluate_contraint t (c : contraint) (s : Polynomes.Assignment.t)
    (v : Real.t) =
  let arr_p, s' = c in
  if is_poly_nul t c s then match s' with Equal -> true | Less -> false
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

let rec list_intervals t c s (p : Polynomes.t) (l : Covering.interval list) acc
    =
  match l with
  | [] -> acc
  | a :: l' ->
      let r = Covering.val_pick a in
      if evaluate_contraint t c s r then list_intervals t c s p l' acc
      else
        list_intervals t c s p l' (Covering.interval_to_intervalPoly a p :: acc)

let get_unsat_intervals t (c' : contraint array) (s : Polynomes.Assignment.t) :
    Covering.intervalPoly list =
  let s_list = Polynomes.Assignment.to_list s in
  let m = List.length s_list in
  let c =
    array_filtrer2 c' (fun x ->
        let poly, _ = x in
        (*let str = Polynomes.Var.get_name (Polynomes.top_variable poly) in
                      Format.printf "%s@." str;*)

        if
          Polynomes.Var.compare
            (Polynomes.top_variable poly)
            (Polynomes.Var.of_index (m + 1))
          = 0
        then true
        else false)
  in
  let n = Array.length c in
  let rec loop i acc =
    if i < 0 then acc
    else if is_poly_nul t c.(i) s then
      if evaluate_contraint t c.(i) s (Real.of_int 0) then loop (i - 1) acc
      else
        [
          Covering.interval_to_intervalPoly
            (Covering.Open (Covering.Ninf, Covering.Pinf))
            (fst c.(i));
        ]
    else
      let p, _ = c.(i) in
      let roots = Polynomes.roots_isolate p s in
      let regions = Covering.pointsToIntervals roots in
      (*let str = Covering.show_intervals regions in 
                    Format.printf " %s maaaaaaaaamaaaaaaaaaaaaaaaaaaaaaaaaaaaaa @." str;*)
      let acc = list_intervals t c.(i) s p regions acc in
      loop (i - 1) acc
  in
  loop (n - 1) []

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*******************Algorithme 4******************************************)

let discriminant_set t (p_set : Polynomes.Set.t) : Polynomes.Set.t =
  Polynomes.Set.map (Polynomes.disc t.poly_ctx) p_set

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

let boucle0 (p : Polynomes.t) (p_set : Polynomes.Set.t) =
  let rec loop l acc =
    match l with
    | [] -> acc
    | q :: l -> loop l (Polynomes.Set.add (Polynomes.resultant p q) acc)
  in
  loop (Polynomes.to_list p_set) Polynomes.Set.empty

let boucle1 (u_set : Polynomes.Set.t) (l_set : Polynomes.Set.t) :
    Polynomes.Set.t =
  let rec loop u acc =
    match u with
    | [] -> acc
    | q :: u -> loop u (Polynomes.Set.union (boucle0 q l_set) acc)
  in
  loop (Polynomes.to_list u_set) Polynomes.Set.empty

let boucle2 (l : Covering.intervalPoly list) : Polynomes.Set.t =
  let n = List.length l in
  let l_array = Array.of_list l in
  let rec loop i acc =
    if i = n - 1 then acc
    else
      loop (i + 1)
        (Polynomes.Set.union
           (boucle1 l_array.(i).u_set l_array.(i + 1).l_set)
           acc)
  in
  loop 0 Polynomes.Set.empty

let construct_characterization t (s : Polynomes.Assignment.t)
    (i_list : Covering.intervalPoly list) : Polynomes.Set.t =
  (*let str3 = Covering.show_intervals_poly i_list in
                    Format.printf "%s le recouvrement  @." str3;*)
  let good_cover = Covering.compute_cover i_list in
  (*let str2 = Covering.show_intervals_poly good_cover in
                  Format.printf "%s le bon recouvrement  @." str2;*)
  let rec loop (l : Covering.intervalPoly list) (acc : Polynomes.Set.t) =
    match l with
    | [] -> acc
    | x :: l ->
        (*let algo6 = Polynomes.required_coefficients s x.p_set in 
                      let strr = Polynomes.string_of_polynomial_list (Polynomes.to_list algo6) in 
                      Format.printf "%s resultat de algo 6 " strr;*)
        loop l
          (union_poly_sets
             [
               discriminant_set t x.p_set;
               x.p_orthogonal_set;
               Polynomes.required_coefficients t.poly_ctx s x.p_set;
               resultant_lower x.l_bound s x.l_set x.p_set;
               resultant_upper x.u_bound s x.u_set x.p_set;
             ])
  in

  let l = loop good_cover Polynomes.Set.empty in
  (*let str1 = Polynomes.string_of_polynomial_list (Polynomes.to_list l) in
                  Format.printf "resultat de l'algo 4 premiere boucle  %s 2 @." str1;*)
  let l' = boucle2 good_cover in
  (*let str = Polynomes.string_of_polynomial_list (Polynomes.to_list l') in
                  Format.printf " resultat de boucle 2 : %s @." str;*)
  let l'' = Polynomes.Set.union l' l in
  (*let str3= Polynomes.string_of_polynomial_list (Polynomes.to_list l'') in
                  Format.printf " resultat avant le filtrage :::::::::::::::::::::::::::::::::::::::::::::::::::::: : %s @." str3;*)
  (* ça marche pas avec la fonction primitive de libpoly avec l'exemple : xyz -1 = 0 *)
  (*let l1 = Polynomes.Set.map (fun p -> Polynomes.primitive p) l'' in
                  let str2 = Polynomes.string_of_polynomial_list (Polynomes.to_list l1) in
                  Format.printf " resultat aprés le filtrage :::::::::::::::::::::::::: %s @." str2;*)
  Polynomes.Set.filter
    (fun x -> if Polynomes.is_constant x = 1 then false else true)
    l''

(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************************************************************************)
(*#######"#"#"#"##"##"#*************** Algorithme 5 ********************************************)

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

let assert_top_variable (p_set : Polynomes.Set.t) (v : Polynomes.Var.t) =
  let p_list = Polynomes.to_list p_set in
  List.for_all
    (fun x -> Polynomes.Var.compare (Polynomes.top_variable x) v = 0)
    p_list

let interval_from_charachterization (v : Polynomes.Var.t)
    (s : Polynomes.Assignment.t) (si : Real.t) (p_set : Polynomes.Set.t) :
    Covering.intervalPoly =
  let pi =
    Polynomes.Set.filter
      (fun x -> Polynomes.Var.compare (Polynomes.top_variable x) v = 0)
      p_set
  in
  (*let str1 = Polynomes.string_of_polynomial_list (Polynomes.to_list pi) in
                  Format.printf "%s : ma list Pi c'est : @." str1;*)
  let p_orthogonal =
    Polynomes.Set.filter
      (fun x -> if Polynomes.Set.mem x pi then false else true)
      p_set
  in
  assert (assert_top_variable pi v);

  (*let str2 =
                    Polynomes.string_of_polynomial_list (Polynomes.to_list p_orthogonal)
                  in
                  Format.printf "%s : ma list P_orthogonal c'est : @." str2;*)
  let roots_list = compute_map_roots pi s in

  let lower_bound = compute_l roots_list (Finite si) in
  let upper_bound = compute_u roots_list (Finite si) in
  let l_set_result = set_function roots_list lower_bound in
  let u_set_result = set_function roots_list upper_bound in
  assert (assert_top_variable l_set_result v);
  assert (assert_top_variable u_set_result v);

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

let get_unsat_cover t : res =
  let c = Dynarray.to_array t.constraints in
  let variables = t.vars in
  let n = Array.length variables in
  let rec loop (s : (Polynomes.Var.t * Real.t) list) acc =
    let i = List.length s in
    (*let amchich = Covering.intervalpoly_to_interval acc in
                (*let str1 = Covering.show_intervals amchich in
                Format.printf " %s amchich : @." str1;*)
            
                let afrukh = Covering.compute_good_covering amchich in
               (* let str = Covering.show_intervals afrukh in
                Format.printf " %s afrukh : @." str;*)*)
    (*Fmt.pr "igeni: %a@." Covering.pp_intervals_poly acc;*)
    let si = Covering.sample_outside (Covering.intervalpoly_to_interval acc) in
    (*Fmt.pr "lqa3a: %s --> %a@." (Polynomes.Var.get_name variables.(i)) Fmt.(option ~none:(fun ppf () -> Fmt.pf ppf "NONE") Real.pp) si;*)

    match si with
    | None -> Unsat acc
    | Some x -> (
        (*let x_value = Real.to_string x in Format.printf "%s le sample point : @. " x_value ;*)
        let vi = variables.(i) in
        let s' = (vi, x) :: s in
        if i = n - 1 then Sat s'
        else
          let acc1 =
            get_unsat_intervals t c (Polynomes.Assignment.of_list s')
          in
          let f = loop s' acc1 in
          match f with
          | Sat s'' -> Sat s''
          | Unsat i ->
              let r =
                construct_characterization t (Polynomes.Assignment.of_list s') i
              in
              (*let str4 = Polynomes.string_of_polynomial_list (Polynomes.to_list  r) in 
                            Format.printf " %s sortie de l'algo44444444444444444444444444444444444444444444444444444444444444444444444444 @." str4;*)

              let new_i =
                interval_from_charachterization vi
                  (Polynomes.Assignment.of_list s)
                  x r
              in
              (*let str2 =
                            Covering.show_intervals_poly
                              ( [ new_i ])
                          in
                          Format.printf "%s la sortie de l'algorothm 5 : @." str2;*)
              let () =
                match new_i.interval with
                | Covering.Exact _ -> Fmt.pr "je ne peux pas généraliser@."
                | _ -> ()
              in

              loop s (new_i :: acc))
  in
  loop [] (get_unsat_intervals t c (Polynomes.Assignment.of_list []))

type solve_result = Sat of (Polynomes.Var.t * Real.t) list | Unsat | Unknown

let solve t : solve_result =
  match get_unsat_cover t with Sat x -> Sat x | Unsat _ -> Unsat

module Covering = Covering
module Real = Real
module Constraint = Constraint
module Z_poly = Z_poly
module Polynomes = Polynomes
