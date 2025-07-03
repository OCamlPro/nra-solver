open QCheck2
module Covering = Nra_solver.Covering
module Constraint = Nra_solver.Constraint
module Real = Nra_solver.Real
module Z_poly = Nra_solver.Z_poly
module Polynomes = Nra_solver.Polynomes

type bound = Finite of int | Pinf | Ninf

let int_range_exclusive l u : int option Gen.t =
  let l' = l + 1 in
  let u' = u - 1 in
  if u' - l' > 1 then Gen.map Option.some (Gen.int_range l' u')
  else Gen.pure None

let fake_ninf = -500
let fake_pinf = 500

let bound_to_int b =
  match b with
  | Finite i -> min fake_pinf (max fake_ninf i)
  | Pinf -> fake_pinf
  | Ninf -> fake_ninf

let sample_interval b1 b2 : int option Gen.t =
  int_range_exclusive (bound_to_int b1) (bound_to_int b2)

type interval = Open of bound * bound | Exact of int

let to_covering_bound b =
  match b with
  | Finite i -> Covering.Finite (Real.of_int i)
  | Pinf -> Covering.Pinf
  | Ninf -> Covering.Ninf

let to_covering_interval i =
  match i with
  | Open (l, u) -> Covering.Open (to_covering_bound l, to_covering_bound u)
  | Exact a -> Covering.Exact (Real.of_int a)

type tactic = bound -> bound -> interval list Gen.t

let trivial l u = Gen.pure [ Open (l, u) ]

let split l u =
  Gen.map
    (fun o ->
      match o with
      | Some m -> [ Open (l, Finite m); Exact m; Open (Finite m, u) ]
      | None -> [ Open (l, u) ])
    (sample_interval l u)

let basile l u =
  Gen.map
    (fun o ->
      match o with
      | Some m -> [ Open (l, Finite m); Open (l, u) ]
      | None -> [ Open (l, u) ])
    (sample_interval l u)

type itree = Lf of interval | Br of itree list

let lf x = Lf x
let br l = Br l

let fringe t =
  let rec loop acc t =
    match t with Lf i -> i :: acc | Br l -> List.fold_left loop acc l
  in
  loop [] t |> List.rev

let generator_itree ~fuel (tactics : (int * tactic) list) l u : itree Gen.t =
  Gen.(
    sized_size (pure fuel) (fun fuel ->
        fix
          (fun self (fuel, l, u) ->
            match fuel with
            | 0 -> pure @@ lf (Open (l, u))
            | n ->
                bind (frequencyl tactics) @@ fun tactic ->
                bind (tactic l u) @@ fun ix ->
                let fuel =
                  let n = List.length ix in
                  if n = 1 then fuel - 1 else fuel / n
                in
                let g =
                  List.map
                    (fun (i : interval) ->
                      match i with
                      | Open (a, b) -> self (fuel, a, b)
                      | Exact _ as i -> pure @@ lf i)
                    ix
                in
                map br (flatten_l g))
          (fuel, l, u)))

let generator_covering ~fuel (tactics : (int * tactic) list) :
    Covering.interval list Gen.t =
  Gen.map
    (fun t -> List.map to_covering_interval @@ fringe t)
    (generator_itree ~fuel tactics Ninf Pinf)

let gen1 = generator_covering ~fuel:15 [ (1, split) ]
let gen2 = generator_covering ~fuel:15 [ (1, split); (3, basile) ]

let print_covering (c : Covering.interval list) =
  Format.asprintf "%a" Covering.pp_debug_intervals c

let test_basile =
  Test.make ~print:print_covering ~count:1000 ~name:__FUNCTION__ gen2 (fun c ->
      let d = Covering.compute_good_covering c in
      Covering.is_good_covering d)

(*
let is_covering = Covering.is_covering
let open_ x y = Covering.Open (Finite (Real.of_int x), Finite (Real.of_int y))
let exact x = Covering.Exact (Real.of_int x)
let finite x = Covering.Finite (Real.of_int x)
let floor x = Z.to_int @@ Real.floor x
let ceil x = Z.to_int @@ Real.ceil x
let gen_real : Real.t Gen.t = Gen.map Real.of_int (Gen.int_range 0 100)
let three = Real.of_int 3

 

let longueur_interval a b : bool =
  match (a, b) with
  | Covering.Finite a_val, Covering.Finite b_val ->
      Real.compare (Real.sub b_val a_val) three >= 0
  | _ -> true 


(*************************************************************************)
  let inter = Covering.inter 
  let length = Covering.length  
  

let length_inter_500  (i : Covering.interval) =  
 match inter i (Open (finite (-500) , finite (500))) with 
 |Some j -> length j 
 |None -> Real.of_int 0

  let assez_grand (a : Real.t) (b : Real.t) : bool
   = Real.compare (length_inter_500 (Covering.Open (Finite a , Finite b)) ) (Real.of_int 1) >= 1
    
let to_real b = 
  match b with 
  |Covering.Finite a -> a 
  |Pinf -> Real.of_int 500
  |Ninf -> Real.of_int (-500)

  let fake_ninf = -500 
  let fake_pinf = 500

  let gen_real : Real.t Gen.t = 
    Gen.map Real.of_int (Gen.int_range fake_ninf fake_pinf)

  let real_range (low : Covering.bound) (high : Covering.bound) : Real.t option Gen.t =
    match low, high with 
    | Ninf, Pinf -> 
      Gen.map Option.some gen_real 
    | Ninf, Finite b when Real.compare b (Real.of_int fake_ninf) >= 0 -> 
      Gen.int_range fake_ninf 

      let ilow = Real.Syntax.(to_real low + ~$1) in
      let ihigh = Real.Syntax.(to_real high - ~$1) in

  if assez_grand low high then
    Gen.map (fun i -> Some (finite i)) (Gen.int_range (ceil (to_real low) + 1) (floor (to_real high) - 1))
  else
    Gen.pure None
(**********************************************************************************)
let gen_real_bound (low : Covering.bound) (high : Covering.bound) :
    Covering.bound Gen.t =
  match (low, high) with
  | Covering.Finite a, Covering.Finite b
    when longueur_interval (Covering.Finite a) (Covering.Finite b) ->
      Gen.map finite (Gen.int_range (ceil a + 1) (floor b -1))
  | Covering.Ninf, Covering.Finite a ->
      Gen.map finite (Gen.int_range (-500) (floor a - 1))
  | Covering.Finite b, Covering.Pinf ->
      Gen.map finite (Gen.int_range (ceil b + 1) 500)
  | Covering.Ninf, Covering.Pinf -> Gen.map finite (Gen.int_range (-500) 500)
  | b1, b2 ->
      Fmt.failwith "There is no integer into (%a, %a)" Covering.pp_bound b1
        Covering.pp_bound b2

let gen_bound : Covering.bound Gen.t =
  Gen.oneof
    [
      (* Générer un Real.t aléatoire et l'envelopper dans Finite *)
      Gen.map finite (Gen.int_range 0 100);
      Gen.pure Covering.Pinf;
      Gen.pure Covering.Ninf;
    ]

let gen_exact (low : int) (high : int) : Covering.interval Gen.t =
  Gen.map exact (Gen.int_range low high)

let gen_interval : Covering.interval Gen.t =
  Gen.oneof
    [
      Gen.map exact (Gen.int_range 0 100);
      Gen.bind (Gen.pair gen_bound gen_bound) (fun (b1, b2) ->
          if Covering.compare_bound b1 b2 < 0 then
            Gen.pure (Covering.Open (b1, b2))
          else Gen.map exact (Gen.int_range 0 100));
    ]

type interval_tree =
  | Leaf of Covering.interval
  | Node of interval_tree * Covering.interval * interval_tree

let node x y z = Node (x, y, z)

let gen_interval_tree : interval_tree Gen.t =
  Gen.(
    sized (fun fuel ->
        fix
          (fun self (fuel, low, high) ->
            match fuel with
            | 0 -> Gen.pure @@ Leaf (Covering.Open (low, high))
            | n ->
                if longueur_interval low high then
                  bind (gen_real_bound low high) @@ fun b ->
                  match b with
                  | Covering.Finite b_val ->
                      map3 node
                        (self (n / 2, low, b))
                        (pure @@ Covering.Exact b_val)
                        (self (n / 2, b, high))
                  | _ -> assert false
                else Gen.pure @@ Leaf (Open (low, high)))
          (fuel, Covering.Ninf, Covering.Pinf)))

type interval_tree' =
  | Leaff of Covering.interval
  | Node2 of interval_tree' * interval_tree'
  | Node3 of interval_tree' * Covering.interval * interval_tree'

let node2 x y = Node2 (x, y)
let node3 x y z = Node3 (x, y, z)
let leaff_open x y = Leaff (Covering.Open (x, y))

(*""""""""""""""""""""""""""""""" genere good coverings"""""""""""""""""""""""""""""""""""""""""""*)
let gen_good_interval_tree'' : interval_tree' Gen.t =
  Gen.(
    sized (fun fuel ->
        fix
          (fun self' (fuel, low, high) ->
            match fuel with
            | 0 ->
                  bind (gen_real_bound' low high) @@ fun b ->
                    (match b with 
                  |Some b_bound -> 
                    bind (gen_real_bound' b_bound high) @@ fun c ->
                      (match c with 
                      |Some c_bound ->
                    pure (node2 (leaff_open low c_bound) (leaff_open b_bound high))
                      |None -> Gen.pure @@ Leaff (Open (low, high)))
                   |None ->  Gen.pure @@ Leaff (Open (low, high)))
            | n ->
                  bind (gen_real_bound' low high) @@ fun b -> 
          (match b with 
           |Some b_bound -> 
                  (match b_bound with
                  | Covering.Finite b_val ->
                      map3 node3
                        (self' (n / 2, low, b_bound))
                        (pure @@ Covering.Exact b_val)
                        (self' (n / 2, b_bound, high))
                  | _ -> assert false)
            |None -> Gen.pure @@ Leaff (Open (low, high))))
          (fuel, Covering.Ninf, Covering.Pinf)))   
(*""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""*)
(*"""""""""""""""""""""""""""""" genere des coverings """"""""""""""""""""""""""""""""""""*)
let gen_interval_tree1 : interval_tree' Gen.t =
  Gen.(
    sized (fun fuel ->
        fix
          (fun self' (fuel, low, high) ->
            match fuel with
            | 0 -> Gen.pure @@ Leaff (Covering.Open (low, high))
            | n ->
                frequency
                  [
                    ( 1,
                      
                        bind (gen_real_bound' low high) @@ fun b ->
                        (match b with 
                          |Some b_bound  ->
                          bind (gen_real_bound' b_bound high) @@ fun c ->
                            (match c with 
                            |Some c_val -> 
                          map2 node2
                            (self' (n / 2, low, c_val ))
                            (self' (n / 2, b_bound, high))
                            |None -> Gen.pure @@ Leaff (Covering.Open (low, high)) )
                          |None ->  Gen.pure @@ Leaff (Covering.Open (low, high))   )
                        );
                    ( 2,
                        bind (gen_real_bound' low high) @@ fun b -> 
                        (match b with 
                         |Some b_bound -> 
                            (match b_bound with
                            | Covering.Finite b_val ->
                            map3 node3
                              (self' (n / 2, low, b_bound))
                              (pure @@ Covering.Exact b_val)
                              (self' (n / 2, b_bound, high))
                            | _ -> assert false)
                          |None -> Gen.pure @@ Leaff (Open (low, high))  )

                        );
                  ])
          (fuel, Covering.Ninf, Covering.Pinf)))

(*****************************gen coverings 2*******************************************************)
let gen_interval_tree2 : interval_tree' Gen.t =
  Gen.(
    sized (fun fuel ->
        fix
          (fun self' (fuel, low, high) ->
            match fuel with
            | 0 -> Gen.pure @@ Leaff (Covering.Open (low, high))
            | n ->
                frequency
                  [
                    ( 0,
                      
                        bind (gen_real_bound' low high) @@ fun b ->
                        (match b with 
                          |Some b_bound  ->
                          bind (gen_real_bound' b_bound high) @@ fun c ->
                            (match c with 
                            |Some c_val -> 
                          map2 node2
                            (self' (n / 2, low, c_val ))
                            (self' (n / 2, b_bound, high))
                            |None -> Gen.pure @@ Leaff (Covering.Open (low, high)) )
                          |None ->  Gen.pure @@ Leaff (Covering.Open (low, high))   )
                        );
                    ( 0,
                        bind (gen_real_bound' low high) @@ fun b -> 
                        (match b with 
                         |Some b_bound -> 
                            (match b_bound with
                            | Covering.Finite b_val ->
                            map3 node3
                              (self' (n / 2, low, b_bound))
                              (pure @@ Covering.Exact b_val)
                              (self' (n / 2, b_bound, high))
                            | _ -> assert false)
                          |None -> Gen.pure @@ Leaff (Open (low, high))  )  );
                      (3,
                        bind (gen_real_bound' low high) @@ fun b ->
                        match b with 
                         |Some b_bound ->
                          map2 node2 
                          (self' (n /2, low, b_bound))
                          (self' (n / 2 , low, high)) 
                        |None -> Gen.pure @@ Leaff (Open (low, high))
                          
                                                                  );    
                  ])
          (fuel, Covering.Ninf, Covering.Pinf)))

(***************************************************************************************************)
let rec fringe_tree (t : interval_tree') : Covering.interval list =
  match t with
  | Leaff x -> [ x ]
  | Node2 (t1, t2) -> fringe_tree t1 @ fringe_tree t2
  | Node3 (t1, y, t2) -> fringe_tree t1 @ [ y ] @ fringe_tree t2

let gen_good_covering2 : Covering.interval list Gen.t =
  Gen.bind gen_good_interval_tree'' (fun t -> Gen.pure (fringe_tree t))

let gen_coverings : Covering.interval list Gen.t =
  Gen.bind gen_interval_tree2 (fun t -> Gen.pure (fringe_tree t))


  let sample_covering : Covering.interval list = Gen.generate1 gen_coverings

  
  

let is_good_covering = Covering.is_good_covering
let compute_good_covering = Covering.compute_good_covering

(* --- Generators --- *)
(* QCheck needs generators to create random test inputs.
   You will need to write generators for your 'covering' type or its components.
   This is often the most challenging part of setting up PBT.
   For now, we use a simple placeholder. *)

let pp_bound ppf b =
  match b with
  | Covering.Finite b -> Format.fprintf ppf "%a" Real.pp b
  | Covering.Pinf -> Format.fprintf ppf "+oo"
  | Covering.Ninf -> Format.fprintf ppf "-oo"

let pp_interval ppf i =
  match i with
  | Covering.Open (b1, b2) ->
      Format.fprintf ppf "(%a, %a)" pp_bound b1 pp_bound b2
  | Exact b -> Format.fprintf ppf "{%a}" Real.pp b

let pp_intervals ppf l =
  let pp_sep ppf () = Format.fprintf ppf "∪" in
  Format.pp_print_list ~pp_sep pp_interval ppf l

let gen_sorted_list (n : int) : Real.t list Gen.t =
  Gen.bind
    (Gen.list_size (Gen.pure n) gen_real)
    (fun l -> Gen.pure (List.sort_uniq Real.compare l))

let build_intervals l =
  let rec loop acc l =
    match l with
    | a :: c :: b :: d :: l ->
        loop
          (Covering.Open (Finite c, Finite d)
          :: Covering.Open (Finite a, Finite b)
          :: acc)
          (b :: d :: l)
    | e :: _ :: _ -> Covering.Open (Finite e, Pinf) :: acc
    | _ -> assert false
  in
  let result = List.rev (loop [] l) in
  match result with
  | Covering.Open (_, b) :: rest -> Covering.Open (Ninf, b) :: rest
  | _ -> result

let gen_good_covering (n : int) : Covering.interval list Gen.t =
  Gen.bind (gen_sorted_list (2 * n)) (fun l -> Gen.pure (build_intervals l))

(* let () =
  let l = Gen.generate ~n:10 (gen_good_covering 5) in
  let pp_sep ppf () = Format.fprintf ppf "\n" in
  Format.printf "%a\n@." (Format.pp_print_list ~pp_sep pp_intervals) l *)

let print_covering (c : Covering.interval list) =
  Format.asprintf "%a" Covering.pp_intervals c

let test_is_good_covering =
  Test.make ~print:print_covering ~count:1000 ~name:__FUNCTION__
    (gen_good_covering 3) is_good_covering

let test_compute_good_covering_identity =
  Test.make ~print:print_covering ~count:1000
    ~name:"compute_good_covering_identity" (gen_good_covering 10) (fun c ->
      let d = compute_good_covering c in
      List.equal Covering.equal_interval c d)

(*************************les tests **************************************************)

let test_is_good_covering2 =
  Test.make ~print:print_covering ~count:1000 ~name:__FUNCTION__
    gen_good_covering2 is_good_covering

let test_is_covering =
  Test.make ~print:print_covering ~count:1000 ~name:__FUNCTION__ gen_coverings
    is_covering

let test_compute_good_covering_identity2 =
  Test.make ~print:print_covering ~count:1000
    ~name:"compute_good_covering_identity" gen_good_covering2 (fun c ->
      let d = compute_good_covering c in
      List.equal Covering.equal_interval c d)

let test_compute_good_covering =
  Test.make ~print:print_covering ~count:10000
    ~name:"compute_good_covering_identity" gen_coverings (fun c ->
      let d = compute_good_covering c in
      is_good_covering d)
(**********************************************************************************************)



(* --- Properties to Test --- *)

(* Property 1: The result of compute_good_covering should be a valid covering. *)
(*let test_compute_good_is_valid =
  Test.make ~count:100 ~name:"compute_good_covering produces a valid covering"
    ~print:print_tree covering_gen (fun c ->
      let gc = Covering.compute_good_covering c in
      match is_covering gc with
      | true -> true
      | false ->
          Test.fail_report
            "Result of compute_good_covering is not a valid covering"
      (* This assumes 'is_covering' correctly defines validity *))*)

(* Property 2: The result of compute_good_covering should be a 'good' covering. *)
(*let test_compute_good_is_good =
  Test.make ~count:100 ~name:"compute_good_covering produces a 'good' covering"
    ~print:print_tree covering_gen (fun c ->
      let gc = compute_good_covering c in
      match is_good_covering gc with
      | true -> true
      | false ->
          Test.fail_report
            "Result of compute_good_covering is not a 'good' covering"
      (* This assumes 'is_good_covering' correctly defines goodness *))*)

(* TODO: Add more properties as needed, for example:
   - Idempotence: compute_good_covering (compute_good_covering c) == compute_good_covering c (requires an equality/equivalence function)
   - Preservation: Check that the good covering 'gc' covers the same set of points as the original 'c' (requires a way to check point membership)
   - Properties of specific covering constructor functions you might write.
*)

(* --- Test Suite --- *)
(* Group all the tests together *)
let covering_suite =
  [
    test_is_good_covering;
    test_compute_good_covering_identity;
    test_is_good_covering2;
    test_is_covering;
    (*test_compute_good_covering_identity2;*)
    (*test_compute_good_covering*)
    (*test_compute_good_is_valid; test_compute_good_is_good *)
  ]

(* --- Run Tests --- *)
(* This line registers the suite to be run by the dune runner *)
let () = QCheck_base_runner.run_tests_main covering_suite
*)
let gen_small_nonzero : int Gen.t =
  Gen.(bind (1 -- 10) @@ fun x -> oneofl [ x; -x ])

let gen_degres_coeff (n : int) : (int * int list) Gen.t =
  (* n ici c'est le nombre de variable ( nb de degres )*)
  Gen.(pair gen_small_nonzero (list_size (pure n) (0 -- 3)))
(* genere un monome normal*)

let gen_degres_coeff_main_var_non_nul (n : int) : (int * int list) Gen.t =
  Gen.(
    pair gen_small_nonzero
      (Gen.map2
         (fun debut_list dernier_element -> debut_list @ dernier_element)
         (list_size (pure (n - 1)) (0 -- 4))
         (list_size (pure 1) (1 -- 4)))
    (*genere un monome ou le degres de la variable principale est non nul*))

let compare_pair ((_, u) : int * int list) ((_, v) : int * int list) : int =
  List.compare Int.compare u v

(*let x = Polynomes.Var.create "x"
let y = Polynomes.Var.create "y"
let z = Polynomes.Var.create "z"
let variables = [| x; y; z |]
let variables_without_z = [ x; y ]*)

let gen_list_monomes (n : int) : (int * int list) list Gen.t =
  Gen.map2
    (fun l1 l2 -> l1 @ l2)
    (Gen.list_size (Gen.int_range 1 2) (gen_degres_coeff n))
    (* une liste de pair qui va me former mon polynome *)
    (Gen.list_size (Gen.pure 1) (gen_degres_coeff_main_var_non_nul n))
(* le derner element de la liste est un monome qui a le dernier deg non nul *)

let gen_poly (t : Nra_solver.t) : Polynomes.t Gen.t =
  let vars = Nra_solver.variables t in
  (* n : nombre des variables*)
  let n = Array.length vars in
  Gen.bind (gen_list_monomes n) (fun l ->
      let l' = List.sort_uniq compare_pair l in

      Gen.pure
        (Polynomes.mk_polynomes
           (Nra_solver.t_to_poly_ctx t)
           (Array.to_list vars) l'))

let gen_constraint t : Nra_solver.contraint Gen.t =
  Gen.bind (gen_poly t) (fun p ->
      Gen.frequency
        [
          (2, Gen.pure (p, Nra_solver.Less)); (1, Gen.pure (p, Nra_solver.Equal));
        ])

let gen_array_constraints t : Nra_solver.contraint array Gen.t =
  Gen.bind
    (Gen.array_size (Gen.pure 2) (gen_constraint t))
    (fun l -> Gen.pure l)

let test_evaluation_constraints t (l : Nra_solver.contraint array)
    (s : Polynomes.Assignment.t) : bool =
  let l_list = Array.to_list l in
  let booleen_func c =
    let p, sigma = c in
    match sigma with
    | Nra_solver.Equal -> Polynomes.sgn (Nra_solver.t_to_poly_ctx t) p s = 0
    | Nra_solver.Less -> Polynomes.sgn (Nra_solver.t_to_poly_ctx t) p s < 0
  in
  List.for_all booleen_func l_list

let test_solver t : bool =
  let c = Nra_solver.t_to_constraints t in
  let res = Nra_solver.solve t in
  Format.printf "%s @." (Nra_solver.show_sat_or_unsat t res);
  match res with
  | Nra_solver.Sat l ->
      let s = Polynomes.Assignment.of_list l in
      test_evaluation_constraints t (Dynarray.to_array c) s
  | Nra_solver.Unsat -> true
  | Unknown -> false

let gen_s (* assignment.t *) t : Polynomes.Assignment.t Gen.t =
  let vars = Nra_solver.variables t in
  let n = Array.length vars in
  Gen.bind
    (Gen.list_size (Gen.pure (n - 1)) (Gen.int_range (-50) 50))
    (fun l ->
      Gen.pure
        (Polynomes.mk_assignment
           (List.rev (List.tl (List.rev (Array.to_list vars))))
           l))

let gen_pair t : (Nra_solver.contraint array * Polynomes.Assignment.t) Gen.t =
  Gen.pair (gen_array_constraints t) (gen_s t)

let test_constraint t (s : Polynomes.Assignment.t)
    (c : Nra_solver.contraint array) (i : Covering.interval) : bool =
  Array.for_all
    (fun const -> Nra_solver.evaluate_contraint t const s (Covering.val_pick i))
    c

let test_constraints t (s : Polynomes.Assignment.t)
    (c : Nra_solver.contraint array) (l : Covering.interval list) : bool =
  let l_arr = Array.of_list l in
  let n = Array.length l_arr in
  let rec loop i acc =
    if i < 0 then acc
    else if not (test_constraint t s c l_arr.(i)) then
      loop (i - 1) (l_arr.(i) :: acc)
    else loop (i - 1) acc
  in
  let res = loop (n - 1) [] in
  if List.length res = n then true else false

let gen_bound : Covering.bound Gen.t =
  Gen.oneof
    [
      Gen.map
        (fun x -> Covering.Finite x)
        (Gen.map Real.of_int (Gen.int_range 0 100));
      Gen.pure Covering.Pinf;
      Gen.pure Covering.Ninf;
    ]

let gen_exact_interval : Covering.interval Gen.t =
  Gen.map (fun x -> Covering.Exact (Real.of_int x)) (Gen.int_range 0 100)

let gen_interval : Covering.interval Gen.t =
  Gen.frequency
    [
      (1, gen_exact_interval);
      ( 1,
        Gen.bind (Gen.pair gen_bound gen_bound) (fun (b1, b2) ->
            let c = Covering.compare_bound b1 b2 in
            if c = 0 then
              match b1 with
              | Covering.Finite r -> Gen.pure (Covering.Exact r)
              | Pinf | Ninf -> Gen.pure (Covering.Exact (Real.of_int 0))
            else if c < 0 then Gen.pure (Covering.Open (b1, b2))
            else Gen.pure (Covering.Open (b2, b1))) );
    ]

let gen_interval_list : Covering.interval list Gen.t = Gen.list gen_interval

let gen_intervals_list_or_coverings : Covering.interval list Gen.t =
  Gen.frequency [ (1, gen2); (1, gen_interval_list) ]

let appartenance (x : Real.t) (i : Covering.interval) : bool =
  match i with
  | Covering.Exact a -> Real.compare x a = 0
  | Open (a, b) ->
      Covering.compare_bound a (Finite x) < 0
      && Covering.compare_bound (Finite x) b < 0

let test_appartenance (x : Real.t) (l : Covering.interval list) : bool =
  List.exists (fun i -> appartenance x i) l

let test_sample_outside l =
  match Covering.sample_outside l with
  | None -> Covering.is_covering l
  | Some x -> if test_appartenance x l then false else true

let pp_array_constraint ppf c = Nra_solver.pp_array_of_constraints ppf c

let pp_pair t ppf
    ((c : Nra_solver.contraint array), (s : Polynomes.Assignment.t)) : unit =
  Format.fprintf ppf
    "(@[<v 0>c -> %a@ s -> %a@])" (* Nouvelle chaîne de format ici *)
    pp_array_constraint c
    (Polynomes.Assignment.pp_assignment (Nra_solver.t_to_poly_ctx t))
    s

(*let p1 =
  Polynomes.mk_polynomes variables_without_z
    [ (-1, [ 2; 0 ]); (4, [ 0; 0 ]); (4, [ 0; 1 ]) ]

let p2 =
  Polynomes.mk_polynomes variables_without_z
    [ (-1, [ 2; 0 ]); (3, [ 0; 0 ]); (2, [ 1; 0 ]); (-4, [ 0; 1 ]) ]

let p3 =
  Polynomes.mk_polynomes variables_without_z
    [ (1, [ 1; 0 ]); (2, [ 0; 0 ]); (-4, [ 0; 1 ]) ]

let c1 =
  ( Polynomes.mk_polynomes variables_without_z
      [ (-1, [ 2; 0 ]); (4, [ 0; 0 ]); (4, [ 0; 1 ]) ],
    Constraint.Less )

let c2 =
  ( Polynomes.mk_polynomes variables_without_z
      [ (-1, [ 2; 0 ]); (3, [ 0; 0 ]); (2, [ 1; 0 ]); (-4, [ 0; 1 ]) ],
    Constraint.Less )

let c3 =
  ( Polynomes.mk_polynomes variables_without_z
      [ (1, [ 1; 0 ]); (2, [ 0; 0 ]); (-4, [ 0; 1 ]) ],
    Constraint.Less )
*)

(*let mon_test =
  let t = Nra_solver.create () in
  ignore (Nra_solver.create_variable t "x" : Nra_solver.variable);
  ignore (Nra_solver.create_variable t "y" : Nra_solver.variable);
  let variables = Nra_solver.variables t in
  let p =
    Polynomes.mk_polynomes
      (Nra_solver.t_to_poly_ctx t)
      (Array.to_list variables)
      [ (1, [ 2; 0 ]); (1, [ 0; 2 ]) ]
  in
  Nra_solver.assert_lt t p (Polynomes.zero (Nra_solver.t_to_poly_ctx t));
  let ans = Nra_solver.solve t in
  let s = Nra_solver.show_sat_or_unsat t ans in
  Format.printf "mon_test: %s @." s *)

let mon_test2 =
  let t = Nra_solver.create () in
  ignore (Nra_solver.create_variable t "x" : Nra_solver.variable);
  ignore (Nra_solver.create_variable t "y" : Nra_solver.variable);

  let vars = Nra_solver.variables t in 

  let p2 = Polynomes.mk_polynomes (Nra_solver.t_to_poly_ctx t) (Array.to_list vars) [( 1,[0 ; 1])] in
  Nra_solver.assert_gt t p2 (Polynomes.zero (Nra_solver.t_to_poly_ctx t));
  let p1 = Polynomes.mk_polynomes (Nra_solver.t_to_poly_ctx t) (Array.to_list vars) [( 1,[1 ; 0])] in
  Nra_solver.assert_gt t p1 (Polynomes.zero (Nra_solver.t_to_poly_ctx t));

  let p4 = Polynomes.mk_polynomes (Nra_solver.t_to_poly_ctx t) (Array.to_list vars) [( 1,[1 ; 0]) ;( 1,[0 ; 1]) ] in
  Nra_solver.assert_eq t p4 (Polynomes.zero (Nra_solver.t_to_poly_ctx t));


  Fmt.pr "Contexte: %a@." Nra_solver.pp t;
  let ans = Nra_solver.solve t in
  let s = Nra_solver.show_sat_or_unsat t ans in
  Format.printf "mon_test2: %s @." s



(*let mon_test3 =
  let t = Nra_solver.create () in
  let p = Polynomes.of_int (Nra_solver.t_to_poly_ctx t) 1 in
  Nra_solver.assert_eq t p (Polynomes.zero (Nra_solver.t_to_poly_ctx t));
  let ans = Nra_solver.solve t in
  let s = Nra_solver.show_sat_or_unsat t ans in
  Format.printf "mon_test3: %s @." s*)
(*
let c5 =
  ( Polynomes.mk_polynomes (Array.to_list variables)
      [ (2, [ 3; 2; 0 ]); (4, [ 1; 0; 3 ]) ],
    Constraint.Less )

let s = Polynomes.Assignment.of_list [ (x, Real.of_int 0) ]*)

(*let result = Constraint.get_unsat_intervals [| c1; c2; c3 |] s
let gen_result = Gen.pure result

let petit_test =
  let print = Fmt.to_to_string Covering.pp_intervals_poly in
  Test.make ~print ~count:100 ~name:"petit test get_unsat_interval marche"
    (Gen.pure result) (fun x ->
      if Covering.intervalpoly_to_interval x = [] then true else false)*)

let test_get_unsat_intervals =
  let t = Nra_solver.create () in

  ignore (Nra_solver.create_variable t "x" : Nra_solver.variable);
  ignore (Nra_solver.create_variable t "y" : Nra_solver.variable);
  ignore (Nra_solver.create_variable t "z" : Nra_solver.variable);
  let print = Fmt.to_to_string (pp_pair t) in
  Test.make ~print ~count:100 ~name:"get_unsat_interval marche" (gen_pair t)
    (fun x ->
      let c, s = x in
      Format.printf "FOOO: %s@." (print x);
      let l = Nra_solver.get_unsat_intervals t c s in
      test_constraints t s c (Covering.intervalpoly_to_interval l))

let test_sample_point =
  let print = Fmt.to_to_string Covering.pp_intervals in
  Test.make ~print ~count:100 ~name:"sample_point marche"
    gen_intervals_list_or_coverings (fun x ->
      Format.printf "Alghum: %s@." (print x);
      test_sample_outside x)

let test_compute_good_covering =
  let print = Fmt.to_to_string Covering.pp_intervals in
  Test.make ~print ~count:100 ~name:"compute_good_covering marche" gen2
    (fun x ->
      let y = Covering.compute_good_covering x in
      let z = Covering.sort_intervals1 x in
      Format.printf "resultat d'avant: %s@." (print x);
      Format.printf "la liste trié: %s@." (print z);
      Format.printf
        "resultat compute good \
         covering=======================================================: %s@."
        (print y);
      Covering.is_good_covering y)

let gen_problem =
  Gen.(
    unit >>= fun () ->
    let t = Nra_solver.create () in
    ignore (Nra_solver.create_variable t "x" : Nra_solver.variable);
    ignore (Nra_solver.create_variable t "y" : Nra_solver.variable);
    ignore (Nra_solver.create_variable t "z" : Nra_solver.variable);
    let zero = Polynomes.zero (Nra_solver.t_to_poly_ctx t) in
    let cs = generate1 (gen_array_constraints t) in
    Array.iter
      (fun (p, sigma) ->
        match sigma with
        | Nra_solver.Equal -> Nra_solver.assert_eq t p zero
        | Nra_solver.Less -> Nra_solver.assert_lt t p zero)
      cs;
    pure t)

let test_algorithme2 =
  let print = Fmt.to_to_string Nra_solver.pp in
  Test.make ~print ~count:20 ~name:"solver marche" gen_problem (fun x ->
      Format.printf "mes contraints : %a" Nra_solver.pp x;
      test_solver x)

(*let test_index_c1 =
  let print = Fmt.to_to_string Polynomes.pp in
  let p, _ = c1 in
  Test.make ~print ~count:100 ~name:"test index" (Gen.pure p) (fun x ->
      Polynomes.Var.compare (Polynomes.Var.of_index 2)
        (Polynomes.top_variable p)
      = 0)*)

(* Group all the tests together *)
let covering_suite = []

(*test_basile;*)
(*test_get_unsat_intervals*)
(*; test_sample_point ; petit_test *)
(*test_compute_good_covering*)
(*test_algorithme2    ]*)

(*
let () =
  let resultat = Constraint.get_unsat_cover [| c1; c2; c3 |] [| x; y |] in
  Constraint.sat_to_assignment resultat;
  flush_all ()*)

(*let s =
  let resultat = Constraint.get_unsat_cover [| c4; c5 |] variables in
  Format.printf "%s @." (Constraint.show_sat_or_unsat resultat)*)

(*let result_algo6 = Polynomes.required_coefficient s p 
let sortie_alg6 = Polynomes.string_of_polynomial_list (Polynomes.to_list result_algo6)
let () = Format.printf " %s le resultat de algo 6 c'est ça ::::::: @. "  sortie_alg6 *)

(*let coeffs = Polynomes.string_of_polynomial_list (Polynomes.to_list (Polynomes.required_coefficient (Polynomes.Assignment.of_list  [(x ,Real.of_int 0)  ]) (fst c4)))
let s = Format.printf "les coefficients alogo 6 result : %s @." coeffs *)

(*let test_is_polu_nul (p : Constraint.contraint) s = 
 if (Constraint.is_poly_nul p s)  then "True " else "false" 

let str = (test_is_polu_nul c4 (Polynomes.Assignment.of_list  [(x ,Real.of_int 0) ; (y , Real.of_int 0) ]) )
let str = Format.printf "la branche speciale  : %s @." str 



  let a =
  let resultat = Constraint.get_unsat_intervals [|c4|] (Polynomes.Assignment.of_list  [(x ,Real.of_int 0) ; (y , Real.of_int 0) ]) in
  Covering.show_intervals_poly resultat 

let str = Format.printf "l'algorithme 3 me donne  : %s @." a *)
(*
let regions0 = Covering.pointsToIntervals  [| |]
let regions1 = Covering.pointsToIntervals [| Real.of_int 0 ; Real.of_int 1|]

let str0 = Covering.show_intervals regions0 
let str1 = Covering.show_intervals regions1 
let () = Format.printf " %s le resultat de l'ensembles vide de points  @." str0 
let () = Format.printf " %s le resultat de l'ensembles non vide de points  @." str1 *)

(* --- Run Tests --- *)
(* This line registers the suite to be run by the dune runner *)
let () = QCheck_base_runner.run_tests_main covering_suite
