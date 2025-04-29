open QCheck2
module Covering = Nra_solver.Covering
module Real = Nra_solver.Real

let is_covering = Covering.is_covering
let open_ x y = Covering.Open (Finite (Real.of_int x), Finite (Real.of_int y))
let exact x = Covering.Exact (Real.of_int x)
let finite x = Covering.Finite (Real.of_int x)
let floor x = Z.to_int @@ Real.floor x
let ceil x = Z.to_int @@ Real.ceil x
let gen_real : Real.t Gen.t = Gen.map Real.of_int (Gen.int_range 0 100)
let three = Real.of_int 3



let to_int b =
  match b with 
  | Covering.Finite b -> if floor b <= 500 && floor b >= (-500) then floor b else if ceil b > 500 then 500 else -500
  | Covering.Pinf -> 500 
  | Covering.Ninf ->  -500  

let longueur_interval a b : bool =
  match (a, b) with
  | Covering.Finite a_val, Covering.Finite b_val ->
      Real.compare (Real.sub b_val a_val) three >= 0
  | _ -> true


  let longueur_interval' a b : bool =
    if (to_int a + 1) - (to_int b -1 ) > 1 then true else false 

    let gen_real_bound' (low : Covering.bound) (high : Covering.bound) :
      Covering.bound option Gen.t =
  if longueur_interval' low high then
    Gen.map (fun i -> Some (finite i)) (Gen.int_range (to_int low) (to_int high))
  else
    Gen.pure None

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
let gen_good_interval_tree' : interval_tree' Gen.t =
  Gen.(
    sized (fun fuel ->
        fix
          (fun self' (fuel, low, high) ->
            match fuel with
            | 0 ->
                if longueur_interval low high then
                  bind (gen_real_bound low high) @@ fun b ->
                  if longueur_interval b high then
                    bind (gen_real_bound b high) @@ fun c ->
                    pure (node2 (leaff_open low c) (leaff_open b high))
                  else Gen.pure @@ Leaff (Open (low, high))
                else Gen.pure @@ Leaff (Open (low, high))
            | n ->
                if longueur_interval low high then
                  bind (gen_real_bound low high) @@ fun b ->
                  match b with
                  | Covering.Finite b_val ->
                      map3 node3
                        (self' (n / 2, low, b))
                        (pure @@ Covering.Exact b_val)
                        (self' (n / 2, b, high))
                  | _ -> assert false
                else Gen.pure @@ Leaff (Open (low, high)))
          (fuel, Covering.Ninf, Covering.Pinf)))   
(**************************************************************************************************)
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
let gen_interval_tree' : interval_tree' Gen.t =
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
                      if longueur_interval low high then
                        bind (gen_real_bound low high) @@ fun b ->
                        if longueur_interval b high then
                          bind (gen_real_bound b high) @@ fun c ->
                          map2 node2
                            (self' (n / 2, low, c))
                            (self' (n / 2, b, high))
                        else Gen.pure @@ Leaff (Covering.Open (low, high))
                      else Gen.pure @@ Leaff (Open (low, high)) );
                    ( 2,
                      if longueur_interval low high then
                        bind (gen_real_bound low high) @@ fun b ->
                        match b with
                        | Covering.Finite b_val ->
                            map3 node3
                              (self' (n / 2, low, b))
                              (pure @@ Covering.Exact b_val)
                              (self' (n / 2, b, high))
                        | _ -> assert false
                      else Gen.pure @@ Leaff (Open (low, high)) );
                  ])
          (fuel, Covering.Ninf, Covering.Pinf)))

(************************************************************************************)


let gen_interval_tree'' : interval_tree' Gen.t =
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
                      if longueur_interval' low high then
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
                      else Gen.pure @@ Leaff (Open (low, high)) );
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

(***************************************************************************************************)
let rec fringe_tree (t : interval_tree') : Covering.interval list =
  match t with
  | Leaff x -> [ x ]
  | Node2 (t1, t2) -> fringe_tree t1 @ fringe_tree t2
  | Node3 (t1, y, t2) -> fringe_tree t1 @ [ y ] @ fringe_tree t2

let gen_good_covering2 : Covering.interval list Gen.t =
  Gen.bind gen_good_interval_tree'' (fun t -> Gen.pure (fringe_tree t))

let gen_coverings : Covering.interval list Gen.t =
  Gen.bind gen_interval_tree'' (fun t -> Gen.pure (fringe_tree t))

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
  Test.make ~print:print_covering ~count:1000
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
    test_compute_good_covering
    (*test_compute_good_is_valid; test_compute_good_is_good *)
  ]

(* --- Run Tests --- *)
(* This line registers the suite to be run by the dune runner *)
let () = QCheck_base_runner.run_tests_main covering_suite
