open QCheck2
module Covering = Nra_solver.Covering
module Real = Nra_solver.Real 
let is_covering = Covering.is_covering


let gen_real : Real.t  Gen.t  =
Gen.map Real.of_int (Gen.int_range 0 100)

let gen_bound : Covering.bound  Gen.t =
  Gen.oneof [
    (* Générer un Real.t aléatoire et l'envelopper dans Finite *)
    Gen.map (fun n -> Covering.Finite n) gen_real;
    Gen.pure Covering.Pinf;
    Gen.pure Covering.Ninf;
  ]
let gen_exact : Covering.interval Gen.t = 
  Gen.map (fun n -> Covering.Exact n) gen_real

let gen_interval : Covering.interval Gen.t =
  Gen.oneof [
    Gen.map (fun n -> Covering.Exact n) gen_real;
    Gen.bind (Gen.pair gen_bound gen_bound) (fun (b1, b2) ->
      if Covering.compare_bound b1 b2 < 0 then
        Gen.pure (Covering.Open (b1, b2))
      else
        Gen.map (fun n -> Covering.Exact n) gen_real
    ); 

    
  ]
let is_good_covering = Covering.is_good_covering
   

let compute_good_covering  = Covering.compute_good_covering

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
    | Covering.Open (b1, b2) -> Format.fprintf ppf "(%a, %a)" pp_bound b1 pp_bound b2
    | Exact b -> Format.fprintf ppf "{%a}" Real.pp b
  

let pp_intervals ppf l =
  let pp_sep ppf () = Format.fprintf ppf "∪" in
  Format.pp_print_list ~pp_sep pp_interval ppf l

let gen_sorted_list (n : int) : Real.t list Gen.t =
  Gen.bind (Gen.list_size (Gen.pure n) gen_real)
    (fun l -> Gen.pure (List.sort_uniq Real.compare  l))


let build_intervals l =
  let rec loop acc l =
    match l with
    | a :: c :: b :: d :: l ->
      loop (Covering.Open (Finite c, Finite d) :: Covering.Open (Finite a, Finite b) :: acc)
        (b :: d :: l)
    | e :: _ :: _ ->  (Covering.Open (Finite e, Pinf) :: acc )
    |_ ->  assert false
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
    Test.make
      ~print:print_covering
      ~count:1000
      ~name:__FUNCTION__
       (gen_good_covering 3)
         
      is_good_covering 

let test_compute_good_covering_identity =
  Test.make 
    ~print: print_covering
    ~count: 1000
    ~name: "compute_good_covering_identity"
     (gen_good_covering 10 ) (fun c -> 
      let d = compute_good_covering c in
      List.equal Covering.equal_interval c d
      )
      

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
let covering_suite = [ test_is_good_covering; test_compute_good_covering_identity (* test_compute_good_is_valid; test_compute_good_is_good *) ]

(* --- Run Tests --- *)
(* This line registers the suite to be run by the dune runner *)
let () = QCheck_base_runner.run_tests_main covering_suite 

