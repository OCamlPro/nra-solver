type bound = Finite of Real.t | Pinf | Ninf

let compare_bound (b : bound) (b' : bound) : int =
  match (b, b') with
  | Finite t1, Finite t2 -> Real.compare t1 t2
  | Pinf, Pinf | Ninf, Ninf -> 0
  | Pinf, _ | _, Ninf -> 1
  | _, Pinf | Ninf, _ -> -1

type interval = Open of bound * bound | Exact of Real.t
type covering = interval list

let make_open b1 b2 =
  if compare_bound b1 b2 >= 0 then invalid_arg "make_open";
  Open (b1, b2)

let make_exact b = Exact b

let sample_interval (b1 : bound) (b2 : bound) : Real.t =
  match (b1, b2) with
  | Finite b1_val, Finite b2_val ->
      Real.div (Real.add b1_val b2_val) (Real.of_int 2)
  | Finite b1_val, Pinf -> Real.add b1_val (Real.of_int 1)
  | Ninf, Finite b2_val -> Real.add b2_val (Real.of_int (-1))
  | Ninf, Pinf -> Real.of_int 0
  | _ -> assert false

let compare_inter (i1 : interval) (i2 : interval) : int =
  match (i1, i2) with
  | Open (a, b), Open (c, d) -> compare_bound a c
  | Open (Ninf, _), _ -> -1
  | _, Open (Ninf, _) -> 1
  | Open (Finite a, b), Exact c -> if a < c then -1 else 1
  | Exact c, Open (Finite a, b) -> if a < c then 1 else -1
  | Open (Pinf, _), _ -> 1
  | _, Open (Pinf, _) -> -1
  | Exact a, Exact b -> if a < b then -1 else if a = b then 0 else -1

let compare_inter1 (i1 : interval) (i2 : interval) : int =
  match (i1, i2) with
  | Open (a, b), Open (c, d) when compare_bound a c = 0 -> compare_bound d b
  | Open (a, _), Open (c, _) -> compare_bound a c
  | Exact a, Exact b -> Real.compare a b
  | Exact a, Open (b, c) ->
      if compare_bound b (Finite a) <= 0 && compare_bound (Finite a) c <= 0 then
        1
      else compare_bound (Finite a) b
  | Open (b, c), Exact a ->
      if compare_bound b (Finite a) <= 0 && compare_bound (Finite a) c <= 0 then
        -1
      else compare_bound b (Finite a)

let sort_intervals (intervals : interval list) : interval list =
  List.sort compare_inter intervals

let sort_intervals1 (intervals : interval list) : interval list =
  List.sort compare_inter1 intervals

let one = Real.of_int 1
let mone = Real.of_int (-1)
let zero = Real.of_int 0
let five = Real.of_int 5
let eight = Real.of_int 8

let l =
  sort_intervals1
    [
      Open (Ninf, Finite one);
      Open (Finite mone, Finite zero);
      Exact eight;
      Open (Finite one, Pinf);
      Exact one;
      Exact five;
    ]

let is_covering l =
  let rec loop_open c l =
    (* En entrant dans cette fonction, on suppose qu'on a déjà un
         recouvrement de (-oo, c).
  
         On cherche l'intervalle fermé [c, c] ou un intervalle ouvert
         de la forme (a, b) avec a < c && c < b. *)
    match l with
    | Exact b :: l when b = c ->
        (* On a recouvert (-oo, c]. *)
        loop_close b l
    | Open (a, Pinf) :: _ when compare_bound a (Finite c) < 0 ->
        (* On a recouvert (-oo, +oo). *)
        true
    | Open (a, Finite b) :: l when compare_bound a (Finite c) < 0 && c < b ->
        (* On a recouvert (-oo, b). *)
        loop_open b l
    | Open (_, Finite b) :: l when b <= c ->
        (* Cet intervalle ouvert est redondant, on l'ignore. *)
        loop_open c l
    | Exact b :: l when b < c ->
        (* Cet intervalle fermé est redondant, on l'ignore. *)
        loop_open c l
    | _ -> false
  and loop_close c l =
    (* En entrant dans cette fonction, on suppose qu'on a déjà un recouvrement
         de (-oo, c].
  
         On cherche un intervalle de la forme (a, b) avec a <= c && c < b. *)
    match l with
    | Open (a, Pinf) :: _ when compare_bound a (Finite c) <= 0 ->
        (* On a recouvert (-oo, +oo). *)
        true
    | Open (a, Finite b) :: l when compare_bound a (Finite c) <= 0 && c < b ->
        (* On a recouvert (-oo, b). *)
        loop_open b l
    | Open (_, b) :: l when compare_bound b (Finite c) <= 0 ->
        (* Cet intervalle ouvert est redondant, on l'ignore. *)
        loop_close c l
    | Exact b :: l when b <= c ->
        (* Cet intervalle fermé est redondant, on l'ignore. *)
        loop_close c l
    | _ -> false
  in
  let l = List.sort compare_inter l in
  match l with
  | Open (Ninf, Pinf) :: _ -> true
  | Open (Ninf, Finite c) :: _ -> loop_open c l
  | _ -> false

let is_good_covering (l : interval list) : bool =
  let rec check_pairs lst =
    match lst with
    | [] | [ _ ] -> true
    | i1 :: i2 :: rest ->
        let condition_met =
          match (i1, i2) with
          | Open (a, _), Open (c, _) when compare_bound a c >= 0 -> false
          | Open (_, b), Open (_, d) -> compare_bound b d < 0
          | Open (_, b), Exact a | Exact a, Open (b, _) ->
              compare_bound (Finite a) b = 0
          | _ -> false
        in
        if condition_met then check_pairs (i2 :: rest) else false
  in
  check_pairs l

let sample_outside (l : interval list) : Real.t option =
  let rec loop_open c l =
    match l with
    | Exact b :: l when b = c -> loop_close b l
    | Exact b :: l when b < c -> loop_open c l
    | Exact b :: _ -> Some (Real.div (Real.add b c) (Real.of_int 2))
    | Open (a, _) :: _ when compare_bound (Finite c) a <= 0 ->
        Some (sample_interval (Finite c) a)
    | Open (_, Finite b) :: l -> loop_open (max c b) l
    | Open (_, Pinf) :: _ -> None
    | [] -> Some (Real.add c (Real.of_int 1))
    | _ -> assert false
  and loop_close c l =
    match l with
    | Exact b :: l when b <= c -> loop_close b l
    | Exact b :: _ -> Some (Real.div (Real.add b c) (Real.of_int 2))
    | Open (a, _) :: _ when compare_bound (Finite c) a < 0 ->
        Some (sample_interval (Finite c) a)
    | Open (_, Finite b) :: l when b <= c -> loop_close c l
    | Open (_, Finite b) :: l when b > c -> loop_open b l
    | Open (_, Pinf) :: _ -> None
    | [] -> Some (Real.add c (Real.of_int 1))
    | _ -> assert false
  in
  let l = List.sort compare_inter l in
  match l with
  | Open (Ninf, Pinf) :: _ -> None
  | Open (Ninf, Finite c) :: _ -> loop_open c l
  | (Open (Finite a, _) | Exact a) :: _ -> Some (Real.add a (Real.of_int (-1)))
  | _ -> assert false

(*

        let compute_good_covering (u : interval list) : interval list =
          let sorted_intervals = sort_intervals u in  
          let n = List.length sorted_intervals in
          let to_keep = Array.make n true in  
        
          for i = 0 to n - 1 do
            if to_keep.(i) then  
              let current_interval = List.nth sorted_intervals i in
              for j = i + 1 to n - 1 do
                if to_keep.(j) then
                  let next_interval = List.nth sorted_intervals j in
                  match current_interval, next_interval with
                  | Open (_, b1), Open (_, b2) ->
                    if compare_bound b2 b1 <= 0 then to_keep.(j) <- false 
                  | Open (_, b1), Exact a2 ->
                    if compare_bound (Finite a2) b1 <= 0 then to_keep.(j) <- false  
                  | Exact a1, Exact a2 ->
                    if  a2 = a1 then to_keep.(j) <- false
                  |Exact _ , Open(_,_) -> ()
              done
          done;
        
          (* Collect the intervals that were marked to be kept *)
          let result = ref [] in
          for i = 0 to n - 1 do
            if to_keep.(i) then
              result := (List.nth sorted_intervals i) :: !result
          done;
          List.rev !result   *)

(********************************************************************************)
let pp_bound ppf b =
  match b with
  | Finite b -> Format.fprintf ppf "%a" Real.pp b
  | Pinf -> Format.fprintf ppf "+oo"
  | Ninf -> Format.fprintf ppf "-oo"

let pp_interval ppf i =
  match i with
  | Open (b1, b2) -> Format.fprintf ppf "(%a, %a)" pp_bound b1 pp_bound b2
  | Exact b -> Format.fprintf ppf "{%a}" Real.pp b

let pp_intervals ppf l =
  let pp_sep ppf () = Format.fprintf ppf "∪" in
  Format.pp_print_list ~pp_sep pp_interval ppf l

let compare_interval i1 i2 =
  match (i1, i2) with
  | Open (a, b), Open (c, d) ->
      let e = compare_bound a c in
      if e <> 0 then e else compare_bound b d
  | Open _, _ -> -1
  | _, Open _ -> 1
  | Exact a, Exact b -> Real.compare a b

let equal_interval i1 i2 = compare_interval i1 i2 = 0

module S = Set.Make (struct
  type t = interval

  let compare i1 i2 =
    match (i1, i2) with
    | Open (a, b), Open (c, d) ->
        let e = compare_bound a c in
        if e <> 0 then e else compare_bound b d
    | Open _, _ -> -1
    | _, Open _ -> 1
    | Exact a, Exact b -> Real.compare a b
end)

(* (-linf, 7), (3 , 5 ), (4, 6)*)

let compute_good_covering (u : interval list) : interval list =
  let l' = ref (sort_intervals u) in
  let rec check_pairs eliminate lst =
    match lst with
    | [] | [ _ ] -> eliminate
    | i1 :: i2 :: rest -> (
        match (i1, i2) with
        | Open (_, b), Open (_, d) ->
            let eliminate =
              if compare_bound d b <= 0 then S.add i2 eliminate else eliminate
            in
            check_pairs eliminate (i2 :: rest)
        | Open (_, b), Exact a ->
            let eliminate =
              if compare_bound (Finite a) b < 0 then S.add i2 eliminate
              else eliminate
            in
            check_pairs eliminate (i2 :: rest)
        | _ -> check_pairs eliminate (i2 :: rest))
  in
  try
    while true do
      let to_eliminate = check_pairs S.empty !l' in
      if S.is_empty to_eliminate then raise Exit;
      l' := List.filter (fun i -> not (S.mem i to_eliminate)) !l'
    done;
    assert false
  with Exit -> !l'
