type bound = Finite of Real.t | Pinf | Ninf

let compare_bound (b : bound) (b' : bound) : int =
  match (b, b') with
  | Finite t1, Finite t2 -> Real.compare t1 t2
  | Pinf, Pinf | Ninf, Ninf -> 0
  | Pinf, _ | _, Ninf -> 1
  | _, Pinf | Ninf, _ -> -1

type interval = Open of bound * bound | Exact of Real.t

type intervalPoly = {
  interval : interval;
  u_bound : bound;
  l_bound : bound;
  u_set : Polynomes.Set.t;
  l_set : Polynomes.Set.t;
  p_set : Polynomes.Set.t;
  p_orthogonal_set : Polynomes.Set.t;
}

let interval_to_intervalPoly (i : interval) (q : Polynomes.t) =
  match i with
  | Open (Ninf, Pinf) ->
      {
        interval = i;
        u_bound = Pinf;
        l_bound = Ninf;
        u_set = Polynomes.Set.empty;
        l_set = Polynomes.Set.empty;
        p_set = Polynomes.Set.singleton q;
        p_orthogonal_set = Polynomes.Set.empty;
      }
  | Open (Ninf, Finite a) ->
      {
        interval = i;
        u_bound = Finite a;
        l_bound = Ninf;
        u_set = Polynomes.Set.singleton q;
        l_set = Polynomes.Set.empty;
        p_set = Polynomes.Set.singleton q;
        p_orthogonal_set = Polynomes.Set.empty;
      }
  | Open (Finite a, Pinf) ->
      {
        interval = i;
        u_bound = Pinf;
        l_bound = Finite a;
        u_set = Polynomes.Set.empty;
        l_set = Polynomes.Set.singleton q;
        p_set = Polynomes.Set.singleton q;
        p_orthogonal_set = Polynomes.Set.empty;
      }
  | Open (Finite a, Finite b) ->
      {
        interval = i;
        u_bound = Finite b;
        l_bound = Finite a;
        u_set = Polynomes.Set.singleton q;
        l_set = Polynomes.Set.singleton q;
        p_set = Polynomes.Set.singleton q;
        p_orthogonal_set = Polynomes.Set.empty;
      }
  | Exact a ->
      {
        interval = i;
        u_bound = Finite a;
        l_bound = Finite a;
        u_set = Polynomes.Set.singleton q;
        l_set = Polynomes.Set.singleton q;
        p_set = Polynomes.Set.singleton q;
        p_orthogonal_set = Polynomes.Set.empty;
      }
  | _ -> assert false

let intervalpoly_to_interval (i : intervalPoly list) : interval list =
  let rec loop i acc =
    match i with [] -> acc | j :: l -> loop l (j.interval :: acc)
  in
  loop (List.rev i) []

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
  | Open (a, _), Open (c, _) -> compare_bound a c
  | Open (Ninf, _), _ -> -1
  | _, Open (Ninf, _) -> 1
  | Open (Finite a, _), Exact c -> if Real.compare a c < 0 then -1 else 1
  | Exact c, Open (Finite a, _) -> if Real.compare a c < 0 then 1 else -1
  | Open (Pinf, _), _ -> 1
  | _, Open (Pinf, _) -> -1
  | Exact a, Exact b -> Real.compare a b

let compare_inter1 (i1 : interval) (i2 : interval) : int =
  match (i1, i2) with
  | Open (a, b), Open (c, d) when compare_bound a c = 0 -> compare_bound d b
  | Open (a, _), Open (c, _) -> compare_bound a c
  | Exact a, Exact b -> Real.compare a b
  | Exact a, Open (b, c) ->
      if compare_bound b (Finite a) < 0 && compare_bound (Finite a) c < 0 then 1
      else compare_bound (Finite a) b
  | Open (b, c), Exact a ->
      if compare_bound b (Finite a) < 0 && compare_bound (Finite a) c < 0 then
        -1
      else compare_bound b (Finite a)

let sort_intervals1 (intervals : interval list) : interval list =
  List.sort compare_inter1 intervals

let is_covering l =
  let rec loop_open c l =
    (* En entrant dans cette fonction, on suppose qu'on a déjà un
         recouvrement de (-oo, c).

         On cherche l'intervalle fermé [c, c] ou un intervalle ouvert
         de la forme (a, b) avec a < c && c < b. *)
    match l with
    | Exact b :: l when Real.compare b c = 0 ->
        (* On a recouvert (-oo, c]. *)
        loop_close b l
    | Open (a, Pinf) :: _ when compare_bound a (Finite c) < 0 ->
        (* On a recouvert (-oo, +oo). *)
        true
    | Open (a, Finite b) :: l
      when compare_bound a (Finite c) < 0 && Real.compare c b < 0 ->
        (* On a recouvert (-oo, b). *)
        loop_open b l
    | Open (_, Finite b) :: l when Real.compare b c <= 0 ->
        (* Cet intervalle ouvert est redondant, on l'ignore. *)
        loop_open c l
    | Exact b :: l when Real.compare b c < 0 ->
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
    | Open (a, Finite b) :: l
      when compare_bound a (Finite c) <= 0 && Real.compare c b < 0 ->
        (* On a recouvert (-oo, b). *)
        loop_open b l
    | Open (_, b) :: l when compare_bound b (Finite c) <= 0 ->
        (* Cet intervalle ouvert est redondant, on l'ignore. *)
        loop_close c l
    | Exact b :: l when Real.compare b c <= 0 ->
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
    | Exact b :: l when Real.compare b c = 0 -> loop_close b l
    | Exact b :: l when Real.compare b c < 0 -> loop_open c l
    | Exact b :: _ -> Some (Real.div (Real.add b c) (Real.of_int 2))
    | Open (a, _) :: _ when compare_bound (Finite c) a <= 0 ->
        Some (sample_interval (Finite c) a)
    | Open (_, Finite b) :: l -> loop_open (Real.max c b) l
    | Open (_, Pinf) :: _ -> None
    | [] -> Some (Real.add c (Real.of_int 1))
    | _ -> assert false
  and loop_close c l =
    match l with
    | Exact b :: l when Real.compare b c <= 0 -> loop_close b l
    | Exact b :: _ -> Some (Real.div (Real.add b c) (Real.of_int 2))
    | Open (a, _) :: _ when compare_bound (Finite c) a < 0 ->
        Some (sample_interval (Finite c) a)
    | Open (_, Finite b) :: l when Real.compare b c <= 0 -> loop_close c l
    | Open (_, Finite b) :: l when Real.compare b c > 0 -> loop_open b l
    | Open (_, Pinf) :: _ -> None
    | [] -> Some (Real.add c (Real.of_int 1))
    | _ -> assert false
  in
  let l = List.sort compare_inter l in
  match l with
  | Open (Ninf, Pinf) :: _ -> None
  | Open (Ninf, Finite c) :: _ -> loop_open c l
  | (Open (Finite a, _) | Exact a) :: _ -> Some (Real.add a (Real.of_int (-1)))
  | [] -> Some (Real.of_int 0)
  | _ -> assert false

(*let compute_good_covering (u : interval list) : interval list =
          let sorted_intervals = sort_intervals1 u in
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
          List.rev !result *)

let compute_good_covering (u : interval list) : interval list =
  let sorted_intervals = sort_intervals1 u in
  let n = List.length sorted_intervals in
  let to_keep = Array.make n true in

  for i = 0 to n - 1 do
    if to_keep.(i) then
      let current_interval = List.nth sorted_intervals i in
      for j = i + 1 to n - 1 do
        if to_keep.(j) then
          let next_interval = List.nth sorted_intervals j in
          match (current_interval, next_interval) with
          | Open (_, b1), Open (_, b2) ->
              if compare_bound b2 b1 <= 0 then to_keep.(j) <- false
          | Open (a1, b1), Exact a2 ->
              if
                compare_bound (Finite a2) b1 < 0
                && compare_bound a1 (Finite a2) < 0
              then to_keep.(j) <- false
          | Exact a1, Exact a2 ->
              if Real.compare a1 a2 = 0 then to_keep.(j) <- false
          | Exact _, Open (_, _) -> ()
      done
  done;

  (* Collect the intervals that were marked to be kept *)
  let result = ref [] in
  for i = 0 to n - 1 do
    if to_keep.(i) then result := List.nth sorted_intervals i :: !result
  done;
  List.rev !result

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

let pp_debug_bound ppf b =
  match b with
  | Finite b -> Format.fprintf ppf "Finite (Real.of_int (%a))" Real.pp b
  | Pinf -> Format.fprintf ppf "Pinf"
  | Ninf -> Format.fprintf ppf "Ninf"

let pp_debug_interval ppf i =
  match i with
  | Open (b1, b2) ->
      Format.fprintf ppf "Open (%a, %a)" pp_debug_bound b1 pp_debug_bound b2
  | Exact b -> Format.fprintf ppf "Exact (Real.of_int (%a))" Real.pp b

let pp_debug_intervals = Fmt.(brackets @@ list ~sep:semi pp_debug_interval)
let show_intervals = Fmt.to_to_string @@ pp_intervals
let string_of_bound = Fmt.to_to_string @@ pp_bound

let pp_interval_poly ppf
    { interval; u_bound; l_bound; u_set; l_set; p_set; p_orthogonal_set } =
  Fmt.pf ppf
    "{ interval: %a;\n\
    \  u_bound: %a;\n\
    \  l_bound: %a;\n\
    \  u_set: %a;\n\
    \  l_set: %a;\n\
    \  p_set: %a;\n\
    \  p_orthogonal_set: %a }"
    pp_interval interval pp_bound u_bound pp_bound l_bound
    Fmt.(iter Polynomes.Set.iter Polynomes.pp)
    u_set
    Fmt.(iter Polynomes.Set.iter Polynomes.pp)
    l_set
    Fmt.(iter Polynomes.Set.iter Polynomes.pp)
    p_set
    Fmt.(iter Polynomes.Set.iter Polynomes.pp)
    p_orthogonal_set

let pp_intervals_poly = Fmt.(brackets @@ list ~sep:semi pp_interval_poly)
let show_intervals_poly = Fmt.to_to_string @@ pp_intervals_poly

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

let val_pick (i : interval) : Real.t =
  match i with Open (l, u) -> sample_interval l u | Exact a -> a

(* (-linf, 7), (3 , 5 ), (4, 6)*)
(*

let compute_good_covering (u : interval list) : interval list =
  let l' = ref (sort_intervals1 u) in
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
  with Exit -> !l' *)

let compute_cover (u : intervalPoly list) : intervalPoly list =
  let l = intervalpoly_to_interval u in
  let l_good = compute_good_covering l in
  let l = List.filter (fun i -> List.mem i.interval l_good) u in
  List.sort
    (fun { interval = i1; _ } { interval = i2; _ } -> compare_inter1 i1 i2)
    l

let length (i : interval) =
  match i with
  | Open (Finite a, Finite b) -> Real.sub b a
  | Exact _ -> Real.Syntax.(~$0)
  | _ -> invalid_arg "infinity length"

let max_bound (a : bound) (b : bound) : bound =
  if compare_bound a b <= 0 then b else a

let min_bound (a : bound) (b : bound) : bound =
  if compare_bound a b <= 0 then a else b

let disjoint (i1 : interval) (i2 : interval) : bool =
  match (i1, i2) with
  | Open (a, b), Open (c, d) -> compare_bound c b >= 0 || compare_bound a d >= 0
  | Open (a, b), Exact c | Exact c, Open (a, b) ->
      compare_bound (Finite c) a <= 0 || compare_bound b (Finite c) <= 0
  | Exact a, Exact b -> Real.compare a b <> 0

let inter (i1 : interval) (i2 : interval) : interval option =
  if disjoint i1 i2 then None
  else
    match (i1, i2) with
    | Open (a, b), Open (c, d) -> Some (Open (max_bound a c, min_bound b d))
    | Exact a, Open (_, _) | Open (_, _), Exact a -> Some (Exact a)
    | Exact a, Exact _ -> Some (Exact a)

let pointsToIntervals (arr : Real.t array) : interval list =
  let n = Array.length arr in
  if n = 0 then [ Open (Ninf, Pinf) ]
  else
    let l' = ref [ Open (Ninf, Finite arr.(0)); Exact arr.(0) ] in
    for i = 1 to n - 1 do
      l' := Exact arr.(i) :: Open (Finite arr.(i - 1), Finite arr.(i)) :: !l'
    done;
    l' := Open (Finite arr.(n - 1), Pinf) :: !l';
    List.rev !l'

let pointsToIntervals2 l =
  let rec list_interval l' =
    match l' with
    | [] -> []
    | [ c ] -> [ Open (Finite c, Pinf) ]
    | a :: b :: l1 ->
        Open (Finite a, Finite b) :: Exact b :: list_interval (b :: l1)
  in
  let l2 = list_interval l in
  match l2 with
  | Open (Finite a, Finite b) :: l ->
      Open (Ninf, Finite a) :: Exact a :: Open (Finite a, Finite b) :: l
  | [] -> []
  | _ -> assert false
