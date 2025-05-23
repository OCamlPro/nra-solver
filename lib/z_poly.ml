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

  let pp = Fmt.(brackets @@ array ~sep:comma int)
end

module M = struct
  include Map.Make (Index)

  let of_list l = of_seq @@ List.to_seq l
  let to_list t = List.of_seq @@ to_seq t
end
type t = Z.t M.t

let zero = M.empty

let make l =
  let l = List.filter (fun (i, c) -> not @@ Z.equal c Z.zero) l in
  M.of_list l

let reciproque_make (l : t) = 
  M.to_list l 

(** 17x^2 y + 3y + 5 *)
let _ : t =
  M.of_list
    [
      ([| 0; 1 |], Z.of_int 3);
      ([| 2; 1 |], Z.of_int 17);
      ([| 0; 0 |], Z.of_int 5);
    ]

let pp_monomes ppf ((degres, coeff) : int array * Z.t) =
  let pp_degre ppf (degre, indice) =
    if degre = 1 then Format.fprintf ppf "v%d" (indice + 1)
    else if degre > 0 then Format.fprintf ppf "v%d^%d" (indice + 1) degre
  in
  Format.fprintf ppf "%a" Real.pp (Real.of_z coeff);
  Array.iteri
    (fun i degre ->
      if degre > 0 then Format.fprintf ppf " %a" pp_degre (degre, i))
    degres

let pp ppf (p : t) : unit =
  let monomes = M.to_list p in
  let pp_sep ppf () = Format.fprintf ppf " + " in
  Format.pp_print_list ~pp_sep pp_monomes ppf monomes

let rec mult (l : Real.t list) : Real.t =
  match l with [] -> Real.of_int 1 | x :: l -> Real.mul (mult l) x

let evaluate_monome (degres : Index.t) (coef : Z.t) (valeurs : Real.t array) :
    Real.t =
  if Array.length degres <> Array.length valeurs then
    failwith
      "La longueur de la liste des degrés doit être égale à la longueur de la \
       list de valeurs "
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

let evaluate (p : t) (l : Real.t array) : Real.t =
  M.fold
    (fun (i : Index.t) (c : Z.t) acc -> Real.add acc (evaluate_monome i c l))
    p (Real.of_int 0)

let equal = M.equal Z.equal
let is_non_nul p = 
  if equal p  zero then false else true 

