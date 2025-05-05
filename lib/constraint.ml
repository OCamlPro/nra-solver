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

type comparaison =
  | SuperieurOuEgal
  | Suerieur
  | InferieurOuEgal
  | Inferieur
  | Egal

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
  |[] -> Real.of_int 1 
  |x :: l -> 
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
      let rec construire_nouveaux_degres n =
        if n < List.length degres - 1 then
          0 :: construire_nouveaux_degres (n + 1)
        else [ List.nth degres (List.length degres - 1) ]
      in
      construire_nouveaux_degres 0 (* reccursion a l'envers if length *)
    in
    if Real.compare (new_coeff) (Real.of_int 0) = 0 then None
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

