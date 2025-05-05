type degres =
  int list (* Une liste d'entiers représentant les degrés de chaque variable *)

type monome_multi_variable = Real.t * degres
type polynome_multi_variable = monome_multi_variable list

type comparaison =
  | SuperieurOuEgal
  | Suerieur
  | InferieurOuEgal
  | Inferieur
  | Egal

type constraints = polynome_multi_variable * comparaison

val substituer_monome :
  monome_multi_variable -> Real.t list -> monome_multi_variable option

val substituer_polynome :
  polynome_multi_variable -> Real.t list -> polynome_multi_variable

val pp_monome : Format.formatter -> monome_multi_variable -> unit
val pp_poly : Format.formatter -> polynome_multi_variable -> unit
val show_poly : polynome_multi_variable -> string
