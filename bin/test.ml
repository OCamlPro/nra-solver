open Nra_solver

let main () =
  let two = Real.of_int 2 in
  Fmt.pr "%a@." Real.pp two;
  ()

let () = main ()