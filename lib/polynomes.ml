type t = Z_poly.t array
let normalize(p : t) : t =
  let j = ref 0 in 
  let n = Array.length p in 
  for i = (n - 2) downto 0 do
     if Z_poly.equal p.(i) Z_poly.zero then j := !j + 1 
     else j := !j 
  done;  
  Array.sub p 0 (n - !j -1)

  let l_coeff (p : t ) : Z_poly.t = 
  let n = Array.length p in p.(n-1) 

  exception Break of Z_poly.t list
  let  required_coefficient ( s : Real.t array ) ( p : t )  = 
   let zpoly_list = ref [] in 
   let q = ref p in 
   try 
   while !q <> [||] do 
    let lc = l_coeff !q in 
    zpoly_list := lc :: !zpoly_list;

       if Real.compare(Z_poly.evaluate lc s)  (Real.of_int 0) <> 0  then (raise ( Break !zpoly_list)  )
       else ( q := normalize  !q)
  done; 
  !zpoly_list
   with Break l -> l 

   let pp ppf arr =
      let pp_sep ppf () = Format.fprintf ppf "; " in
      Format.fprintf ppf "[| %a" Fmt.(array ~sep:semi Z_poly.pp) arr;
      (*Format.pp_print_array ~pp_sep Z_poly.pp_polynomes ppf arr;*)
      Format.fprintf ppf " |]"  


      let mk_poly (specs : (int list * int) list) : Z_poly.t =
         Z_poly.make (List.map (fun (l, c) -> (Array.of_list l, Z.of_int c)) specs)

     let mk_poly_array poly_specs = Array.map mk_poly poly_specs

      let p = mk_poly_array
      [|
      [ ([ 2 ], -1) ;([ 0 ], 4) ]; 
      [[0] , 0] ;
      [[0] , 0] ;
      [ ([ 0 ], 4) ] ;
      [[0] , 0];
      [ ([ 2 ], -1); ([ 1 ], 2); ([ 0 ], 3) ]
      |] 
 
      
      