(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

OposicionsSecundariaCatalunya2018-2.4b:
 Comparison of two segments in Exercise 2.4 of Oposicions Secundària Catalunya 2018 via realgeom (three regular triangles, ver. b):Let A, B be arbitrary points. Let C be the regular 3-gon with vertices A, B, C. Let D be the regular 3-gon with vertices A, C, D. Let E be the regular 3-gon with vertices A, D, E. Let F be the midpoint of A, C. Let G be the midpoint of A, B. Let p be the segment D, G. Let q be the segment E, F. Let H be the intersection of p and q. Let r be the segment H, A. Compare segment D, G and segment H, A.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v21 () Real)
(declare-fun v22 () Real)
(declare-fun v24 () Real)
(declare-fun v25 () Real)
(declare-fun v6 () Real)
(assert (and (< 0 m) (< 0 v25) (< 0 v24) (= (+ (* (* v10 v21) 2) (* (* v11 v22) (- 4) )(* (* v21 v6) 2) (* v10 (- 1) )(* v22 2) (* v6 (- 1))) 0) (= (+ (* (* v15 v22) (- 4) )(* (* v15 v6) 2) (* (* v16 v21) 4) (* (* v21 v6) (- 2) )(* v16 (- 1) )v22) 0) (= (+ (* v10 v10) (* (* v10 v6) 2) (* (* v11 v11) 4) (* (* v24 v24) (- 4) )(* v6 v6) (* v11 (- 4) )1) 0) (= (+ (* (* v6 v6) 4) (- 3) )0) (= (+ (* (* v10 v10) 4) (- 3) )0) (= (+ (* (* v10 v6) (- 4) )(* v11 (- 4) )1) 0) (= (+ (* (* v14 v14) 4) (- 3) )0) (= (+ (* (* v10 v14) (- 1) )(* (* v14 v6) (- 1) )v11 (* v15 (- 2))) 0) (= (+ (* (* v11 v14) 4) v10 (* v16 (- 4) )v6) 0) (= (+ (* v21 v21) (* v22 v22) (* (* v25 v25) (- 1))) 0) (= (+ (* (* m v25) (- 1) )v24) 0)))
(check-sat)
(exit)
