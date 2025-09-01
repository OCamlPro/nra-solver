(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

Triangle-Area_Perimeter_a:
 Comparision of Perimeter and Area via realgeom (generic triangle, ver. a):Let A, B, C be arbitrary points. Let c be the segment A, B. Let a be the segment B, C. Let b be the segment C, A. Let i be the line through C perpendicular to c. Let D be the intersection of i and c. Let h_c be the segment C, D. Compare (a + b + c)^2 and c h_c / 2.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v14) (< 0 v12) (< 0 v11) (< 0 v13) (= (+ (* (* v11 v11) (- 1) )(* v8 v8) (* v9 v9) (* v8 (- 2) )(* v9 (- 2) )2) 0) (= (+ (* (* v14 v14) (- 1) )(* v8 v8) (* v8 (- 2) )1) 0) (= (+ (* (* v12 v12) (- 1) )(* v8 v8) (* v9 v9) (* v8 (- 2) )1) 0) (= (+ (* v8 v15) (* v15 (- 1) )(- 1) )0) (= (+ (* v13 (- 1) )1) 0) (= (+ (* (* m v14) (- 1) )(* (* v11 v11) 2) (* (* v11 v12) 4) (* (* v12 v12) 2) (* v11 4) (* v12 4) 2) 0)))
(check-sat)
(exit)
