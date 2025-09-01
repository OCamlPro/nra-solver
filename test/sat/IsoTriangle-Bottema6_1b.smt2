(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema6.1b:
 Comparison of Sums of Heights and Perimeter via RealGeom, Bottema 6.1 (isosceles triangle, ver. b):Let A, B be arbitrary points. Let c be the segment A, B. Let g be the perpendicular bisector of c. Let C be a point on g. Let b be the segment A, C. Let D be the midpoint of A, B. Let h_c be the segment C, D. Let h be the line through B perpendicular to b. Let E be the intersection of h and b. Let h_b be the segment B, E. Compare 2h_b + h_c and 2b + c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v13 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v20 () Real)
(assert (and (< 0 m) (< 0 v18) (< 0 v17) (< 0 v20) (< 0 v19) (= (+ (* v13 v13) (* (* v17 v17) (- 1) )(* v13 (- 2) )1) 0) (= (+ (* (* v13 v16) (- 2) )v15 (* v16 2) (- 1) )0) (= (+ (* v15 v15) (* v16 v16) (* (* v18 v18) (- 1) )(* v15 (- 2) )1) 0) (= (+ (* (* v13 v15) 2) (* v15 (- 2) )v16) 0) (= (+ (* (* v13 v13) 4) (* (* v20 v20) (- 4) )(* v13 (- 8) )5) 0) (= (+ (* v19 (- 1) )1) 0) (= (+ (* (* m v20) (- 2) )(* m (- 1) )v17 (* v18 2)) 0)))
(check-sat)
(exit)
