(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Area_Perimeter_a:
 Comparison of Area and Perimeter via RealGeom (isoceles triangle, ver. a):Let B_1, B_2 be arbitrary points. Let a be the segment B_1, B_2. Let g be the perpendicular bisector of a. Let A be a point on g. Let b be the segment A, B_1. Let D be the intersection of g and a. Let h_a be the segment D, A. Compare (a + 2b)^2 and a h_a / 2.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(assert (and (< 0 m) (< 0 v15) (< 0 v13) (< 0 v14) (= (- (* v10 v10) (* v15 v15)) 0) (= (+ (* (* v10 v10) 4) (* (* v13 v13) (- 4) )1) 0) (= (+ (* v14 (- 1) )1) 0) (= (+ (* (* m v15) (- 1) )(* (* v13 v13) 8) (* v13 8) 2) 0)))
(check-sat)
(exit)
