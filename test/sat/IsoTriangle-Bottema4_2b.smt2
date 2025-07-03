(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema4.2b:
 Comparison of Area and Perimeter via RealGeom, Bottema 4.2 (isoceles triangle, ver. b):Let A, B be arbitrary points. Let c be the segment A, B. Let g be the perpendicular bisector of c. Let C be a point on g. Let b be the segment C, A. Let D be the intersection of g and c. Let h_c be the segment D, C. Compare (2b + c)^2 and c h_c / 2.

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
(assert (and (< 0 m) (< 0 v15) (< 0 v14) (< 0 v13) (= (- (* v10 v10) (* v15 v15)) 0) (= (+ (* (* v10 v10) 4) (* (* v14 v14) (- 4) )1) 0) (= (+ (* v13 (- 1) )1) 0) (= (+ (* (* m v15) (- 1) )(* (* v14 v14) 8) (* v14 8) 2) 0)))
(check-sat)
(exit)
