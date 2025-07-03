(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema6.1a:
 Comparison of Sums of Heights and Perimeter via RealGeom, Bottema 6.1 (isosceles triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let d be the circle through B with center A. Let C be a point on d. Let a be the segment B, C. Let f be the line through C perpendicular to c. Let g be the line through A perpendicular to a. Let D be the intersection of c and f. Let E be the intersection of a and g. Let h_a be the segment C, D. Let h_c be the segment A, E. Compare 2h_a + h_c and a + 2c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v7 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v15) (< 0 v16) (< 0 v18) (< 0 v17) (= (+ (* v13 v9) (* v14 v7) (* v14 (- 1) )(* v9 (- 1))) 0) (= (- (* v13 v7) (* v14 v9) v13) 0) (= (+ (* (* v16 v16) (- 1) )(* v9 v9)) 0) (= (+ (* (* v18 v18) (- 1) )(* v7 v7) (* v9 v9) (* v7 (- 2) )1) 0) (= (+ (* (* v7 v7) (- 1) )(* (* v9 v9) (- 1) )1) 0) (= (+ (* v13 v13) (* v14 v14) (* (* v15 v15) (- 1))) 0) (= (+ (* v17 (- 1) )1) 0) (= (+ (* (* m v18) (- 1) )(* m (- 2) )v15 (* v16 2)) 0)))
(check-sat)
(exit)
