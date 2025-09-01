(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema1.19a:
 Comparison of Expressions Related to Triangle Sides via realgeom, Bottema 1.19 (right triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let M be the midpoint of c. Let d be the circle through B with center M. Let C be a point on d. Let b be the segment A, C. Let a be the segment C, B. Compare a^2 + b^2 + c^2 and (a + b + c)^2.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v9) (< 0 v10) (< 0 v11) (= (+ (* (* v7 v7) (- 1) )(* (* v8 v8) (- 1) )v7) 0) (= (+ (* v7 v7) (* v8 v8) (* (* v9 v9) (- 1) )(* v7 (- 2) )1) 0) (= (+ (* (* v10 v10) (- 1) )(* v7 v7) (* v8 v8)) 0) (= (+ (* v11 (- 1) )1) 0) (= (+ (* (* m (* v10 v10)) (- 1) )(* (* m v10 v9) (- 2) )(* (* m (* v9 v9)) (- 1) )(* (* m v10) (- 2) )(* (* m v9) (- 2) )(* v10 v10) (* v9 v9) (* m (- 1) )1) 0)))
(check-sat)
(exit)
