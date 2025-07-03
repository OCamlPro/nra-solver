(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoRightTriangle-Bottema5.3b:
 Comparison of Expressions Related to Triangle Sides via realgeom, Bottema 5.3 (isosceles right triangle, ver. b):Let A, B be arbitrary points. Let c be the segment A, B. Let M be the midpoint of c. Let d be the circle through B with center M. Let f be the line through M perpendicular to c. Let C be the intersection point of d, f. Let a be the segment C, B. Let b be the segment A, C. Let R be the segment M, B. Compare a + b + c and segment M, B.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v11) (< 0 v13) (< 0 v14) (< 0 v12) (= (+ (* (* v10 v10) (- 4) )1) 0) (= (+ (* (* v10 v10) 4) (* (* v14 v14) (- 4) )1) 0) (= (+ (* (* v10 v10) 4) (* (* v13 v13) (- 4) )1) 0) (= (+ v13 v14 (* w1 (- 1) )1) 0) (= (+ (* m (- 1) )(* w1 2)) 0) (= (+ (* v11 (- 2) )1) 0) (= (+ (* v12 (- 1) )1) 0)))
(check-sat)
(exit)
