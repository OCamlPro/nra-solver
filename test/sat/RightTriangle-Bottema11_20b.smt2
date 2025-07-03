(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema11.20b:
 Comparison of Expressions Related to Triangle Sides via realgeom, Bottema 11.20 (right triangle, ver. b):Let C, B be arbitrary points. Let a be the segment C, B. Let f be the line through C perpendicular to a. Let A be a point on f. Let c be the segment A, B. Let b be the segment C, A. Compare a + b and segment A, B.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v11) (< 0 v9) (< 0 v10) (= (+ (* v8 v8) (* (* v9 v9) (- 1) )1) 0) (= (+ (* (* v11 v11) (- 1) )(* v8 v8)) 0) (= (+ v11 (* w1 (- 1) )1) 0) (= (+ (* (* m v9) (- 1) )w1) 0) (= (+ (* v10 (- 1) )1) 0)))
(check-sat)
(exit)
