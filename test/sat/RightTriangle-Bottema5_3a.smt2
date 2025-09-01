(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema5.3a:
 Comparison of Circumradius and Perimeter via realgeom, Bottema 5.3 (right triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let O be the midpoint of c. Let d be the circle through B with center O. Let C be a point on d. Let b be the segment A, C. Let a be the segment C, B. Let R be the segment O, C. Compare a + b + c and segment O, C.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(declare-fun v9 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v9) (< 0 v10) (< 0 v12) (< 0 v11) (= (+ (* (* v7 v7) (- 1) )(* (* v8 v8) (- 1) )v7) 0) (= (+ (* (* v7 v7) 4) (* (* v8 v8) 4) (* (* v9 v9) (- 4) )(* v7 (- 4) )1) 0) (= (+ (* (* v10 v10) (- 1) )(* v7 v7) (* v8 v8) (* v7 (- 2) )1) 0) (= (+ (* (* v12 v12) (- 1) )(* v7 v7) (* v8 v8)) 0) (= (+ v10 v12 (* w1 (- 1) )1) 0) (= (+ (* (* m v9) (- 1) )w1) 0) (= (+ (* v11 (- 1) )1) 0)))
(check-sat)
(exit)
