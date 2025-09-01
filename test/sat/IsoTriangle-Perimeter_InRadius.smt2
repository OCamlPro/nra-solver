(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Perimeter_InRadius:
 Comparison of Perimeter and InRadius via realgeom (isosceles triangle):Let B_1, B_2 be arbitrary points. Let f be the segment B_1, B_2. Let g be the perpendicular bisector of f. Let A be a point on g. Let t1 be the polygon B_1, B_2, A. Let a be the segment B_1, B_2. Let b_1 be the segment B_2, A. Let b_2 be the segment A, B_1. Let d be the circle through B_2 with center B_1. Let D be the intersection point of d, b_2. Let E be the midpoint of D, B_2. Let h be the line B_1, E. Let F be the intersection of g and h. Let H be the intersection of g and f. Let r be the segment F, H. Compare b_1 + b_2 + a and segment F, H.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v10 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v16 () Real)
(declare-fun v19 () Real)
(declare-fun v20 () Real)
(declare-fun v21 () Real)
(declare-fun v22 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v19) (< 0 v21) (< 0 v20) (< 0 v22) (= (- (* v16 v16) (* v19 v19)) 0) (= (+ (* (* v10 v10) 4) (* (* v20 v20) (- 4) )1) 0) (= (- (* (* v10 v13) 2) v10 v14) 0) (= (- (* (* v13 v16) 2) v14) 0) (= (+ (* (* v13 v13) (- 4) )(* (* v14 v14) (- 4) )(* v13 4)) 0) (= (+ (* (* v10 v10) 4) (* (* v21 v21) (- 4) )1) 0) (= (+ v20 v21 (* w1 (- 1) )1) 0) (= (+ (* (* m v19) (- 1) )w1) 0) (= (+ (* v22 (- 1) )1) 0)))
(check-sat)
(exit)
