(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

EulerInequality_IsoTriangle-CircumRadius_InRadius:
 Euler's Inequality: Comparison of CircumRadius and InRadius via realgeom (isosceles triangle):Let B_1, B_2 be arbitrary points. Let f be the segment B_1, B_2. Let g be the perpendicular bisector of f. Let A be a point on g. Let t1 be the polygon B_1, B_2, A. Let b_2 be the segment A, B_1. Let d be the circle through B_2 with center B_1. Let D be the intersection point of d, b_2. Let E be the midpoint of D, B_2. Let h be the line B_1, E. Let F be the intersection of g and h. Let H be the intersection of g and f. Let r be the segment F, H. Let i be the perpendicular bisector of B_1A. Let I be the intersection of g and i. Let R be the segment I, A. Compare segment I, A and segment F, H.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v16 () Real)
(declare-fun v21 () Real)
(declare-fun v24 () Real)
(declare-fun v26 () Real)
(declare-fun v27 () Real)
(assert (and (< 0 m) (< 0 v26) (< 0 v27) (= (+ (* (* v21 v21) 4) (* (* v21 v24) 4) (* v21 (- 2) )(* v24 (- 1))) 0) (= (+ (* (* v21 v21) 16) (* (* v21 v24) 16) (* (* v24 v24) 4) (* (* v26 v26) (- 4) )(* v21 (- 8) )(* v24 (- 4) )1) 0) (= (- (* v16 v16) (* v27 v27)) 0) (= (+ (* (* v13 v21) (- 8) )(* v13 2) (* v14 (- 2) )(* v21 4) (- 1) )0) (= (- (* (* v13 v16) 2) v14) 0) (= (+ (* (* v13 v13) (- 4) )(* (* v14 v14) (- 4) )(* v13 4)) 0) (= (+ (* (* m v27) (- 1) )v26) 0)))
(check-sat)
(exit)
