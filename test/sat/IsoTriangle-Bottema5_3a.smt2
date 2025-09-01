(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema5.3a:
 Comparison of Circumradius and Perimeter via RealGeom, Bottema 5.3 (isosceles triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let d be the circle through B with center A. Let C be a point on d. Let a be the segment B, C. Let e be the segment A, C. Let f be the perpendicular bisector of c. Let g be the perpendicular bisector of e. Let O be the intersection of g and f. Let R be the segment A, O. Compare a + 2c and segment A, O.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun v5 () Real)
(declare-fun v6 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v17) (< 0 v19) (< 0 v18) (= (+ (* (* v16 v6) (- 2) )(* v5 v5) (* v6 v6) (* v5 (- 1))) 0) (= (+ (* (* v19 v19) (- 1) )(* v5 v5) (* v6 v6) (* v5 (- 2) )1) 0) (= (+ (* (* v5 v5) (- 1) )(* (* v6 v6) (- 1) )1) 0) (= (+ (* (* v16 v16) 4) (* (* v17 v17) (- 4) )1) 0) (= (+ v19 (* w1 (- 1) )2) 0) (= (+ (* (* m v17) (- 1) )w1) 0) (= (+ (* v18 (- 1) )1) 0)))
(check-sat)
(exit)
