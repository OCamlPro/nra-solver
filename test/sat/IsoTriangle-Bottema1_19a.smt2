(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema1.19a:
 Comparison of Expressions Related to Triangle Sides via RealGeom, Bottema 1.19 (isosceles triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let d be the circle through B with center A. Let C be a point on d. Let a be the segment B, C. Compare a^2 + 2c^2 and (a + 2c)^2.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v5 () Real)
(declare-fun v6 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)
(assert (and (< 0 m) (< 0 v7) (< 0 v8) (= (+ (* v5 v5) (* v6 v6) (* (* v7 v7) (- 1) )(* v5 (- 2) )1) 0) (= (+ (* (* v5 v5) (- 1) )(* (* v6 v6) (- 1) )1) 0) (= (+ (* v8 (- 1) )1) 0) (= (+ (* (* m (* v7 v7)) (- 1) )(* (* m v7) (- 4) )(* v7 v7) (* m (- 4) )2) 0)))
(check-sat)
(exit)
