(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

RightTriangle-Bottema8.1a:
 Comparison of Sum of Medians and Perimeter via realgeom, Bottema 8.1 (right triangle, ver. a):Let A, B be arbitrary points. Let c be the segment A, B. Let M_1 be the midpoint of c. Let d be the circle through B with center M_1. Let C be a point on d. Let b be the segment A, C. Let a be the segment C, B. Let m_c be the segment M_1, C. Let M_2 be the midpoint of b. Let M_3 be the midpoint of a. Let m_a be the segment A, M_3. Let m_b be the segment B, M_2. Compare m_a + m_b + m_c and a + b + c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v11 () Real)
(declare-fun v12 () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(assert (and (< 0 m) (< 0 v13) (< 0 v15) (< 0 v14) (< 0 v16) (< 0 v18) (< 0 v17) (= (+ (* (* v11 v11) (- 4) )(* (* v12 v12) (- 4) )(* v11 6) (- 2) )0) (= (+ (* (* v11 v11) 4) (* (* v12 v12) 4) (* (* v13 v13) (- 4) )(* v11 (- 12) )9) 0) (= (+ (* (* v11 v11) 16) (* (* v12 v12) 16) (* (* v14 v14) (- 4) )(* v11 (- 24) )9) 0) (= (+ (* (* v11 v11) 4) (* (* v12 v12) 4) (* (* v16 v16) (- 1) )(* v11 (- 8) )4) 0) (= (+ (* (* v11 v11) 4) (* (* v12 v12) 4) (* (* v18 v18) (- 1) )(* v11 (- 4) )1) 0) (= (+ (* v11 v11) (* v12 v12) (* (* v15 v15) (- 1))) 0) (= (+ (* v17 (- 1) )1) 0) (= (+ (* (* m v16) (- 1) )(* (* m v18) (- 1) )(* m (- 1) )v13 v14 v15) 0)))
(check-sat)
(exit)
