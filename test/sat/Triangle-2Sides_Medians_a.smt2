(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

Triangle-2Sides_Medians_a:
 Comparision of Medians and 2 Sides via realgeom (ver. a):Let A, B, C be arbitrary points. Let t1 be the polygon A, B, C. Let c be the segment A, B. Let a be the segment B, C. Let b be the segment C, A. Let D be the midpoint of c. Let E be the midpoint of b. Let F be the midpoint of a. Let m_a be the segment A, F. Let m_b be the segment B, E. Let m_c be the segment C, D. Compare b + c and m_a + m_b + m_c.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status unknown)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v13 () Real)
(declare-fun v14 () Real)
(declare-fun v15 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v6 () Real)
(declare-fun v9 () Real)
(assert (and (< 0 m) (< 0 v17) (< 0 v16) (< 0 v15) (< 0 v13) (< 0 v14) (= (+ (* (* v16 v16) (- 4) )(* v6 v6) (* (* v9 v9) 4) (* v9 (- 8) )4) 0) (= (+ (* (* v17 v17) (- 4) )(* (* v6 v6) 4) (* (* v9 v9) 16) (* v9 (- 8) )1) 0) (= (+ (* (* v13 v13) (- 1) )(* v6 v6) (* (* v9 v9) 4)) 0) (= (+ (* v18 v6) (- 1) )0) (= (+ (* (* v15 v15) (- 4) )(* v6 v6) (* (* v9 v9) 4) (* v9 4) 1) 0) (= (+ (* v14 (- 1) )1) 0) (= (+ (* (* m v15) (- 1) )(* (* m v16) (- 1) )(* (* m v17) (- 1) )v13 1) 0)))
(check-sat)
(exit)
