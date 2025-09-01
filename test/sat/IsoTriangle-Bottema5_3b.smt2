(set-info :smt-lib-version 2.6)
(set-info :source |The authors Robert Vajda and Zoltan Kovacs released this problem in the paper that can be found in "http://ceur-ws.org/Vol-2752/paper15.pdf". A short description of the problem can be found down below.

IsoTriangle-Bottema5.3b:
 Comparison of Perimeter and CircumRadius via realgeom, Bottema 5.3 (isosceles triangle, ver. b):Let A, B be arbitrary points. Let c be the segment A, B. Let D be the midpoint of A, B. Let g be the line through D perpendicular to c. Let C be a point on g. Let b be the segment A, C. Let E be the midpoint of A, C. Let i be the line through E perpendicular to b. Let F be the intersection of i and g. Let R be the segment A, F. Compare 2b + c and segment A, F.

This problem was added to SMT-LIB by Tereso del Rio and Matthew England.| )
(set-info :category "industrial")
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :status sat)
(set-logic QF_NRA)
(declare-fun m () Real)
(declare-fun v14 () Real)
(declare-fun v16 () Real)
(declare-fun v17 () Real)
(declare-fun v18 () Real)
(declare-fun v19 () Real)
(declare-fun w1 () Real)
(assert (and (< 0 m) (< 0 v17) (< 0 v19) (< 0 v18) (= (+ (* (* v14 v14) (- 16) )(* (* v14 v16) 16) (* v14 16) (* v16 (- 8) )(- 3) )0) (= (+ (* (* v14 v14) 16) (* (* v19 v19) (- 4) )(* v14 (- 16) )5) 0) (= (+ (* (* v16 v16) 4) (* (* v17 v17) (- 4) )1) 0) (= (+ (* v19 2) (* w1 (- 1) )1) 0) (= (+ (* (* m v17) (- 1) )w1) 0) (= (+ (* v18 (- 1) )1) 0)))
(check-sat)
(exit)
