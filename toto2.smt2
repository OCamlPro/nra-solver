(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :status unsat)
(declare-const y Real)
(declare-const x Real)
(assert (and

 (> x 0) 
 (> y 0)
 (= (+ x y) 0)))

(check-sat)
(exit)
