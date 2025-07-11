(set-option :produce-models true)
(set-logic QF_NRA)
(declare-fun z () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun w () Real)
(assert
(and
  (= (+ (* 2 w) (- 1)) 0)
  (= x w)
  (= (* z z) 1)
  (= (+ (* x x) (* y y)) (* z z))))
(check-sat)
(get-model)
