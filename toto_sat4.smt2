(set-option :produce-models true)
(set-logic QF_NRA)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun x () Real)
(assert
(and
  (= (+ (* 2 x) (- 1)) 0)
  (= (* z z) 1)
  (= (+ (* x x) (* y y)) (* z z))))
(check-sat)
(get-model)