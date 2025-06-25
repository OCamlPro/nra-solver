(set-logic QF_NRA)
(set-option :produce-models true)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real) ; New variable declared
; -6x^2 z^2 + 10 x y^2 z + 10 x y = 0
(assert
  (=
    (+
      (* (- 6) (* x x) (* z z))  ; -6x^2 z^2
      (* 10 x (* y y) z)      ; 10xy^2 z
      (* 10 x y)              ; 10xy
    )
    0
  )
)

; 2x^3 y^2 + 4x z^3 < 0
(assert
  (<
    (+
      (* 2 (* x x x) (* y y)) ; 2x^3 y^2
      (* 4 x (* z z z))       ; 4x z^3
    )
    0
  )
)
(check-sat)
(get-model)
