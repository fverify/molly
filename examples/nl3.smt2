(declare-const x Real)
(declare-const y Real)
(assert (= (+ (* x x) (* y y)) 15.75))
(check-sat)
(get-model)
