(declare-const x Real)
(declare-const y Real)
(assert (= (+ (+ (* (* (* x x) x) x) (* (* (* x x) x) y)) (* (* y y) x)) 29.0))
(check-sat)
(get-model)
