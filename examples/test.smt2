;(or (and (= (* x z) (+ y z)) (and (> x (+ z 1.0)) (< (+ x y) (- y z)))) (= (double z) (double y)))
(declare-fun x () (_ FP 8 24))
(declare-fun y () (_ FP 8 24))
(declare-fun z () (_ FP 8 24))

(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun x_star_z () (_ FP 8 24) (* .3 x z))
(define-fun y_plus_z () (_ FP 8 24) (+ .3 y z))
(define-fun prop1 () Bool (= x_star_z y_plus_z))
;(define-fun z () (_ FP 8 24) (+ .3 y x))

(define-fun one () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.0))
(define-fun z_plus_1 () (_ FP 8 24) (+ .3 z one))
(define-fun prop2 () Bool (> x z_plus_1))

(define-fun x_plus_y () (_ FP 8 24) (+ .3 x y))
(define-fun y_minus_z () (_ FP 8 24) (- .3 y z))
(define-fun prop3 () Bool (< x_plus_y y_minus_z))

(define-fun propexp1 () Bool (and prop2 prop3))
(define-fun propexp2 () Bool (and prop1 propexp1))

(define-fun y_upcasted () (_ FP 11 53) ((_ asFloat 11 53) .3 y))
(define-fun z_upcasted () (_ FP 11 53) ((_ asFloat 11 53) .3 z))
(define-fun prop4 () Bool (= z_upcasted y_upcasted))

(define-fun result () Bool (or propexp2 prop4))
(assert result)
(check-sat)
;(get-model)

;(declare-fun b13 () (_ FP 11 53))
;(set-logic QF_FPABV)
;(declare-fun b8 () (_ FP 8 24))
;(declare-fun b20 () (_ FP 8 24))
;(declare-fun b23 () (_ FP 8 24))
;(declare-fun b13 () (_ FP 11 53))
;(define-fun .3 () RoundingMode roundNearestTiesToEven)
;(define-fun .9 () (_ FP 8 24) b8)
;(define-fun .10 () (_ FP 8 24) b20)
;(define-fun .11 () Bool (<= .9 .10))
;(define-fun .12 () (_ FP 8 24) (* .3 .9 .9))
;(define-fun .13 () (_ FP 8 24) (+ .3 .9 .12))
;(define-fun .14 () (_ FP 11 53) ((_ asFloat 11 53) .3 .13))
;(define-fun .15 () (_ FP 11 53) b13)
;(define-fun .16 () Bool (< .14 .15))
;(define-fun .17 () Bool (and .11 .16))
;(define-fun .18 () (_ FP 8 24) b23)
;(define-fun .19 () Bool (<= .18 .9))
;(define-fun .20 () Bool (and .17 .19))
;(assert .20)
;(check-sat)