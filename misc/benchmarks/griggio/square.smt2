(set-logic QF_FPABV)
(declare-fun x () (_ FP 11 53))
(declare-fun y () (_ FP 11 53))
(declare-fun z () (_ FP 11 53))
(define-fun .11 () (_ FP 11 53) z)
(define-fun .12 () (_ FP 11 53) y)
(define-fun .13 () Bool (== .11 .12))
(assert .13)
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .14 () (_ FP 11 53) x)
(define-fun .15 () (_ FP 11 53) (* .3 .11 .12))
(define-fun .16 () Bool (== .14 .15))
(assert .16)
(define-fun .10 () (_ FP 11 53) ((_ asFloat 11 53) roundTowardZero 0.0))
(define-fun .17 () Bool (< .14 .10))
(assert .17)
(check-sat)
