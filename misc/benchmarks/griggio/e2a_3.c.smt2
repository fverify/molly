(set-logic QF_FPABV)
(declare-fun b9 () (_ FP 11 53))
(declare-fun b43 () (_ FP 11 53))
(declare-fun b13 () (_ FP 11 53))
(declare-fun b33 () (_ FP 11 53))
(declare-fun b11 () (_ FP 11 53))
(declare-fun b40 () (_ FP 11 53))
(declare-fun b36 () (_ FP 11 53))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 11 53) b13)
(define-fun .10 () (_ FP 11 53) b9)
(define-fun .11 () (_ FP 11 53) (+ .3 .9 .10))
(define-fun .12 () (_ FP 11 53) b11)
(define-fun .13 () Bool (< .12 .11))
(define-fun .14 () Bool (<= .10 .12))
(define-fun .15 () Bool (and .13 .14))
(define-fun .16 () (_ FP 11 53) b33)
(define-fun .17 () Bool (<= .10 .16))
(define-fun .18 () Bool (and .15 .17))
(define-fun .19 () (_ FP 11 53) b36)
(define-fun .20 () Bool (<= .19 .10))
(define-fun .21 () Bool (and .18 .20))
(define-fun .22 () (_ FP 11 53) b40)
(define-fun .23 () Bool (<= .9 .22))
(define-fun .24 () Bool (and .21 .23))
(define-fun .25 () (_ FP 11 53) b43)
(define-fun .26 () Bool (<= .25 .9))
(define-fun .27 () Bool (and .24 .26))
(assert .27)
(check-sat)
