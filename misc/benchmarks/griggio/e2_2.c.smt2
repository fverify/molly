(set-logic QF_FPABV)
(declare-fun b20 () (_ FP 11 53))
(declare-fun b28 () (_ FP 11 53))
(declare-fun b42 () (_ FP 11 53))
(declare-fun b45 () (_ FP 11 53))
(declare-fun b23 () (_ FP 11 53))
(declare-fun b32 () (_ FP 11 53))
(declare-fun b35 () (_ FP 11 53))
(declare-fun b10 () (_ FP 11 53))
(declare-fun b22 () (_ FP 11 53))
(declare-fun b25 () (_ FP 11 53))
(declare-fun b16 () (_ FP 11 53))
(declare-fun b12 () (_ FP 11 53))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 11 53) b10)
(define-fun .10 () (_ FP 11 53) b16)
(define-fun .11 () (_ FP 11 53) (+ .3 .9 .10))
(define-fun .12 () (_ FP 11 53) b12)
(define-fun .13 () Bool (< .12 .11))
(define-fun .14 () Bool (<= .9 .12))
(define-fun .15 () Bool (and .13 .14))
(define-fun .16 () (_ FP 11 53) b20)
(define-fun .17 () (_ FP 11 53) b25)
(define-fun .18 () Bool (<= .16 .17))
(define-fun .19 () Bool (and .15 .18))
(define-fun .20 () (_ FP 11 53) b28)
(define-fun .21 () Bool (<= .20 .16))
(define-fun .22 () Bool (and .19 .21))
(define-fun .23 () (_ FP 11 53) b32)
(define-fun .24 () Bool (<= .9 .23))
(define-fun .25 () Bool (and .22 .24))
(define-fun .26 () (_ FP 11 53) b35)
(define-fun .27 () Bool (<= .26 .9))
(define-fun .28 () Bool (and .25 .27))
(define-fun .29 () (_ FP 11 53) b22)
(define-fun .30 () Bool (<= .29 .23))
(define-fun .31 () Bool (and .28 .30))
(define-fun .32 () Bool (<= .26 .29))
(define-fun .33 () Bool (and .31 .32))
(define-fun .34 () (_ FP 11 53) b23)
(define-fun .35 () (_ FP 11 53) b42)
(define-fun .36 () Bool (<= .34 .35))
(define-fun .37 () Bool (and .33 .36))
(define-fun .38 () (_ FP 11 53) b45)
(define-fun .39 () Bool (<= .38 .34))
(define-fun .40 () Bool (and .37 .39))
(assert .40)
(check-sat)