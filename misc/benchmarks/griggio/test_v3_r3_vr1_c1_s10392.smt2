(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(define-fun .10 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.0))
(define-fun .13 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 1.0)))
(define-fun .14 () (_ FP 8 24) x0)
(define-fun .15 () Bool (<= .13 .14))
(define-fun .16 () Bool (<= .14 .10))
(define-fun .17 () Bool (and .15 .16))
(assert .17)
(define-fun .18 () (_ FP 8 24) x1)
(define-fun .19 () Bool (<= .13 .18))
(define-fun .20 () Bool (<= .18 .10))
(define-fun .21 () Bool (and .19 .20))
(assert .21)
(define-fun .22 () (_ FP 8 24) x2)
(define-fun .23 () Bool (<= .13 .22))
(define-fun .24 () Bool (<= .22 .10))
(define-fun .25 () Bool (and .23 .24))
(assert .25)
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .12 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0))
(define-fun .31 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.244000002741813659668))
(define-fun .34 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.938000023365020751953)))
(define-fun .35 () (_ FP 8 24) (* .3 .14 .34))
(define-fun .36 () (_ FP 8 24) (+ .3 .12 .35))
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.799000024795532226563)))
(define-fun .40 () (_ FP 8 24) (* .3 .18 .39))
(define-fun .41 () (_ FP 8 24) (+ .3 .36 .40))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.899999976158142089844))
(define-fun .44 () (_ FP 8 24) (* .3 .22 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .41 .44))
(define-fun .46 () Bool (<= .45 .31))
(assert .46)
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.275000005960464477539))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00499999988824129104614))
(define-fun .51 () (_ FP 8 24) (* .3 .14 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .12 .51))
(define-fun .54 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.935000002384185791016))
(define-fun .55 () (_ FP 8 24) (* .3 .18 .54))
(define-fun .56 () (_ FP 8 24) (+ .3 .52 .55))
(define-fun .59 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.294999986886978149414)))
(define-fun .60 () (_ FP 8 24) (* .3 .22 .59))
(define-fun .61 () (_ FP 8 24) (+ .3 .56 .60))
(define-fun .62 () Bool (<= .61 .48))
(assert .62)
(define-fun .65 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0359999984502792358398)))
(define-fun .67 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.337000012397766113281))
(define-fun .68 () (_ FP 8 24) (* .3 .14 .67))
(define-fun .69 () (_ FP 8 24) (+ .3 .12 .68))
(define-fun .71 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.648000001907348632813))
(define-fun .72 () (_ FP 8 24) (* .3 .18 .71))
(define-fun .73 () (_ FP 8 24) (+ .3 .69 .72))
(define-fun .76 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.143999993801116943359)))
(define-fun .77 () (_ FP 8 24) (* .3 .22 .76))
(define-fun .78 () (_ FP 8 24) (+ .3 .73 .77))
(define-fun .79 () Bool (<= .78 .65))
(assert .79)
(check-sat)
