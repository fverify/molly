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
(define-fun .32 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.893999993801116943359)))
(define-fun .34 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.307000011205673217773))
(define-fun .35 () (_ FP 8 24) (* .3 .14 .34))
(define-fun .36 () (_ FP 8 24) (+ .3 .12 .35))
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.349000006914138793945)))
(define-fun .40 () (_ FP 8 24) (* .3 .18 .39))
(define-fun .41 () (_ FP 8 24) (+ .3 .36 .40))
(define-fun .44 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00800000037997961044312)))
(define-fun .45 () (_ FP 8 24) (* .3 .22 .44))
(define-fun .46 () (_ FP 8 24) (+ .3 .41 .45))
(define-fun .47 () Bool (<= .46 .32))
(assert .47)
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.333000004291534423828)))
(define-fun .52 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.683000028133392333984))
(define-fun .53 () (_ FP 8 24) (* .3 .14 .52))
(define-fun .54 () (_ FP 8 24) (+ .3 .12 .53))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.444000005722045898438))
(define-fun .57 () (_ FP 8 24) (* .3 .18 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .54 .57))
(define-fun .61 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.654999971389770507813)))
(define-fun .62 () (_ FP 8 24) (* .3 .22 .61))
(define-fun .63 () (_ FP 8 24) (+ .3 .58 .62))
(define-fun .64 () Bool (<= .50 .63))
(assert .64)
(define-fun .66 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.910000026226043701172))
(define-fun .69 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.933000028133392333984)))
(define-fun .70 () (_ FP 8 24) (* .3 .14 .69))
(define-fun .71 () (_ FP 8 24) (+ .3 .12 .70))
(define-fun .74 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.880999982357025146484)))
(define-fun .75 () (_ FP 8 24) (* .3 .18 .74))
(define-fun .76 () (_ FP 8 24) (+ .3 .71 .75))
(define-fun .79 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0160000007599592208862)))
(define-fun .80 () (_ FP 8 24) (* .3 .22 .79))
(define-fun .81 () (_ FP 8 24) (+ .3 .76 .80))
(define-fun .82 () Bool (<= .66 .81))
(assert .82)
(check-sat)
