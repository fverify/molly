(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(define-fun .10 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 10.0))
(define-fun .13 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 10.0)))
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
(define-fun .32 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.760999977588653564453)))
(define-fun .35 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.361000001430511474609)))
(define-fun .36 () (_ FP 8 24) (* .3 .14 .35))
(define-fun .37 () (_ FP 8 24) (+ .3 .12 .36))
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.187000006437301635742))
(define-fun .40 () (_ FP 8 24) (* .3 .18 .39))
(define-fun .41 () (_ FP 8 24) (+ .3 .37 .40))
(define-fun .44 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.199000000953674316406)))
(define-fun .45 () (_ FP 8 24) (* .3 .22 .44))
(define-fun .46 () (_ FP 8 24) (+ .3 .41 .45))
(define-fun .47 () Bool (<= .32 .46))
(assert .47)
(define-fun .49 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.365000009536743164063))
(define-fun .52 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.688000023365020751953)))
(define-fun .53 () (_ FP 8 24) (* .3 .14 .52))
(define-fun .54 () (_ FP 8 24) (+ .3 .12 .53))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.991999983787536621094))
(define-fun .57 () (_ FP 8 24) (* .3 .18 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .54 .57))
(define-fun .60 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.398999989032745361328))
(define-fun .61 () (_ FP 8 24) (* .3 .22 .60))
(define-fun .62 () (_ FP 8 24) (+ .3 .58 .61))
(define-fun .63 () Bool (<= .49 .62))
(assert .63)
(define-fun .66 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.971000015735626220703)))
(define-fun .69 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00400000018998980522156)))
(define-fun .70 () (_ FP 8 24) (* .3 .14 .69))
(define-fun .71 () (_ FP 8 24) (+ .3 .12 .70))
(define-fun .74 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.352999985218048095703)))
(define-fun .75 () (_ FP 8 24) (* .3 .18 .74))
(define-fun .76 () (_ FP 8 24) (+ .3 .71 .75))
(define-fun .78 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.628000020980834960938))
(define-fun .79 () (_ FP 8 24) (* .3 .22 .78))
(define-fun .80 () (_ FP 8 24) (+ .3 .76 .79))
(define-fun .81 () Bool (<= .80 .66))
(assert .81)
(check-sat)
