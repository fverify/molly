(set-logic QF_FPABV)
(declare-fun |c::main::1::IN!0@1#0| () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) |c::main::1::IN!0@1#0|)
(define-fun .11 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.5))
(define-fun .12 () (_ FP 8 24) (* .3 .9 .11))
(define-fun .14 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.0))
(define-fun .15 () (_ FP 8 24) (+ .3 .12 .14))
(define-fun .17 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.125))
(define-fun .18 () (_ FP 8 24) (* .3 .9 .17))
(define-fun .19 () (_ FP 8 24) (* .3 .9 .18))
(define-fun .20 () (_ FP 8 24) (- .19))
(define-fun .21 () (_ FP 8 24) (+ .3 .15 .20))
(define-fun .23 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0625))
(define-fun .24 () (_ FP 8 24) (* .3 .9 .23))
(define-fun .25 () (_ FP 8 24) (* .3 .9 .24))
(define-fun .26 () (_ FP 8 24) (* .3 .9 .25))
(define-fun .27 () (_ FP 8 24) (+ .3 .21 .26))
(define-fun .29 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0390625))
(define-fun .30 () (_ FP 8 24) (* .3 .9 .29))
(define-fun .31 () (_ FP 8 24) (* .3 .9 .30))
(define-fun .32 () (_ FP 8 24) (* .3 .9 .31))
(define-fun .33 () (_ FP 8 24) (* .3 .9 .32))
(define-fun .34 () (_ FP 8 24) (- .33))
(define-fun .35 () (_ FP 8 24) (+ .3 .27 .34))
(define-fun .37 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0))
(define-fun .38 () Bool (<= .37 .35))
(define-fun .39 () Bool (not .38))
(define-fun .41 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.39800000190734863281))
(define-fun .42 () Bool (< .35 .41))
(define-fun .43 () Bool (not .42))
(define-fun .44 () Bool (< .9 .14))
(define-fun .45 () Bool (<= .37 .9))
(define-fun .46 () Bool (and .44 .45))
(define-fun .47 () Bool (and .43 .46))
(define-fun .48 () Bool (and .39 .47))
(assert .48)
(check-sat)
