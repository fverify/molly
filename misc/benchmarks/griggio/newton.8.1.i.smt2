(set-logic QF_FPABV)
(declare-fun |c::main::1::IN!0@1#0| () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) |c::main::1::IN!0@1#0|)
(define-fun .11 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 2.0))
(define-fun .12 () Bool (< .9 .11))
(define-fun .14 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 2.0)))
(define-fun .15 () Bool (< .14 .9))
(define-fun .16 () Bool (and .12 .15))
(define-fun .17 () (_ FP 8 24) (* .3 .9 .9))
(define-fun .18 () (_ FP 8 24) (/ .3 .17 .11))
(define-fun .19 () (_ FP 8 24) (- .18))
(define-fun .21 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.0))
(define-fun .22 () (_ FP 8 24) (+ .3 .19 .21))
(define-fun .23 () (_ FP 8 24) (* .3 .9 .17))
(define-fun .24 () (_ FP 8 24) (* .3 .9 .23))
(define-fun .26 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 24.0))
(define-fun .27 () (_ FP 8 24) (/ .3 .24 .26))
(define-fun .28 () (_ FP 8 24) (+ .3 .22 .27))
(define-fun .29 () (_ FP 8 24) (* .3 .9 .24))
(define-fun .30 () (_ FP 8 24) (* .3 .9 .29))
(define-fun .32 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 720.0))
(define-fun .33 () (_ FP 8 24) (/ .3 .30 .32))
(define-fun .34 () (_ FP 8 24) (+ .3 .28 .33))
(define-fun .36 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 6.0))
(define-fun .37 () (_ FP 8 24) (/ .3 .23 .36))
(define-fun .38 () (_ FP 8 24) (- .37))
(define-fun .39 () (_ FP 8 24) (+ .3 .9 .38))
(define-fun .41 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 120.0))
(define-fun .42 () (_ FP 8 24) (/ .3 .29 .41))
(define-fun .43 () (_ FP 8 24) (+ .3 .39 .42))
(define-fun .44 () (_ FP 8 24) (* .3 .9 .30))
(define-fun .46 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 5040.0))
(define-fun .47 () (_ FP 8 24) (/ .3 .44 .46))
(define-fun .48 () (_ FP 8 24) (+ .3 .43 .47))
(define-fun .49 () (_ FP 8 24) (/ .3 .48 .34))
(define-fun .50 () (_ FP 8 24) (- .49))
(define-fun .51 () (_ FP 8 24) (+ .3 .9 .50))
(define-fun .52 () (_ FP 11 53) ((_ asFloat 11 53) .3 .51))
(define-fun .54 () (_ FP 11 53) ((_ asFloat 11 53) roundTowardZero 0.100000000000000005551))
(define-fun .55 () Bool (< .52 .54))
(define-fun .56 () Bool (not .55))
(define-fun .57 () Bool (and .16 .56))
(assert .57)
(check-sat)