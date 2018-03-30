(set-logic QF_FPABV)
(declare-fun |c::main::1::IN!0@1#0| () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) |c::main::1::IN!0@1#0|)
(define-fun .11 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.20000000298023223877))
(define-fun .12 () Bool (< .9 .11))
(define-fun .14 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.20000000298023223877)))
(define-fun .15 () Bool (< .14 .9))
(define-fun .16 () Bool (and .12 .15))
(define-fun .17 () (_ FP 8 24) (* .3 .9 .9))
(define-fun .19 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 2.0))
(define-fun .20 () (_ FP 8 24) (/ .3 .17 .19))
(define-fun .21 () (_ FP 8 24) (- .20))
(define-fun .23 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.0))
(define-fun .24 () (_ FP 8 24) (+ .3 .21 .23))
(define-fun .25 () (_ FP 8 24) (* .3 .9 .17))
(define-fun .26 () (_ FP 8 24) (* .3 .9 .25))
(define-fun .28 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 24.0))
(define-fun .29 () (_ FP 8 24) (/ .3 .26 .28))
(define-fun .30 () (_ FP 8 24) (+ .3 .24 .29))
(define-fun .31 () (_ FP 8 24) (* .3 .9 .26))
(define-fun .32 () (_ FP 8 24) (* .3 .9 .31))
(define-fun .34 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 720.0))
(define-fun .35 () (_ FP 8 24) (/ .3 .32 .34))
(define-fun .36 () (_ FP 8 24) (+ .3 .30 .35))
(define-fun .38 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 6.0))
(define-fun .39 () (_ FP 8 24) (/ .3 .25 .38))
(define-fun .40 () (_ FP 8 24) (- .39))
(define-fun .41 () (_ FP 8 24) (+ .3 .9 .40))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 120.0))
(define-fun .44 () (_ FP 8 24) (/ .3 .31 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .41 .44))
(define-fun .46 () (_ FP 8 24) (* .3 .9 .32))
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 5040.0))
(define-fun .49 () (_ FP 8 24) (/ .3 .46 .48))
(define-fun .50 () (_ FP 8 24) (+ .3 .45 .49))
(define-fun .51 () (_ FP 8 24) (/ .3 .50 .36))
(define-fun .52 () (_ FP 8 24) (- .51))
(define-fun .53 () (_ FP 8 24) (+ .3 .9 .52))
(define-fun .54 () (_ FP 8 24) (* .3 .53 .53))
(define-fun .55 () (_ FP 8 24) (/ .3 .54 .19))
(define-fun .56 () (_ FP 8 24) (- .55))
(define-fun .57 () (_ FP 8 24) (+ .3 .23 .56))
(define-fun .58 () (_ FP 8 24) (* .3 .53 .54))
(define-fun .59 () (_ FP 8 24) (* .3 .53 .58))
(define-fun .60 () (_ FP 8 24) (/ .3 .59 .28))
(define-fun .61 () (_ FP 8 24) (+ .3 .57 .60))
(define-fun .62 () (_ FP 8 24) (* .3 .53 .59))
(define-fun .63 () (_ FP 8 24) (* .3 .53 .62))
(define-fun .64 () (_ FP 8 24) (/ .3 .63 .34))
(define-fun .65 () (_ FP 8 24) (+ .3 .61 .64))
(define-fun .66 () (_ FP 8 24) (/ .3 .58 .38))
(define-fun .67 () (_ FP 8 24) (- .66))
(define-fun .68 () (_ FP 8 24) (+ .3 .53 .67))
(define-fun .69 () (_ FP 8 24) (/ .3 .62 .43))
(define-fun .70 () (_ FP 8 24) (+ .3 .68 .69))
(define-fun .71 () (_ FP 8 24) (* .3 .53 .63))
(define-fun .72 () (_ FP 8 24) (/ .3 .71 .48))
(define-fun .73 () (_ FP 8 24) (+ .3 .70 .72))
(define-fun .74 () (_ FP 8 24) (/ .3 .73 .65))
(define-fun .75 () (_ FP 8 24) (- .74))
(define-fun .76 () (_ FP 8 24) (+ .3 .53 .75))
(define-fun .77 () (_ FP 8 24) (* .3 .76 .76))
(define-fun .78 () (_ FP 8 24) (/ .3 .77 .19))
(define-fun .79 () (_ FP 8 24) (- .78))
(define-fun .80 () (_ FP 8 24) (+ .3 .23 .79))
(define-fun .81 () (_ FP 8 24) (* .3 .76 .77))
(define-fun .82 () (_ FP 8 24) (* .3 .76 .81))
(define-fun .83 () (_ FP 8 24) (/ .3 .82 .28))
(define-fun .84 () (_ FP 8 24) (+ .3 .80 .83))
(define-fun .85 () (_ FP 8 24) (* .3 .76 .82))
(define-fun .86 () (_ FP 8 24) (* .3 .76 .85))
(define-fun .87 () (_ FP 8 24) (/ .3 .86 .34))
(define-fun .88 () (_ FP 8 24) (+ .3 .84 .87))
(define-fun .89 () (_ FP 8 24) (/ .3 .81 .38))
(define-fun .90 () (_ FP 8 24) (- .89))
(define-fun .91 () (_ FP 8 24) (+ .3 .76 .90))
(define-fun .92 () (_ FP 8 24) (/ .3 .85 .43))
(define-fun .93 () (_ FP 8 24) (+ .3 .91 .92))
(define-fun .94 () (_ FP 8 24) (* .3 .76 .86))
(define-fun .95 () (_ FP 8 24) (/ .3 .94 .48))
(define-fun .96 () (_ FP 8 24) (+ .3 .93 .95))
(define-fun .97 () (_ FP 8 24) (/ .3 .96 .88))
(define-fun .98 () (_ FP 8 24) (- .97))
(define-fun .99 () (_ FP 8 24) (+ .3 .76 .98))
(define-fun .100 () (_ FP 11 53) ((_ asFloat 11 53) .3 .99))
(define-fun .102 () (_ FP 11 53) ((_ asFloat 11 53) roundTowardZero 0.100000000000000005551))
(define-fun .103 () Bool (< .100 .102))
(define-fun .104 () Bool (not .103))
(define-fun .105 () Bool (and .16 .104))
(assert .105)
(check-sat)
