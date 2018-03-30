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
(define-fun .52 () (_ FP 8 24) (* .3 .51 .51))
(define-fun .53 () (_ FP 8 24) (/ .3 .52 .11))
(define-fun .54 () (_ FP 8 24) (- .53))
(define-fun .55 () (_ FP 8 24) (+ .3 .21 .54))
(define-fun .56 () (_ FP 8 24) (* .3 .51 .52))
(define-fun .57 () (_ FP 8 24) (* .3 .51 .56))
(define-fun .58 () (_ FP 8 24) (/ .3 .57 .26))
(define-fun .59 () (_ FP 8 24) (+ .3 .55 .58))
(define-fun .60 () (_ FP 8 24) (* .3 .51 .57))
(define-fun .61 () (_ FP 8 24) (* .3 .51 .60))
(define-fun .62 () (_ FP 8 24) (/ .3 .61 .32))
(define-fun .63 () (_ FP 8 24) (+ .3 .59 .62))
(define-fun .64 () (_ FP 8 24) (/ .3 .56 .36))
(define-fun .65 () (_ FP 8 24) (- .64))
(define-fun .66 () (_ FP 8 24) (+ .3 .51 .65))
(define-fun .67 () (_ FP 8 24) (/ .3 .60 .41))
(define-fun .68 () (_ FP 8 24) (+ .3 .66 .67))
(define-fun .69 () (_ FP 8 24) (* .3 .51 .61))
(define-fun .70 () (_ FP 8 24) (/ .3 .69 .46))
(define-fun .71 () (_ FP 8 24) (+ .3 .68 .70))
(define-fun .72 () (_ FP 8 24) (/ .3 .71 .63))
(define-fun .73 () (_ FP 8 24) (- .72))
(define-fun .74 () (_ FP 8 24) (+ .3 .51 .73))
(define-fun .75 () (_ FP 8 24) (* .3 .74 .74))
(define-fun .76 () (_ FP 8 24) (/ .3 .75 .11))
(define-fun .77 () (_ FP 8 24) (- .76))
(define-fun .78 () (_ FP 8 24) (+ .3 .21 .77))
(define-fun .79 () (_ FP 8 24) (* .3 .74 .75))
(define-fun .80 () (_ FP 8 24) (* .3 .74 .79))
(define-fun .81 () (_ FP 8 24) (/ .3 .80 .26))
(define-fun .82 () (_ FP 8 24) (+ .3 .78 .81))
(define-fun .83 () (_ FP 8 24) (* .3 .74 .80))
(define-fun .84 () (_ FP 8 24) (* .3 .74 .83))
(define-fun .85 () (_ FP 8 24) (/ .3 .84 .32))
(define-fun .86 () (_ FP 8 24) (+ .3 .82 .85))
(define-fun .87 () (_ FP 8 24) (/ .3 .79 .36))
(define-fun .88 () (_ FP 8 24) (- .87))
(define-fun .89 () (_ FP 8 24) (+ .3 .74 .88))
(define-fun .90 () (_ FP 8 24) (/ .3 .83 .41))
(define-fun .91 () (_ FP 8 24) (+ .3 .89 .90))
(define-fun .92 () (_ FP 8 24) (* .3 .74 .84))
(define-fun .93 () (_ FP 8 24) (/ .3 .92 .46))
(define-fun .94 () (_ FP 8 24) (+ .3 .91 .93))
(define-fun .95 () (_ FP 8 24) (/ .3 .94 .86))
(define-fun .96 () (_ FP 8 24) (- .95))
(define-fun .97 () (_ FP 8 24) (+ .3 .74 .96))
(define-fun .98 () (_ FP 11 53) ((_ asFloat 11 53) .3 .97))
(define-fun .100 () (_ FP 11 53) ((_ asFloat 11 53) roundTowardZero 0.100000000000000005551))
(define-fun .101 () Bool (< .98 .100))
(define-fun .102 () Bool (not .101))
(define-fun .103 () Bool (and .16 .102))
(assert .103)
(check-sat)
