(set-logic QF_FPABV)
(declare-fun b37 () (_ FP 8 24))
(declare-fun b69 () (_ FP 8 24))
(declare-fun b72 () (_ FP 8 24))
(declare-fun b31 () (_ FP 8 24))
(declare-fun b13 () (_ FP 8 24))
(declare-fun b34 () (_ FP 8 24))
(declare-fun b22 () (_ FP 8 24))
(declare-fun b11 () (_ FP 8 24))
(declare-fun b41 () (_ FP 11 53))
(declare-fun b28 () (_ FP 8 24))
(declare-fun b16 () (_ FP 8 24))
(declare-fun b25 () (_ FP 8 24))
(declare-fun b19 () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) b69)
(define-fun .10 () (_ FP 8 24) b11)
(define-fun .11 () Bool (< .9 .10))
(define-fun .12 () (_ FP 8 24) b13)
(define-fun .13 () (_ FP 8 24) (* .3 .10 .12))
(define-fun .14 () (_ FP 8 24) b16)
(define-fun .15 () (_ FP 8 24) (* .3 .13 .14))
(define-fun .16 () (_ FP 8 24) b19)
(define-fun .17 () (_ FP 8 24) (* .3 .15 .16))
(define-fun .18 () (_ FP 8 24) b22)
(define-fun .19 () (_ FP 8 24) (* .3 .17 .18))
(define-fun .20 () (_ FP 8 24) b25)
(define-fun .21 () (_ FP 8 24) (* .3 .19 .20))
(define-fun .22 () (_ FP 8 24) b28)
(define-fun .23 () (_ FP 8 24) (* .3 .21 .22))
(define-fun .24 () (_ FP 8 24) b31)
(define-fun .25 () (_ FP 8 24) (* .3 .23 .24))
(define-fun .26 () (_ FP 8 24) b34)
(define-fun .27 () (_ FP 8 24) (* .3 .25 .26))
(define-fun .28 () (_ FP 8 24) b37)
(define-fun .29 () (_ FP 8 24) (* .3 .27 .28))
(define-fun .30 () (_ FP 11 53) ((_ asFloat 11 53) .3 .29))
(define-fun .31 () (_ FP 11 53) b41)
(define-fun .32 () Bool (< .31 .30))
(define-fun .33 () Bool (and .11 .32))
(define-fun .34 () (_ FP 8 24) b72)
(define-fun .35 () Bool (< .10 .34))
(define-fun .36 () Bool (and .33 .35))
(define-fun .37 () Bool (< .9 .12))
(define-fun .38 () Bool (and .36 .37))
(define-fun .39 () Bool (< .12 .34))
(define-fun .40 () Bool (and .38 .39))
(define-fun .41 () Bool (< .9 .14))
(define-fun .42 () Bool (and .40 .41))
(define-fun .43 () Bool (< .14 .34))
(define-fun .44 () Bool (and .42 .43))
(define-fun .45 () Bool (< .9 .16))
(define-fun .46 () Bool (and .44 .45))
(define-fun .47 () Bool (< .16 .34))
(define-fun .48 () Bool (and .46 .47))
(define-fun .49 () Bool (< .9 .18))
(define-fun .50 () Bool (and .48 .49))
(define-fun .51 () Bool (< .18 .34))
(define-fun .52 () Bool (and .50 .51))
(define-fun .53 () Bool (< .9 .20))
(define-fun .54 () Bool (and .52 .53))
(define-fun .55 () Bool (< .20 .34))
(define-fun .56 () Bool (and .54 .55))
(define-fun .57 () Bool (< .9 .22))
(define-fun .58 () Bool (and .56 .57))
(define-fun .59 () Bool (< .22 .34))
(define-fun .60 () Bool (and .58 .59))
(define-fun .61 () Bool (< .9 .24))
(define-fun .62 () Bool (and .60 .61))
(define-fun .63 () Bool (< .24 .34))
(define-fun .64 () Bool (and .62 .63))
(define-fun .65 () Bool (< .9 .26))
(define-fun .66 () Bool (and .64 .65))
(define-fun .67 () Bool (< .26 .34))
(define-fun .68 () Bool (and .66 .67))
(define-fun .69 () Bool (< .9 .28))
(define-fun .70 () Bool (and .68 .69))
(define-fun .71 () Bool (< .28 .34))
(define-fun .72 () Bool (and .70 .71))
(assert .72)
(check-sat)
