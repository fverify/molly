(set-logic QF_FPABV)
(declare-fun b38 () (_ FP 8 24))
(declare-fun b26 () (_ FP 8 24))
(declare-fun b14 () (_ FP 8 24))
(declare-fun b29 () (_ FP 8 24))
(declare-fun b35 () (_ FP 8 24))
(declare-fun b20 () (_ FP 8 24))
(declare-fun b17 () (_ FP 8 24))
(declare-fun b10 () (_ FP 8 24))
(declare-fun b32 () (_ FP 8 24))
(declare-fun b11 () (_ FP 8 24))
(declare-fun b41 () (_ FP 8 24))
(declare-fun b23 () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) b11)
(define-fun .10 () (_ FP 8 24) b10)
(define-fun .11 () Bool (< .9 .10))
(define-fun .12 () (_ FP 8 24) (/ .3 .10 .9))
(define-fun .13 () (_ FP 8 24) b14)
(define-fun .14 () (_ FP 8 24) (/ .3 .12 .13))
(define-fun .15 () (_ FP 8 24) b17)
(define-fun .16 () (_ FP 8 24) (/ .3 .14 .15))
(define-fun .17 () (_ FP 8 24) b20)
(define-fun .18 () (_ FP 8 24) (/ .3 .16 .17))
(define-fun .19 () (_ FP 8 24) b23)
(define-fun .20 () (_ FP 8 24) (/ .3 .18 .19))
(define-fun .21 () (_ FP 8 24) b26)
(define-fun .22 () (_ FP 8 24) (/ .3 .20 .21))
(define-fun .23 () (_ FP 8 24) b29)
(define-fun .24 () (_ FP 8 24) (/ .3 .22 .23))
(define-fun .25 () (_ FP 8 24) b32)
(define-fun .26 () (_ FP 8 24) (/ .3 .24 .25))
(define-fun .27 () (_ FP 8 24) b35)
(define-fun .28 () (_ FP 8 24) (/ .3 .26 .27))
(define-fun .29 () (_ FP 8 24) b38)
(define-fun .30 () (_ FP 8 24) (/ .3 .28 .29))
(define-fun .31 () (_ FP 8 24) b41)
(define-fun .32 () Bool (< .30 .31))
(define-fun .33 () Bool (and .11 .32))
(define-fun .34 () Bool (<= .31 .9))
(define-fun .35 () Bool (and .33 .34))
(define-fun .36 () Bool (< .13 .12))
(define-fun .37 () Bool (and .35 .36))
(define-fun .38 () Bool (<= .31 .13))
(define-fun .39 () Bool (and .37 .38))
(define-fun .40 () Bool (< .15 .14))
(define-fun .41 () Bool (and .39 .40))
(define-fun .42 () Bool (<= .31 .15))
(define-fun .43 () Bool (and .41 .42))
(define-fun .44 () Bool (< .17 .16))
(define-fun .45 () Bool (and .43 .44))
(define-fun .46 () Bool (<= .31 .17))
(define-fun .47 () Bool (and .45 .46))
(define-fun .48 () Bool (< .19 .18))
(define-fun .49 () Bool (and .47 .48))
(define-fun .50 () Bool (<= .31 .19))
(define-fun .51 () Bool (and .49 .50))
(define-fun .52 () Bool (< .21 .20))
(define-fun .53 () Bool (and .51 .52))
(define-fun .54 () Bool (<= .31 .21))
(define-fun .55 () Bool (and .53 .54))
(define-fun .56 () Bool (< .23 .22))
(define-fun .57 () Bool (and .55 .56))
(define-fun .58 () Bool (<= .31 .23))
(define-fun .59 () Bool (and .57 .58))
(define-fun .60 () Bool (< .25 .24))
(define-fun .61 () Bool (and .59 .60))
(define-fun .62 () Bool (<= .31 .25))
(define-fun .63 () Bool (and .61 .62))
(define-fun .64 () Bool (< .27 .26))
(define-fun .65 () Bool (and .63 .64))
(define-fun .66 () Bool (<= .31 .27))
(define-fun .67 () Bool (and .65 .66))
(define-fun .68 () Bool (< .29 .28))
(define-fun .69 () Bool (and .67 .68))
(define-fun .70 () Bool (<= .31 .29))
(define-fun .71 () Bool (and .69 .70))
(assert .71)
(check-sat)
