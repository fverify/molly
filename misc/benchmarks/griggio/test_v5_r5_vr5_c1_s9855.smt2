(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(declare-fun x3 () (_ FP 8 24))
(declare-fun x4 () (_ FP 8 24))
(define-fun .10 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 5.0))
(define-fun .13 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 5.0)))
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
(define-fun .26 () (_ FP 8 24) x3)
(define-fun .27 () Bool (<= .13 .26))
(define-fun .28 () Bool (<= .26 .10))
(define-fun .29 () Bool (and .27 .28))
(assert .29)
(define-fun .30 () (_ FP 8 24) x4)
(define-fun .31 () Bool (<= .13 .30))
(define-fun .32 () Bool (<= .30 .10))
(define-fun .33 () Bool (and .31 .32))
(assert .33)
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .12 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0))
(define-fun .40 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00400000018998980522156)))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.545000016689300537109)))
(define-fun .44 () (_ FP 8 24) (* .3 .14 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .12 .44))
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.850000023841857910156)))
(define-fun .49 () (_ FP 8 24) (* .3 .18 .48))
(define-fun .50 () (_ FP 8 24) (+ .3 .45 .49))
(define-fun .52 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.398999989032745361328))
(define-fun .53 () (_ FP 8 24) (* .3 .22 .52))
(define-fun .54 () (_ FP 8 24) (+ .3 .50 .53))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.853999972343444824219))
(define-fun .57 () (_ FP 8 24) (* .3 .26 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .54 .57))
(define-fun .60 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.072999998927116394043))
(define-fun .61 () (_ FP 8 24) (* .3 .30 .60))
(define-fun .62 () (_ FP 8 24) (+ .3 .58 .61))
(define-fun .63 () Bool (<= .62 .40))
(assert .63)
(define-fun .65 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.720000028610229492188))
(define-fun .67 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.714999973773956298828))
(define-fun .68 () (_ FP 8 24) (* .3 .14 .67))
(define-fun .69 () (_ FP 8 24) (+ .3 .12 .68))
(define-fun .72 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.195999994874000549316)))
(define-fun .73 () (_ FP 8 24) (* .3 .18 .72))
(define-fun .74 () (_ FP 8 24) (+ .3 .69 .73))
(define-fun .77 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.948000013828277587891)))
(define-fun .78 () (_ FP 8 24) (* .3 .22 .77))
(define-fun .79 () (_ FP 8 24) (+ .3 .74 .78))
(define-fun .81 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.476000010967254638672))
(define-fun .82 () (_ FP 8 24) (* .3 .26 .81))
(define-fun .83 () (_ FP 8 24) (+ .3 .79 .82))
(define-fun .86 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.324000000953674316406)))
(define-fun .87 () (_ FP 8 24) (* .3 .30 .86))
(define-fun .88 () (_ FP 8 24) (+ .3 .83 .87))
(define-fun .89 () Bool (<= .65 .88))
(assert .89)
(define-fun .92 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.925999999046325683594)))
(define-fun .95 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.731999993324279785156)))
(define-fun .96 () (_ FP 8 24) (* .3 .14 .95))
(define-fun .97 () (_ FP 8 24) (+ .3 .12 .96))
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.127000004053115844727))
(define-fun .100 () (_ FP 8 24) (* .3 .18 .99))
(define-fun .101 () (_ FP 8 24) (+ .3 .97 .100))
(define-fun .104 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.293999999761581420898)))
(define-fun .105 () (_ FP 8 24) (* .3 .22 .104))
(define-fun .106 () (_ FP 8 24) (+ .3 .101 .105))
(define-fun .109 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.541000008583068847656)))
(define-fun .110 () (_ FP 8 24) (* .3 .26 .109))
(define-fun .111 () (_ FP 8 24) (+ .3 .106 .110))
(define-fun .113 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.866999983787536621094))
(define-fun .114 () (_ FP 8 24) (* .3 .30 .113))
(define-fun .115 () (_ FP 8 24) (+ .3 .111 .114))
(define-fun .116 () Bool (<= .92 .115))
(assert .116)
(define-fun .118 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.10700000077486038208))
(define-fun .120 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.726000010967254638672))
(define-fun .121 () (_ FP 8 24) (* .3 .14 .120))
(define-fun .122 () (_ FP 8 24) (+ .3 .12 .121))
(define-fun .125 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00200000009499490261078)))
(define-fun .126 () (_ FP 8 24) (* .3 .18 .125))
(define-fun .127 () (_ FP 8 24) (+ .3 .122 .126))
(define-fun .129 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.486000001430511474609))
(define-fun .130 () (_ FP 8 24) (* .3 .22 .129))
(define-fun .131 () (_ FP 8 24) (+ .3 .127 .130))
(define-fun .134 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.930000007152557373047)))
(define-fun .135 () (_ FP 8 24) (* .3 .26 .134))
(define-fun .136 () (_ FP 8 24) (+ .3 .131 .135))
(define-fun .138 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.273000001907348632813))
(define-fun .139 () (_ FP 8 24) (* .3 .30 .138))
(define-fun .140 () (_ FP 8 24) (+ .3 .136 .139))
(define-fun .141 () Bool (<= .140 .118))
(assert .141)
(define-fun .143 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.878000020980834960938))
(define-fun .146 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.12800000607967376709)))
(define-fun .147 () (_ FP 8 24) (* .3 .14 .146))
(define-fun .148 () (_ FP 8 24) (+ .3 .12 .147))
(define-fun .151 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.38100001215934753418)))
(define-fun .152 () (_ FP 8 24) (* .3 .18 .151))
(define-fun .153 () (_ FP 8 24) (+ .3 .148 .152))
(define-fun .156 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.624000012874603271484)))
(define-fun .157 () (_ FP 8 24) (* .3 .22 .156))
(define-fun .158 () (_ FP 8 24) (+ .3 .153 .157))
(define-fun .161 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.805999994277954101563)))
(define-fun .162 () (_ FP 8 24) (* .3 .26 .161))
(define-fun .163 () (_ FP 8 24) (+ .3 .158 .162))
(define-fun .166 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.47999998927116394043)))
(define-fun .167 () (_ FP 8 24) (* .3 .30 .166))
(define-fun .168 () (_ FP 8 24) (+ .3 .163 .167))
(define-fun .169 () Bool (<= .168 .143))
(assert .169)
(check-sat)
