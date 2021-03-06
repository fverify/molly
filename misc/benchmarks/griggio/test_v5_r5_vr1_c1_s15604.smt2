(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(declare-fun x3 () (_ FP 8 24))
(declare-fun x4 () (_ FP 8 24))
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
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.595000028610229492188))
(define-fun .42 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0430000014603137969971)))
(define-fun .43 () (_ FP 8 24) (* .3 .14 .42))
(define-fun .44 () (_ FP 8 24) (+ .3 .12 .43))
(define-fun .46 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.513999998569488525391))
(define-fun .47 () (_ FP 8 24) (* .3 .18 .46))
(define-fun .48 () (_ FP 8 24) (+ .3 .44 .47))
(define-fun .51 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.601000010967254638672)))
(define-fun .52 () (_ FP 8 24) (* .3 .22 .51))
(define-fun .53 () (_ FP 8 24) (+ .3 .48 .52))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.460000008344650268555)))
(define-fun .57 () (_ FP 8 24) (* .3 .26 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .53 .57))
(define-fun .61 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0599999986588954925537)))
(define-fun .62 () (_ FP 8 24) (* .3 .30 .61))
(define-fun .63 () (_ FP 8 24) (+ .3 .58 .62))
(define-fun .64 () Bool (<= .63 .39))
(assert .64)
(define-fun .67 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.363999992609024047852)))
(define-fun .69 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.675999999046325683594))
(define-fun .70 () (_ FP 8 24) (* .3 .14 .69))
(define-fun .71 () (_ FP 8 24) (+ .3 .12 .70))
(define-fun .73 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0979999974370002746582))
(define-fun .74 () (_ FP 8 24) (* .3 .18 .73))
(define-fun .75 () (_ FP 8 24) (+ .3 .71 .74))
(define-fun .78 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0920000001788139343262)))
(define-fun .79 () (_ FP 8 24) (* .3 .22 .78))
(define-fun .80 () (_ FP 8 24) (+ .3 .75 .79))
(define-fun .82 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.745000004768371582031))
(define-fun .83 () (_ FP 8 24) (* .3 .26 .82))
(define-fun .84 () (_ FP 8 24) (+ .3 .80 .83))
(define-fun .86 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.275000005960464477539))
(define-fun .87 () (_ FP 8 24) (* .3 .30 .86))
(define-fun .88 () (_ FP 8 24) (+ .3 .84 .87))
(define-fun .89 () Bool (<= .88 .67))
(assert .89)
(define-fun .92 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.704999983310699462891)))
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.286000013351440429688))
(define-fun .95 () (_ FP 8 24) (* .3 .14 .94))
(define-fun .96 () (_ FP 8 24) (+ .3 .12 .95))
(define-fun .98 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.676999986171722412109))
(define-fun .99 () (_ FP 8 24) (* .3 .18 .98))
(define-fun .100 () (_ FP 8 24) (+ .3 .96 .99))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.528999984264373779297)))
(define-fun .104 () (_ FP 8 24) (* .3 .22 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .100 .104))
(define-fun .108 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.46700000762939453125)))
(define-fun .109 () (_ FP 8 24) (* .3 .26 .108))
(define-fun .110 () (_ FP 8 24) (+ .3 .105 .109))
(define-fun .112 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.481000006198883056641))
(define-fun .113 () (_ FP 8 24) (* .3 .30 .112))
(define-fun .114 () (_ FP 8 24) (+ .3 .110 .113))
(define-fun .115 () Bool (<= .92 .114))
(assert .115)
(define-fun .117 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.400000005960464477539))
(define-fun .119 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.970000028610229492188))
(define-fun .120 () (_ FP 8 24) (* .3 .14 .119))
(define-fun .121 () (_ FP 8 24) (+ .3 .12 .120))
(define-fun .123 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.437999993562698364258))
(define-fun .124 () (_ FP 8 24) (* .3 .18 .123))
(define-fun .125 () (_ FP 8 24) (+ .3 .121 .124))
(define-fun .128 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.958000004291534423828)))
(define-fun .129 () (_ FP 8 24) (* .3 .22 .128))
(define-fun .130 () (_ FP 8 24) (+ .3 .125 .129))
(define-fun .133 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.305999994277954101563)))
(define-fun .134 () (_ FP 8 24) (* .3 .26 .133))
(define-fun .135 () (_ FP 8 24) (+ .3 .130 .134))
(define-fun .137 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.792999982833862304688))
(define-fun .138 () (_ FP 8 24) (* .3 .30 .137))
(define-fun .139 () (_ FP 8 24) (+ .3 .135 .138))
(define-fun .140 () Bool (<= .117 .139))
(assert .140)
(define-fun .142 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.888000011444091796875))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.495999991893768310547))
(define-fun .145 () (_ FP 8 24) (* .3 .14 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .12 .145))
(define-fun .149 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.39500001072883605957)))
(define-fun .150 () (_ FP 8 24) (* .3 .18 .149))
(define-fun .151 () (_ FP 8 24) (+ .3 .146 .150))
(define-fun .154 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.426999986171722412109)))
(define-fun .155 () (_ FP 8 24) (* .3 .22 .154))
(define-fun .156 () (_ FP 8 24) (+ .3 .151 .155))
(define-fun .158 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.759999990463256835938))
(define-fun .159 () (_ FP 8 24) (* .3 .26 .158))
(define-fun .160 () (_ FP 8 24) (+ .3 .156 .159))
(define-fun .163 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.463999986648559570313)))
(define-fun .164 () (_ FP 8 24) (* .3 .30 .163))
(define-fun .165 () (_ FP 8 24) (+ .3 .160 .164))
(define-fun .166 () Bool (<= .165 .142))
(assert .166)
(check-sat)
