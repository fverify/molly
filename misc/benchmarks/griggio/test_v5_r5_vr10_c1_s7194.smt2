(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(declare-fun x3 () (_ FP 8 24))
(declare-fun x4 () (_ FP 8 24))
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
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.218999996781349182129))
(define-fun .42 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.430000007152557373047)))
(define-fun .43 () (_ FP 8 24) (* .3 .14 .42))
(define-fun .44 () (_ FP 8 24) (+ .3 .12 .43))
(define-fun .46 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.166999995708465576172))
(define-fun .47 () (_ FP 8 24) (* .3 .18 .46))
(define-fun .48 () (_ FP 8 24) (+ .3 .44 .47))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.950999975204467773438))
(define-fun .51 () (_ FP 8 24) (* .3 .22 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .48 .51))
(define-fun .54 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.46099999547004699707))
(define-fun .55 () (_ FP 8 24) (* .3 .26 .54))
(define-fun .56 () (_ FP 8 24) (+ .3 .52 .55))
(define-fun .59 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.284000009298324584961)))
(define-fun .60 () (_ FP 8 24) (* .3 .30 .59))
(define-fun .61 () (_ FP 8 24) (+ .3 .56 .60))
(define-fun .62 () Bool (<= .61 .39))
(assert .62)
(define-fun .64 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.402000010013580322266))
(define-fun .67 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.675999999046325683594)))
(define-fun .68 () (_ FP 8 24) (* .3 .14 .67))
(define-fun .69 () (_ FP 8 24) (+ .3 .12 .68))
(define-fun .71 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0670000016689300537109))
(define-fun .72 () (_ FP 8 24) (* .3 .18 .71))
(define-fun .73 () (_ FP 8 24) (+ .3 .69 .72))
(define-fun .75 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.280000001192092895508))
(define-fun .76 () (_ FP 8 24) (* .3 .22 .75))
(define-fun .77 () (_ FP 8 24) (+ .3 .73 .76))
(define-fun .79 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.72399997711181640625))
(define-fun .80 () (_ FP 8 24) (* .3 .26 .79))
(define-fun .81 () (_ FP 8 24) (+ .3 .77 .80))
(define-fun .83 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.660000026226043701172))
(define-fun .84 () (_ FP 8 24) (* .3 .30 .83))
(define-fun .85 () (_ FP 8 24) (+ .3 .81 .84))
(define-fun .86 () Bool (<= .64 .85))
(assert .86)
(define-fun .88 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.578000009059906005859))
(define-fun .90 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.720000028610229492188))
(define-fun .91 () (_ FP 8 24) (* .3 .14 .90))
(define-fun .92 () (_ FP 8 24) (+ .3 .12 .91))
(define-fun .95 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.328999996185302734375)))
(define-fun .96 () (_ FP 8 24) (* .3 .18 .95))
(define-fun .97 () (_ FP 8 24) (+ .3 .92 .96))
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.602999985218048095703))
(define-fun .100 () (_ FP 8 24) (* .3 .22 .99))
(define-fun .101 () (_ FP 8 24) (+ .3 .97 .100))
(define-fun .104 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.607999980449676513672)))
(define-fun .105 () (_ FP 8 24) (* .3 .26 .104))
(define-fun .106 () (_ FP 8 24) (+ .3 .101 .105))
(define-fun .108 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.764999985694885253906))
(define-fun .109 () (_ FP 8 24) (* .3 .30 .108))
(define-fun .110 () (_ FP 8 24) (+ .3 .106 .109))
(define-fun .111 () Bool (<= .110 .88))
(assert .111)
(define-fun .113 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.234999999403953552246))
(define-fun .116 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.254000008106231689453)))
(define-fun .117 () (_ FP 8 24) (* .3 .14 .116))
(define-fun .118 () (_ FP 8 24) (+ .3 .12 .117))
(define-fun .120 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.411000013351440429688))
(define-fun .121 () (_ FP 8 24) (* .3 .18 .120))
(define-fun .122 () (_ FP 8 24) (+ .3 .118 .121))
(define-fun .124 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.703999996185302734375))
(define-fun .125 () (_ FP 8 24) (* .3 .22 .124))
(define-fun .126 () (_ FP 8 24) (+ .3 .122 .125))
(define-fun .129 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.603999972343444824219)))
(define-fun .130 () (_ FP 8 24) (* .3 .26 .129))
(define-fun .131 () (_ FP 8 24) (+ .3 .126 .130))
(define-fun .134 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.24699999392032623291)))
(define-fun .135 () (_ FP 8 24) (* .3 .30 .134))
(define-fun .136 () (_ FP 8 24) (+ .3 .131 .135))
(define-fun .137 () Bool (<= .113 .136))
(assert .137)
(define-fun .139 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.504000008106231689453))
(define-fun .142 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.352999985218048095703)))
(define-fun .143 () (_ FP 8 24) (* .3 .14 .142))
(define-fun .144 () (_ FP 8 24) (+ .3 .12 .143))
(define-fun .147 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.666000008583068847656)))
(define-fun .148 () (_ FP 8 24) (* .3 .18 .147))
(define-fun .149 () (_ FP 8 24) (+ .3 .144 .148))
(define-fun .151 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.377000004053115844727))
(define-fun .152 () (_ FP 8 24) (* .3 .22 .151))
(define-fun .153 () (_ FP 8 24) (+ .3 .149 .152))
(define-fun .155 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.456000000238418579102))
(define-fun .156 () (_ FP 8 24) (* .3 .26 .155))
(define-fun .157 () (_ FP 8 24) (+ .3 .153 .156))
(define-fun .159 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.537999987602233886719))
(define-fun .160 () (_ FP 8 24) (* .3 .30 .159))
(define-fun .161 () (_ FP 8 24) (+ .3 .157 .160))
(define-fun .162 () Bool (<= .139 .161))
(assert .162)
(check-sat)
