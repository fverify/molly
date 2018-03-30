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
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.824000000953674316406))
(define-fun .42 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.342999994754791259766)))
(define-fun .43 () (_ FP 8 24) (* .3 .14 .42))
(define-fun .44 () (_ FP 8 24) (+ .3 .12 .43))
(define-fun .46 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.830999970436096191406))
(define-fun .47 () (_ FP 8 24) (* .3 .18 .46))
(define-fun .48 () (_ FP 8 24) (+ .3 .44 .47))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.77600002288818359375))
(define-fun .51 () (_ FP 8 24) (* .3 .22 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .48 .51))
(define-fun .54 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.354000002145767211914))
(define-fun .55 () (_ FP 8 24) (* .3 .26 .54))
(define-fun .56 () (_ FP 8 24) (+ .3 .52 .55))
(define-fun .58 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.575999975204467773438))
(define-fun .59 () (_ FP 8 24) (* .3 .30 .58))
(define-fun .60 () (_ FP 8 24) (+ .3 .56 .59))
(define-fun .61 () Bool (<= .60 .39))
(assert .61)
(define-fun .63 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.103000000119209289551))
(define-fun .66 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.843999981880187988281)))
(define-fun .67 () (_ FP 8 24) (* .3 .14 .66))
(define-fun .68 () (_ FP 8 24) (+ .3 .12 .67))
(define-fun .70 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0439999997615814208984))
(define-fun .71 () (_ FP 8 24) (* .3 .18 .70))
(define-fun .72 () (_ FP 8 24) (+ .3 .68 .71))
(define-fun .75 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.518000006675720214844)))
(define-fun .76 () (_ FP 8 24) (* .3 .22 .75))
(define-fun .77 () (_ FP 8 24) (+ .3 .72 .76))
(define-fun .80 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.823000013828277587891)))
(define-fun .81 () (_ FP 8 24) (* .3 .26 .80))
(define-fun .82 () (_ FP 8 24) (+ .3 .77 .81))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.182999998331069946289)))
(define-fun .86 () (_ FP 8 24) (* .3 .30 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .82 .86))
(define-fun .88 () Bool (<= .63 .87))
(assert .88)
(define-fun .90 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.509999990463256835938))
(define-fun .92 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.551999986171722412109))
(define-fun .93 () (_ FP 8 24) (* .3 .14 .92))
(define-fun .94 () (_ FP 8 24) (+ .3 .12 .93))
(define-fun .96 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.319999992847442626953))
(define-fun .97 () (_ FP 8 24) (* .3 .18 .96))
(define-fun .98 () (_ FP 8 24) (+ .3 .94 .97))
(define-fun .100 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0640000030398368835449))
(define-fun .101 () (_ FP 8 24) (* .3 .22 .100))
(define-fun .102 () (_ FP 8 24) (+ .3 .98 .101))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0219999998807907104492)))
(define-fun .106 () (_ FP 8 24) (* .3 .26 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .102 .106))
(define-fun .109 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.109999999403953552246))
(define-fun .110 () (_ FP 8 24) (* .3 .30 .109))
(define-fun .111 () (_ FP 8 24) (+ .3 .107 .110))
(define-fun .112 () Bool (<= .90 .111))
(assert .112)
(define-fun .114 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.187999993562698364258))
(define-fun .117 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.17800000309944152832)))
(define-fun .118 () (_ FP 8 24) (* .3 .14 .117))
(define-fun .119 () (_ FP 8 24) (+ .3 .12 .118))
(define-fun .122 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.992999970912933349609)))
(define-fun .123 () (_ FP 8 24) (* .3 .18 .122))
(define-fun .124 () (_ FP 8 24) (+ .3 .119 .123))
(define-fun .127 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.611999988555908203125)))
(define-fun .128 () (_ FP 8 24) (* .3 .22 .127))
(define-fun .129 () (_ FP 8 24) (+ .3 .124 .128))
(define-fun .131 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.652999997138977050781))
(define-fun .132 () (_ FP 8 24) (* .3 .26 .131))
(define-fun .133 () (_ FP 8 24) (+ .3 .129 .132))
(define-fun .136 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.827000021934509277344)))
(define-fun .137 () (_ FP 8 24) (* .3 .30 .136))
(define-fun .138 () (_ FP 8 24) (+ .3 .133 .137))
(define-fun .139 () Bool (<= .138 .114))
(assert .139)
(define-fun .141 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.28299999237060546875))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.259999990463256835938)))
(define-fun .145 () (_ FP 8 24) (* .3 .14 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .12 .145))
(define-fun .148 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0939999967813491821289))
(define-fun .149 () (_ FP 8 24) (* .3 .18 .148))
(define-fun .150 () (_ FP 8 24) (+ .3 .146 .149))
(define-fun .152 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.456999987363815307617))
(define-fun .153 () (_ FP 8 24) (* .3 .22 .152))
(define-fun .154 () (_ FP 8 24) (+ .3 .150 .153))
(define-fun .157 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.814000010490417480469)))
(define-fun .158 () (_ FP 8 24) (* .3 .26 .157))
(define-fun .159 () (_ FP 8 24) (+ .3 .154 .158))
(define-fun .161 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.695999979972839355469))
(define-fun .162 () (_ FP 8 24) (* .3 .30 .161))
(define-fun .163 () (_ FP 8 24) (+ .3 .159 .162))
(define-fun .164 () Bool (<= .141 .163))
(assert .164)
(check-sat)
