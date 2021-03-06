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
(define-fun .40 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.155000001192092895508)))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.101999998092651367188)))
(define-fun .44 () (_ FP 8 24) (* .3 .14 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .12 .44))
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.20000000298023223877)))
(define-fun .49 () (_ FP 8 24) (* .3 .18 .48))
(define-fun .50 () (_ FP 8 24) (+ .3 .45 .49))
(define-fun .53 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.228000000119209289551)))
(define-fun .54 () (_ FP 8 24) (* .3 .22 .53))
(define-fun .55 () (_ FP 8 24) (+ .3 .50 .54))
(define-fun .57 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.259000003337860107422))
(define-fun .58 () (_ FP 8 24) (* .3 .26 .57))
(define-fun .59 () (_ FP 8 24) (+ .3 .55 .58))
(define-fun .61 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.754999995231628417969))
(define-fun .62 () (_ FP 8 24) (* .3 .30 .61))
(define-fun .63 () (_ FP 8 24) (+ .3 .59 .62))
(define-fun .64 () Bool (<= .40 .63))
(assert .64)
(define-fun .66 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.742999970912933349609))
(define-fun .68 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00700000021606683731079))
(define-fun .69 () (_ FP 8 24) (* .3 .14 .68))
(define-fun .70 () (_ FP 8 24) (+ .3 .12 .69))
(define-fun .73 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.166999995708465576172)))
(define-fun .74 () (_ FP 8 24) (* .3 .18 .73))
(define-fun .75 () (_ FP 8 24) (+ .3 .70 .74))
(define-fun .78 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.661000013351440429688)))
(define-fun .79 () (_ FP 8 24) (* .3 .22 .78))
(define-fun .80 () (_ FP 8 24) (+ .3 .75 .79))
(define-fun .83 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.126000002026557922363)))
(define-fun .84 () (_ FP 8 24) (* .3 .26 .83))
(define-fun .85 () (_ FP 8 24) (+ .3 .80 .84))
(define-fun .88 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.584999978542327880859)))
(define-fun .89 () (_ FP 8 24) (* .3 .30 .88))
(define-fun .90 () (_ FP 8 24) (+ .3 .85 .89))
(define-fun .91 () Bool (<= .66 .90))
(assert .91)
(define-fun .93 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.894999980926513671875))
(define-fun .95 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.111000001430511474609))
(define-fun .96 () (_ FP 8 24) (* .3 .14 .95))
(define-fun .97 () (_ FP 8 24) (+ .3 .12 .96))
(define-fun .100 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.493000000715255737305)))
(define-fun .101 () (_ FP 8 24) (* .3 .18 .100))
(define-fun .102 () (_ FP 8 24) (+ .3 .97 .101))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.432999998331069946289)))
(define-fun .106 () (_ FP 8 24) (* .3 .22 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .102 .106))
(define-fun .109 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0860000029206275939941))
(define-fun .110 () (_ FP 8 24) (* .3 .26 .109))
(define-fun .111 () (_ FP 8 24) (+ .3 .107 .110))
(define-fun .114 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.665000021457672119141)))
(define-fun .115 () (_ FP 8 24) (* .3 .30 .114))
(define-fun .116 () (_ FP 8 24) (+ .3 .111 .115))
(define-fun .117 () Bool (<= .116 .93))
(assert .117)
(define-fun .119 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.649999976158142089844))
(define-fun .121 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.435000002384185791016))
(define-fun .122 () (_ FP 8 24) (* .3 .14 .121))
(define-fun .123 () (_ FP 8 24) (+ .3 .12 .122))
(define-fun .126 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0680000036954879760742)))
(define-fun .127 () (_ FP 8 24) (* .3 .18 .126))
(define-fun .128 () (_ FP 8 24) (+ .3 .123 .127))
(define-fun .131 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.340999990701675415039)))
(define-fun .132 () (_ FP 8 24) (* .3 .22 .131))
(define-fun .133 () (_ FP 8 24) (+ .3 .128 .132))
(define-fun .134 () (_ FP 8 24) (* .3 .26 .43))
(define-fun .135 () (_ FP 8 24) (+ .3 .133 .134))
(define-fun .138 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.972000002861022949219)))
(define-fun .139 () (_ FP 8 24) (* .3 .30 .138))
(define-fun .140 () (_ FP 8 24) (+ .3 .135 .139))
(define-fun .141 () Bool (<= .119 .140))
(assert .141)
(define-fun .143 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.172999992966651916504))
(define-fun .146 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.625)))
(define-fun .147 () (_ FP 8 24) (* .3 .14 .146))
(define-fun .148 () (_ FP 8 24) (+ .3 .12 .147))
(define-fun .150 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.501999974250793457031))
(define-fun .151 () (_ FP 8 24) (* .3 .18 .150))
(define-fun .152 () (_ FP 8 24) (+ .3 .148 .151))
(define-fun .155 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0199999995529651641846)))
(define-fun .156 () (_ FP 8 24) (* .3 .22 .155))
(define-fun .157 () (_ FP 8 24) (+ .3 .152 .156))
(define-fun .160 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0320000015199184417725)))
(define-fun .161 () (_ FP 8 24) (* .3 .26 .160))
(define-fun .162 () (_ FP 8 24) (+ .3 .157 .161))
(define-fun .165 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0630000010132789611816)))
(define-fun .166 () (_ FP 8 24) (* .3 .30 .165))
(define-fun .167 () (_ FP 8 24) (+ .3 .162 .166))
(define-fun .168 () Bool (<= .143 .167))
(assert .168)
(check-sat)
