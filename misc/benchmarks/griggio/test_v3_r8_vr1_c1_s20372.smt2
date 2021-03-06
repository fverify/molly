(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
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
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .12 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0))
(define-fun .32 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.21400000154972076416)))
(define-fun .34 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.975000023841857910156))
(define-fun .35 () (_ FP 8 24) (* .3 .14 .34))
(define-fun .36 () (_ FP 8 24) (+ .3 .12 .35))
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0309999994933605194092)))
(define-fun .40 () (_ FP 8 24) (* .3 .18 .39))
(define-fun .41 () (_ FP 8 24) (+ .3 .36 .40))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.885999977588653564453))
(define-fun .44 () (_ FP 8 24) (* .3 .22 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .41 .44))
(define-fun .46 () Bool (<= .32 .45))
(assert .46)
(define-fun .49 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.537999987602233886719)))
(define-fun .51 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.869000017642974853516))
(define-fun .52 () (_ FP 8 24) (* .3 .14 .51))
(define-fun .53 () (_ FP 8 24) (+ .3 .12 .52))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.52600002288818359375)))
(define-fun .57 () (_ FP 8 24) (* .3 .18 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .53 .57))
(define-fun .60 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.856000006198883056641))
(define-fun .61 () (_ FP 8 24) (* .3 .22 .60))
(define-fun .62 () (_ FP 8 24) (+ .3 .58 .61))
(define-fun .63 () Bool (<= .62 .49))
(assert .63)
(define-fun .65 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.725000023841857910156))
(define-fun .67 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.945999979972839355469))
(define-fun .68 () (_ FP 8 24) (* .3 .14 .67))
(define-fun .69 () (_ FP 8 24) (+ .3 .12 .68))
(define-fun .72 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.224000006914138793945)))
(define-fun .73 () (_ FP 8 24) (* .3 .18 .72))
(define-fun .74 () (_ FP 8 24) (+ .3 .69 .73))
(define-fun .77 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.363999992609024047852)))
(define-fun .78 () (_ FP 8 24) (* .3 .22 .77))
(define-fun .79 () (_ FP 8 24) (+ .3 .74 .78))
(define-fun .80 () Bool (<= .65 .79))
(assert .80)
(define-fun .82 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.219999998807907104492))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.266000002622604370117)))
(define-fun .86 () (_ FP 8 24) (* .3 .14 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .12 .86))
(define-fun .89 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.628000020980834960938))
(define-fun .90 () (_ FP 8 24) (* .3 .18 .89))
(define-fun .91 () (_ FP 8 24) (+ .3 .87 .90))
(define-fun .93 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.90799999237060546875))
(define-fun .94 () (_ FP 8 24) (* .3 .22 .93))
(define-fun .95 () (_ FP 8 24) (+ .3 .91 .94))
(define-fun .96 () Bool (<= .82 .95))
(assert .96)
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.711000025272369384766)))
(define-fun .101 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.241999998688697814941))
(define-fun .102 () (_ FP 8 24) (* .3 .14 .101))
(define-fun .103 () (_ FP 8 24) (+ .3 .12 .102))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.398999989032745361328))
(define-fun .106 () (_ FP 8 24) (* .3 .18 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .103 .106))
(define-fun .109 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.182999998331069946289))
(define-fun .110 () (_ FP 8 24) (* .3 .22 .109))
(define-fun .111 () (_ FP 8 24) (+ .3 .107 .110))
(define-fun .112 () Bool (<= .99 .111))
(assert .112)
(define-fun .115 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.563000023365020751953)))
(define-fun .118 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.508000016212463378906)))
(define-fun .119 () (_ FP 8 24) (* .3 .14 .118))
(define-fun .120 () (_ FP 8 24) (+ .3 .12 .119))
(define-fun .122 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.20000000298023223877))
(define-fun .123 () (_ FP 8 24) (* .3 .18 .122))
(define-fun .124 () (_ FP 8 24) (+ .3 .120 .123))
(define-fun .126 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.310999989509582519531))
(define-fun .127 () (_ FP 8 24) (* .3 .22 .126))
(define-fun .128 () (_ FP 8 24) (+ .3 .124 .127))
(define-fun .129 () Bool (<= .115 .128))
(assert .129)
(define-fun .132 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.188999995589256286621)))
(define-fun .135 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0230000000447034835815)))
(define-fun .136 () (_ FP 8 24) (* .3 .14 .135))
(define-fun .137 () (_ FP 8 24) (+ .3 .12 .136))
(define-fun .140 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.745999991893768310547)))
(define-fun .141 () (_ FP 8 24) (* .3 .18 .140))
(define-fun .142 () (_ FP 8 24) (+ .3 .137 .141))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.861999988555908203125))
(define-fun .145 () (_ FP 8 24) (* .3 .22 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .142 .145))
(define-fun .147 () Bool (<= .146 .132))
(assert .147)
(define-fun .150 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.920000016689300537109)))
(define-fun .153 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.456999987363815307617)))
(define-fun .154 () (_ FP 8 24) (* .3 .14 .153))
(define-fun .155 () (_ FP 8 24) (+ .3 .12 .154))
(define-fun .157 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.884000003337860107422))
(define-fun .158 () (_ FP 8 24) (* .3 .18 .157))
(define-fun .159 () (_ FP 8 24) (+ .3 .155 .158))
(define-fun .161 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.305000007152557373047))
(define-fun .162 () (_ FP 8 24) (* .3 .22 .161))
(define-fun .163 () (_ FP 8 24) (+ .3 .159 .162))
(define-fun .164 () Bool (<= .163 .150))
(assert .164)
(check-sat)
