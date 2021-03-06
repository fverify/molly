(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(declare-fun x3 () (_ FP 8 24))
(declare-fun x4 () (_ FP 8 24))
(declare-fun x5 () (_ FP 8 24))
(declare-fun x6 () (_ FP 8 24))
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
(define-fun .34 () (_ FP 8 24) x5)
(define-fun .35 () Bool (<= .13 .34))
(define-fun .36 () Bool (<= .34 .10))
(define-fun .37 () Bool (and .35 .36))
(assert .37)
(define-fun .38 () (_ FP 8 24) x6)
(define-fun .39 () Bool (<= .13 .38))
(define-fun .40 () Bool (<= .38 .10))
(define-fun .41 () Bool (and .39 .40))
(assert .41)
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .12 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0))
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.71700000762939453125)))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.714999973773956298828))
(define-fun .51 () (_ FP 8 24) (* .3 .14 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .12 .51))
(define-fun .55 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.994000017642974853516)))
(define-fun .56 () (_ FP 8 24) (* .3 .18 .55))
(define-fun .57 () (_ FP 8 24) (+ .3 .52 .56))
(define-fun .59 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.181999996304512023926))
(define-fun .60 () (_ FP 8 24) (* .3 .22 .59))
(define-fun .61 () (_ FP 8 24) (+ .3 .57 .60))
(define-fun .64 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.137999996542930603027)))
(define-fun .65 () (_ FP 8 24) (* .3 .26 .64))
(define-fun .66 () (_ FP 8 24) (+ .3 .61 .65))
(define-fun .68 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.449999988079071044922))
(define-fun .69 () (_ FP 8 24) (* .3 .30 .68))
(define-fun .70 () (_ FP 8 24) (+ .3 .66 .69))
(define-fun .72 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.483999997377395629883))
(define-fun .73 () (_ FP 8 24) (* .3 .34 .72))
(define-fun .74 () (_ FP 8 24) (+ .3 .70 .73))
(define-fun .76 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.638999998569488525391))
(define-fun .77 () (_ FP 8 24) (* .3 .38 .76))
(define-fun .78 () (_ FP 8 24) (+ .3 .74 .77))
(define-fun .79 () Bool (<= .78 .48))
(assert .79)
(define-fun .82 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.303999990224838256836)))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.308999985456466674805)))
(define-fun .86 () (_ FP 8 24) (* .3 .14 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .12 .86))
(define-fun .89 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0670000016689300537109))
(define-fun .90 () (_ FP 8 24) (* .3 .18 .89))
(define-fun .91 () (_ FP 8 24) (+ .3 .87 .90))
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.172000005841255187988)))
(define-fun .95 () (_ FP 8 24) (* .3 .22 .94))
(define-fun .96 () (_ FP 8 24) (+ .3 .91 .95))
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.490000009536743164063)))
(define-fun .100 () (_ FP 8 24) (* .3 .26 .99))
(define-fun .101 () (_ FP 8 24) (+ .3 .96 .100))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.949000000953674316406))
(define-fun .104 () (_ FP 8 24) (* .3 .30 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .101 .104))
(define-fun .108 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.637000024318695068359)))
(define-fun .109 () (_ FP 8 24) (* .3 .34 .108))
(define-fun .110 () (_ FP 8 24) (+ .3 .105 .109))
(define-fun .113 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.677999973297119140625)))
(define-fun .114 () (_ FP 8 24) (* .3 .38 .113))
(define-fun .115 () (_ FP 8 24) (+ .3 .110 .114))
(define-fun .116 () Bool (<= .115 .82))
(assert .116)
(define-fun .119 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.442999988794326782227)))
(define-fun .121 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.572000026702880859375))
(define-fun .122 () (_ FP 8 24) (* .3 .14 .121))
(define-fun .123 () (_ FP 8 24) (+ .3 .12 .122))
(define-fun .125 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.623000025749206542969))
(define-fun .126 () (_ FP 8 24) (* .3 .18 .125))
(define-fun .127 () (_ FP 8 24) (+ .3 .123 .126))
(define-fun .130 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.409000009298324584961)))
(define-fun .131 () (_ FP 8 24) (* .3 .22 .130))
(define-fun .132 () (_ FP 8 24) (+ .3 .127 .131))
(define-fun .135 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.317999988794326782227)))
(define-fun .136 () (_ FP 8 24) (* .3 .26 .135))
(define-fun .137 () (_ FP 8 24) (+ .3 .132 .136))
(define-fun .140 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.070000000298023223877)))
(define-fun .141 () (_ FP 8 24) (* .3 .30 .140))
(define-fun .142 () (_ FP 8 24) (+ .3 .137 .141))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.237000003457069396973))
(define-fun .145 () (_ FP 8 24) (* .3 .34 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .142 .145))
(define-fun .149 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.114000000059604644775)))
(define-fun .150 () (_ FP 8 24) (* .3 .38 .149))
(define-fun .151 () (_ FP 8 24) (+ .3 .146 .150))
(define-fun .152 () Bool (<= .151 .119))
(assert .152)
(define-fun .154 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0630000010132789611816))
(define-fun .156 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.561999976634979248047))
(define-fun .157 () (_ FP 8 24) (* .3 .14 .156))
(define-fun .158 () (_ FP 8 24) (+ .3 .12 .157))
(define-fun .160 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.867999970912933349609))
(define-fun .161 () (_ FP 8 24) (* .3 .18 .160))
(define-fun .162 () (_ FP 8 24) (+ .3 .158 .161))
(define-fun .165 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.342999994754791259766)))
(define-fun .166 () (_ FP 8 24) (* .3 .22 .165))
(define-fun .167 () (_ FP 8 24) (+ .3 .162 .166))
(define-fun .170 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.759000003337860107422)))
(define-fun .171 () (_ FP 8 24) (* .3 .26 .170))
(define-fun .172 () (_ FP 8 24) (+ .3 .167 .171))
(define-fun .174 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.764999985694885253906))
(define-fun .175 () (_ FP 8 24) (* .3 .30 .174))
(define-fun .176 () (_ FP 8 24) (+ .3 .172 .175))
(define-fun .179 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.778999984264373779297)))
(define-fun .180 () (_ FP 8 24) (* .3 .34 .179))
(define-fun .181 () (_ FP 8 24) (+ .3 .176 .180))
(define-fun .183 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.976999998092651367188))
(define-fun .184 () (_ FP 8 24) (* .3 .38 .183))
(define-fun .185 () (_ FP 8 24) (+ .3 .181 .184))
(define-fun .186 () Bool (<= .154 .185))
(assert .186)
(define-fun .189 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.171000003814697265625)))
(define-fun .192 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.722000002861022949219)))
(define-fun .193 () (_ FP 8 24) (* .3 .14 .192))
(define-fun .194 () (_ FP 8 24) (+ .3 .12 .193))
(define-fun .197 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.574000000953674316406)))
(define-fun .198 () (_ FP 8 24) (* .3 .18 .197))
(define-fun .199 () (_ FP 8 24) (+ .3 .194 .198))
(define-fun .202 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.34200000762939453125)))
(define-fun .203 () (_ FP 8 24) (* .3 .22 .202))
(define-fun .204 () (_ FP 8 24) (+ .3 .199 .203))
(define-fun .207 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.984000027179718017578)))
(define-fun .208 () (_ FP 8 24) (* .3 .26 .207))
(define-fun .209 () (_ FP 8 24) (+ .3 .204 .208))
(define-fun .211 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.632000029087066650391))
(define-fun .212 () (_ FP 8 24) (* .3 .30 .211))
(define-fun .213 () (_ FP 8 24) (+ .3 .209 .212))
(define-fun .216 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.358000010251998901367)))
(define-fun .217 () (_ FP 8 24) (* .3 .34 .216))
(define-fun .218 () (_ FP 8 24) (+ .3 .213 .217))
(define-fun .221 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.521000027656555175781)))
(define-fun .222 () (_ FP 8 24) (* .3 .38 .221))
(define-fun .223 () (_ FP 8 24) (+ .3 .218 .222))
(define-fun .224 () Bool (<= .223 .189))
(assert .224)
(define-fun .227 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.273000001907348632813)))
(define-fun .229 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.374000012874603271484))
(define-fun .230 () (_ FP 8 24) (* .3 .14 .229))
(define-fun .231 () (_ FP 8 24) (+ .3 .12 .230))
(define-fun .234 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.111000001430511474609)))
(define-fun .235 () (_ FP 8 24) (* .3 .18 .234))
(define-fun .236 () (_ FP 8 24) (+ .3 .231 .235))
(define-fun .239 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.446000009775161743164)))
(define-fun .240 () (_ FP 8 24) (* .3 .22 .239))
(define-fun .241 () (_ FP 8 24) (+ .3 .236 .240))
(define-fun .243 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.398999989032745361328))
(define-fun .244 () (_ FP 8 24) (* .3 .26 .243))
(define-fun .245 () (_ FP 8 24) (+ .3 .241 .244))
(define-fun .248 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.680000007152557373047)))
(define-fun .249 () (_ FP 8 24) (* .3 .30 .248))
(define-fun .250 () (_ FP 8 24) (+ .3 .245 .249))
(define-fun .253 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.187999993562698364258)))
(define-fun .254 () (_ FP 8 24) (* .3 .34 .253))
(define-fun .255 () (_ FP 8 24) (+ .3 .250 .254))
(define-fun .258 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.135000005364418029785)))
(define-fun .259 () (_ FP 8 24) (* .3 .38 .258))
(define-fun .260 () (_ FP 8 24) (+ .3 .255 .259))
(define-fun .261 () Bool (<= .260 .227))
(assert .261)
(define-fun .264 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.569000005722045898438)))
(define-fun .267 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.225999996066093444824)))
(define-fun .268 () (_ FP 8 24) (* .3 .14 .267))
(define-fun .269 () (_ FP 8 24) (+ .3 .12 .268))
(define-fun .271 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.736000001430511474609))
(define-fun .272 () (_ FP 8 24) (* .3 .18 .271))
(define-fun .273 () (_ FP 8 24) (+ .3 .269 .272))
(define-fun .275 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.382999986410140991211))
(define-fun .276 () (_ FP 8 24) (* .3 .22 .275))
(define-fun .277 () (_ FP 8 24) (+ .3 .273 .276))
(define-fun .279 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.708999991416931152344))
(define-fun .280 () (_ FP 8 24) (* .3 .26 .279))
(define-fun .281 () (_ FP 8 24) (+ .3 .277 .280))
(define-fun .284 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.712000012397766113281)))
(define-fun .285 () (_ FP 8 24) (* .3 .30 .284))
(define-fun .286 () (_ FP 8 24) (+ .3 .281 .285))
(define-fun .289 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0460000000894069671631)))
(define-fun .290 () (_ FP 8 24) (* .3 .34 .289))
(define-fun .291 () (_ FP 8 24) (+ .3 .286 .290))
(define-fun .294 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.470999985933303833008)))
(define-fun .295 () (_ FP 8 24) (* .3 .38 .294))
(define-fun .296 () (_ FP 8 24) (+ .3 .291 .295))
(define-fun .297 () Bool (<= .264 .296))
(assert .297)
(check-sat)
