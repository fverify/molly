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
(define-fun .40 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.527000010013580322266)))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.21099999547004699707)))
(define-fun .44 () (_ FP 8 24) (* .3 .14 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .12 .44))
(define-fun .47 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.746999979019165039063))
(define-fun .48 () (_ FP 8 24) (* .3 .18 .47))
(define-fun .49 () (_ FP 8 24) (+ .3 .45 .48))
(define-fun .52 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.497000008821487426758)))
(define-fun .53 () (_ FP 8 24) (* .3 .22 .52))
(define-fun .54 () (_ FP 8 24) (+ .3 .49 .53))
(define-fun .57 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.773999989032745361328)))
(define-fun .58 () (_ FP 8 24) (* .3 .26 .57))
(define-fun .59 () (_ FP 8 24) (+ .3 .54 .58))
(define-fun .62 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.610000014305114746094)))
(define-fun .63 () (_ FP 8 24) (* .3 .30 .62))
(define-fun .64 () (_ FP 8 24) (+ .3 .59 .63))
(define-fun .65 () Bool (<= .40 .64))
(assert .65)
(define-fun .67 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00200000009499490261078))
(define-fun .70 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.707000017166137695313)))
(define-fun .71 () (_ FP 8 24) (* .3 .14 .70))
(define-fun .72 () (_ FP 8 24) (+ .3 .12 .71))
(define-fun .74 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.46099999547004699707))
(define-fun .75 () (_ FP 8 24) (* .3 .18 .74))
(define-fun .76 () (_ FP 8 24) (+ .3 .72 .75))
(define-fun .79 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0270000007003545761108)))
(define-fun .80 () (_ FP 8 24) (* .3 .22 .79))
(define-fun .81 () (_ FP 8 24) (+ .3 .76 .80))
(define-fun .84 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0280000008642673492432)))
(define-fun .85 () (_ FP 8 24) (* .3 .26 .84))
(define-fun .86 () (_ FP 8 24) (+ .3 .81 .85))
(define-fun .88 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0450000017881393432617))
(define-fun .89 () (_ FP 8 24) (* .3 .30 .88))
(define-fun .90 () (_ FP 8 24) (+ .3 .86 .89))
(define-fun .91 () Bool (<= .67 .90))
(assert .91)
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.319000005722045898438)))
(define-fun .97 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.488000005483627319336)))
(define-fun .98 () (_ FP 8 24) (* .3 .14 .97))
(define-fun .99 () (_ FP 8 24) (+ .3 .12 .98))
(define-fun .101 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.902999997138977050781))
(define-fun .102 () (_ FP 8 24) (* .3 .18 .101))
(define-fun .103 () (_ FP 8 24) (+ .3 .99 .102))
(define-fun .106 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.84899997711181640625)))
(define-fun .107 () (_ FP 8 24) (* .3 .22 .106))
(define-fun .108 () (_ FP 8 24) (+ .3 .103 .107))
(define-fun .111 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.892000019550323486328)))
(define-fun .112 () (_ FP 8 24) (* .3 .26 .111))
(define-fun .113 () (_ FP 8 24) (+ .3 .108 .112))
(define-fun .116 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.675000011920928955078)))
(define-fun .117 () (_ FP 8 24) (* .3 .30 .116))
(define-fun .118 () (_ FP 8 24) (+ .3 .113 .117))
(define-fun .119 () Bool (<= .118 .94))
(assert .119)
(define-fun .121 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.753000020980834960938))
(define-fun .124 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.884999990463256835938)))
(define-fun .125 () (_ FP 8 24) (* .3 .14 .124))
(define-fun .126 () (_ FP 8 24) (+ .3 .12 .125))
(define-fun .129 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.564999997615814208984)))
(define-fun .130 () (_ FP 8 24) (* .3 .18 .129))
(define-fun .131 () (_ FP 8 24) (+ .3 .126 .130))
(define-fun .134 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.931999981403350830078)))
(define-fun .135 () (_ FP 8 24) (* .3 .22 .134))
(define-fun .136 () (_ FP 8 24) (+ .3 .131 .135))
(define-fun .139 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.409000009298324584961)))
(define-fun .140 () (_ FP 8 24) (* .3 .26 .139))
(define-fun .141 () (_ FP 8 24) (+ .3 .136 .140))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0460000000894069671631)))
(define-fun .145 () (_ FP 8 24) (* .3 .30 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .141 .145))
(define-fun .147 () Bool (<= .121 .146))
(assert .147)
(define-fun .150 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.270999997854232788086)))
(define-fun .152 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.216000005602836608887))
(define-fun .153 () (_ FP 8 24) (* .3 .14 .152))
(define-fun .154 () (_ FP 8 24) (+ .3 .12 .153))
(define-fun .157 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.998000025749206542969)))
(define-fun .158 () (_ FP 8 24) (* .3 .18 .157))
(define-fun .159 () (_ FP 8 24) (+ .3 .154 .158))
(define-fun .161 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.070000000298023223877))
(define-fun .162 () (_ FP 8 24) (* .3 .22 .161))
(define-fun .163 () (_ FP 8 24) (+ .3 .159 .162))
(define-fun .165 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.305000007152557373047))
(define-fun .166 () (_ FP 8 24) (* .3 .26 .165))
(define-fun .167 () (_ FP 8 24) (+ .3 .163 .166))
(define-fun .169 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.796000003814697265625))
(define-fun .170 () (_ FP 8 24) (* .3 .30 .169))
(define-fun .171 () (_ FP 8 24) (+ .3 .167 .170))
(define-fun .172 () Bool (<= .150 .171))
(assert .172)
(define-fun .175 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.925999999046325683594)))
(define-fun .177 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.180999994277954101563))
(define-fun .178 () (_ FP 8 24) (* .3 .14 .177))
(define-fun .179 () (_ FP 8 24) (+ .3 .12 .178))
(define-fun .182 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.978999972343444824219)))
(define-fun .183 () (_ FP 8 24) (* .3 .18 .182))
(define-fun .184 () (_ FP 8 24) (+ .3 .179 .183))
(define-fun .187 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.853999972343444824219)))
(define-fun .188 () (_ FP 8 24) (* .3 .22 .187))
(define-fun .189 () (_ FP 8 24) (+ .3 .184 .188))
(define-fun .192 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.712000012397766113281)))
(define-fun .193 () (_ FP 8 24) (* .3 .26 .192))
(define-fun .194 () (_ FP 8 24) (+ .3 .189 .193))
(define-fun .197 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0900000035762786865234)))
(define-fun .198 () (_ FP 8 24) (* .3 .30 .197))
(define-fun .199 () (_ FP 8 24) (+ .3 .194 .198))
(define-fun .200 () Bool (<= .199 .175))
(assert .200)
(define-fun .203 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0149999996647238731384)))
(define-fun .205 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.635999977588653564453))
(define-fun .206 () (_ FP 8 24) (* .3 .14 .205))
(define-fun .207 () (_ FP 8 24) (+ .3 .12 .206))
(define-fun .209 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.279000014066696166992))
(define-fun .210 () (_ FP 8 24) (* .3 .18 .209))
(define-fun .211 () (_ FP 8 24) (+ .3 .207 .210))
(define-fun .213 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.637000024318695068359))
(define-fun .214 () (_ FP 8 24) (* .3 .22 .213))
(define-fun .215 () (_ FP 8 24) (+ .3 .211 .214))
(define-fun .218 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.755999982357025146484)))
(define-fun .219 () (_ FP 8 24) (* .3 .26 .218))
(define-fun .220 () (_ FP 8 24) (+ .3 .215 .219))
(define-fun .222 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.474999994039535522461))
(define-fun .223 () (_ FP 8 24) (* .3 .30 .222))
(define-fun .224 () (_ FP 8 24) (+ .3 .220 .223))
(define-fun .225 () Bool (<= .224 .203))
(assert .225)
(define-fun .227 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.101000003516674041748))
(define-fun .230 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.138999998569488525391)))
(define-fun .231 () (_ FP 8 24) (* .3 .14 .230))
(define-fun .232 () (_ FP 8 24) (+ .3 .12 .231))
(define-fun .235 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.310000002384185791016)))
(define-fun .236 () (_ FP 8 24) (* .3 .18 .235))
(define-fun .237 () (_ FP 8 24) (+ .3 .232 .236))
(define-fun .240 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.412000000476837158203)))
(define-fun .241 () (_ FP 8 24) (* .3 .22 .240))
(define-fun .242 () (_ FP 8 24) (+ .3 .237 .241))
(define-fun .244 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.620000004768371582031))
(define-fun .245 () (_ FP 8 24) (* .3 .26 .244))
(define-fun .246 () (_ FP 8 24) (+ .3 .242 .245))
(define-fun .248 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.642000019550323486328))
(define-fun .249 () (_ FP 8 24) (* .3 .30 .248))
(define-fun .250 () (_ FP 8 24) (+ .3 .246 .249))
(define-fun .251 () Bool (<= .227 .250))
(assert .251)
(define-fun .253 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.248999997973442077637))
(define-fun .255 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.451000005006790161133))
(define-fun .256 () (_ FP 8 24) (* .3 .14 .255))
(define-fun .257 () (_ FP 8 24) (+ .3 .12 .256))
(define-fun .260 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.337000012397766113281)))
(define-fun .261 () (_ FP 8 24) (* .3 .18 .260))
(define-fun .262 () (_ FP 8 24) (+ .3 .257 .261))
(define-fun .264 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.187000006437301635742))
(define-fun .265 () (_ FP 8 24) (* .3 .22 .264))
(define-fun .266 () (_ FP 8 24) (+ .3 .262 .265))
(define-fun .268 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.601999998092651367188))
(define-fun .269 () (_ FP 8 24) (* .3 .26 .268))
(define-fun .270 () (_ FP 8 24) (+ .3 .266 .269))
(define-fun .272 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.504999995231628417969))
(define-fun .273 () (_ FP 8 24) (* .3 .30 .272))
(define-fun .274 () (_ FP 8 24) (+ .3 .270 .273))
(define-fun .275 () Bool (<= .274 .253))
(assert .275)
(define-fun .278 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.472999989986419677734)))
(define-fun .281 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.670000016689300537109)))
(define-fun .282 () (_ FP 8 24) (* .3 .14 .281))
(define-fun .283 () (_ FP 8 24) (+ .3 .12 .282))
(define-fun .286 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.75)))
(define-fun .287 () (_ FP 8 24) (* .3 .18 .286))
(define-fun .288 () (_ FP 8 24) (+ .3 .283 .287))
(define-fun .291 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.231999993324279785156)))
(define-fun .292 () (_ FP 8 24) (* .3 .22 .291))
(define-fun .293 () (_ FP 8 24) (+ .3 .288 .292))
(define-fun .295 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.771000027656555175781))
(define-fun .296 () (_ FP 8 24) (* .3 .26 .295))
(define-fun .297 () (_ FP 8 24) (+ .3 .293 .296))
(define-fun .299 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.128999993205070495605))
(define-fun .300 () (_ FP 8 24) (* .3 .30 .299))
(define-fun .301 () (_ FP 8 24) (+ .3 .297 .300))
(define-fun .302 () Bool (<= .278 .301))
(assert .302)
(define-fun .304 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.202999994158744812012))
(define-fun .305 () (_ FP 8 24) (* .3 .14 .304))
(define-fun .306 () (_ FP 8 24) (+ .3 .12 .305))
(define-fun .308 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.143000006675720214844))
(define-fun .309 () (_ FP 8 24) (* .3 .18 .308))
(define-fun .310 () (_ FP 8 24) (+ .3 .306 .309))
(define-fun .312 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0810000002384185791016))
(define-fun .313 () (_ FP 8 24) (* .3 .22 .312))
(define-fun .314 () (_ FP 8 24) (+ .3 .310 .313))
(define-fun .315 () (_ FP 8 24) (* .3 .26 .152))
(define-fun .316 () (_ FP 8 24) (+ .3 .314 .315))
(define-fun .318 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.259000003337860107422))
(define-fun .319 () (_ FP 8 24) (* .3 .30 .318))
(define-fun .320 () (_ FP 8 24) (+ .3 .316 .319))
(define-fun .321 () Bool (<= .209 .320))
(assert .321)
(define-fun .323 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.342999994754791259766))
(define-fun .325 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.363999992609024047852))
(define-fun .326 () (_ FP 8 24) (* .3 .14 .325))
(define-fun .327 () (_ FP 8 24) (+ .3 .12 .326))
(define-fun .328 () (_ FP 8 24) (+ .3 .102 .327))
(define-fun .331 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.722999989986419677734)))
(define-fun .332 () (_ FP 8 24) (* .3 .22 .331))
(define-fun .333 () (_ FP 8 24) (+ .3 .328 .332))
(define-fun .335 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0769999995827674865723))
(define-fun .336 () (_ FP 8 24) (* .3 .26 .335))
(define-fun .337 () (_ FP 8 24) (+ .3 .333 .336))
(define-fun .339 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.275999993085861206055))
(define-fun .340 () (_ FP 8 24) (* .3 .30 .339))
(define-fun .341 () (_ FP 8 24) (+ .3 .337 .340))
(define-fun .342 () Bool (<= .323 .341))
(assert .342)
(define-fun .345 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.331000000238418579102)))
(define-fun .348 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.14200000464916229248)))
(define-fun .349 () (_ FP 8 24) (* .3 .14 .348))
(define-fun .350 () (_ FP 8 24) (+ .3 .12 .349))
(define-fun .353 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.666000008583068847656)))
(define-fun .354 () (_ FP 8 24) (* .3 .18 .353))
(define-fun .355 () (_ FP 8 24) (+ .3 .350 .354))
(define-fun .357 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.333999991416931152344))
(define-fun .358 () (_ FP 8 24) (* .3 .22 .357))
(define-fun .359 () (_ FP 8 24) (+ .3 .355 .358))
(define-fun .362 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.884000003337860107422)))
(define-fun .363 () (_ FP 8 24) (* .3 .26 .362))
(define-fun .364 () (_ FP 8 24) (+ .3 .359 .363))
(define-fun .367 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.264999985694885253906)))
(define-fun .368 () (_ FP 8 24) (* .3 .30 .367))
(define-fun .369 () (_ FP 8 24) (+ .3 .364 .368))
(define-fun .370 () Bool (<= .345 .369))
(assert .370)
(define-fun .143 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0460000000894069671631))
(define-fun .372 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.203999996185302734375))
(define-fun .375 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.261000007390975952148)))
(define-fun .376 () (_ FP 8 24) (* .3 .14 .375))
(define-fun .377 () (_ FP 8 24) (+ .3 .12 .376))
(define-fun .379 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.587000012397766113281))
(define-fun .380 () (_ FP 8 24) (* .3 .18 .379))
(define-fun .381 () (_ FP 8 24) (+ .3 .377 .380))
(define-fun .382 () (_ FP 8 24) (* .3 .22 .143))
(define-fun .383 () (_ FP 8 24) (+ .3 .381 .382))
(define-fun .386 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0209999997168779373169)))
(define-fun .387 () (_ FP 8 24) (* .3 .26 .386))
(define-fun .388 () (_ FP 8 24) (+ .3 .383 .387))
(define-fun .391 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.172999992966651916504)))
(define-fun .392 () (_ FP 8 24) (* .3 .30 .391))
(define-fun .393 () (_ FP 8 24) (+ .3 .388 .392))
(define-fun .394 () Bool (<= .393 .372))
(assert .394)
(define-fun .397 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.409999996423721313477)))
(define-fun .399 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0340000018477439880371))
(define-fun .400 () (_ FP 8 24) (* .3 .14 .399))
(define-fun .401 () (_ FP 8 24) (+ .3 .12 .400))
(define-fun .402 () (_ FP 8 24) (* .3 .18 .345))
(define-fun .403 () (_ FP 8 24) (+ .3 .401 .402))
(define-fun .406 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.225999996066093444824)))
(define-fun .407 () (_ FP 8 24) (* .3 .22 .406))
(define-fun .408 () (_ FP 8 24) (+ .3 .403 .407))
(define-fun .411 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.9340000152587890625)))
(define-fun .412 () (_ FP 8 24) (* .3 .26 .411))
(define-fun .413 () (_ FP 8 24) (+ .3 .408 .412))
(define-fun .415 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.856000006198883056641))
(define-fun .416 () (_ FP 8 24) (* .3 .30 .415))
(define-fun .417 () (_ FP 8 24) (+ .3 .413 .416))
(define-fun .418 () Bool (<= .397 .417))
(assert .418)
(check-sat)
