(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(declare-fun x3 () (_ FP 8 24))
(declare-fun x4 () (_ FP 8 24))
(declare-fun x5 () (_ FP 8 24))
(declare-fun x6 () (_ FP 8 24))
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
(define-fun .47 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.8159999847412109375))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.238000005483627319336)))
(define-fun .51 () (_ FP 8 24) (* .3 .14 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .12 .51))
(define-fun .55 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.158999994397163391113)))
(define-fun .56 () (_ FP 8 24) (* .3 .18 .55))
(define-fun .57 () (_ FP 8 24) (+ .3 .52 .56))
(define-fun .59 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.855000019073486328125))
(define-fun .60 () (_ FP 8 24) (* .3 .22 .59))
(define-fun .61 () (_ FP 8 24) (+ .3 .57 .60))
(define-fun .63 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.389999985694885253906))
(define-fun .64 () (_ FP 8 24) (* .3 .26 .63))
(define-fun .65 () (_ FP 8 24) (+ .3 .61 .64))
(define-fun .68 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.382999986410140991211)))
(define-fun .69 () (_ FP 8 24) (* .3 .30 .68))
(define-fun .70 () (_ FP 8 24) (+ .3 .65 .69))
(define-fun .72 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.181999996304512023926))
(define-fun .73 () (_ FP 8 24) (* .3 .34 .72))
(define-fun .74 () (_ FP 8 24) (+ .3 .70 .73))
(define-fun .77 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.652999997138977050781)))
(define-fun .78 () (_ FP 8 24) (* .3 .38 .77))
(define-fun .79 () (_ FP 8 24) (+ .3 .74 .78))
(define-fun .80 () Bool (<= .47 .79))
(assert .80)
(define-fun .82 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.563000023365020751953))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.681999981403350830078)))
(define-fun .86 () (_ FP 8 24) (* .3 .14 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .12 .86))
(define-fun .89 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.987999975681304931641))
(define-fun .90 () (_ FP 8 24) (* .3 .18 .89))
(define-fun .91 () (_ FP 8 24) (+ .3 .87 .90))
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.688000023365020751953)))
(define-fun .95 () (_ FP 8 24) (* .3 .22 .94))
(define-fun .96 () (_ FP 8 24) (+ .3 .91 .95))
(define-fun .98 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.851000010967254638672))
(define-fun .99 () (_ FP 8 24) (* .3 .26 .98))
(define-fun .100 () (_ FP 8 24) (+ .3 .96 .99))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.307000011205673217773)))
(define-fun .104 () (_ FP 8 24) (* .3 .30 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .100 .104))
(define-fun .107 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.137999996542930603027))
(define-fun .108 () (_ FP 8 24) (* .3 .34 .107))
(define-fun .109 () (_ FP 8 24) (+ .3 .105 .108))
(define-fun .111 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.19699999690055847168))
(define-fun .112 () (_ FP 8 24) (* .3 .38 .111))
(define-fun .113 () (_ FP 8 24) (+ .3 .109 .112))
(define-fun .114 () Bool (<= .113 .82))
(assert .114)
(define-fun .116 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0350000001490116119385))
(define-fun .119 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0329999998211860656738)))
(define-fun .120 () (_ FP 8 24) (* .3 .14 .119))
(define-fun .121 () (_ FP 8 24) (+ .3 .12 .120))
(define-fun .123 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.72399997711181640625))
(define-fun .124 () (_ FP 8 24) (* .3 .18 .123))
(define-fun .125 () (_ FP 8 24) (+ .3 .121 .124))
(define-fun .128 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.773999989032745361328)))
(define-fun .129 () (_ FP 8 24) (* .3 .22 .128))
(define-fun .130 () (_ FP 8 24) (+ .3 .125 .129))
(define-fun .132 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.209000006318092346191))
(define-fun .133 () (_ FP 8 24) (* .3 .26 .132))
(define-fun .134 () (_ FP 8 24) (+ .3 .130 .133))
(define-fun .137 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.490999996662139892578)))
(define-fun .138 () (_ FP 8 24) (* .3 .30 .137))
(define-fun .139 () (_ FP 8 24) (+ .3 .134 .138))
(define-fun .142 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.337999999523162841797)))
(define-fun .143 () (_ FP 8 24) (* .3 .34 .142))
(define-fun .144 () (_ FP 8 24) (+ .3 .139 .143))
(define-fun .147 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.27000001072883605957)))
(define-fun .148 () (_ FP 8 24) (* .3 .38 .147))
(define-fun .149 () (_ FP 8 24) (+ .3 .144 .148))
(define-fun .150 () Bool (<= .149 .116))
(assert .150)
(define-fun .152 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.372000008821487426758))
(define-fun .154 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.17499999701976776123))
(define-fun .155 () (_ FP 8 24) (* .3 .14 .154))
(define-fun .156 () (_ FP 8 24) (+ .3 .12 .155))
(define-fun .158 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0920000001788139343262))
(define-fun .159 () (_ FP 8 24) (* .3 .18 .158))
(define-fun .160 () (_ FP 8 24) (+ .3 .156 .159))
(define-fun .162 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0450000017881393432617))
(define-fun .163 () (_ FP 8 24) (* .3 .22 .162))
(define-fun .164 () (_ FP 8 24) (+ .3 .160 .163))
(define-fun .166 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.879999995231628417969))
(define-fun .167 () (_ FP 8 24) (* .3 .26 .166))
(define-fun .168 () (_ FP 8 24) (+ .3 .164 .167))
(define-fun .170 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.726000010967254638672))
(define-fun .171 () (_ FP 8 24) (* .3 .30 .170))
(define-fun .172 () (_ FP 8 24) (+ .3 .168 .171))
(define-fun .174 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.935999989509582519531))
(define-fun .175 () (_ FP 8 24) (* .3 .34 .174))
(define-fun .176 () (_ FP 8 24) (+ .3 .172 .175))
(define-fun .179 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.287000000476837158203)))
(define-fun .180 () (_ FP 8 24) (* .3 .38 .179))
(define-fun .181 () (_ FP 8 24) (+ .3 .176 .180))
(define-fun .182 () Bool (<= .181 .152))
(assert .182)
(define-fun .184 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.157000005245208740234))
(define-fun .187 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.801999986171722412109)))
(define-fun .188 () (_ FP 8 24) (* .3 .14 .187))
(define-fun .189 () (_ FP 8 24) (+ .3 .12 .188))
(define-fun .191 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0719999969005584716797))
(define-fun .192 () (_ FP 8 24) (* .3 .18 .191))
(define-fun .193 () (_ FP 8 24) (+ .3 .189 .192))
(define-fun .196 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.223000004887580871582)))
(define-fun .197 () (_ FP 8 24) (* .3 .22 .196))
(define-fun .198 () (_ FP 8 24) (+ .3 .193 .197))
(define-fun .201 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.569999992847442626953)))
(define-fun .202 () (_ FP 8 24) (* .3 .26 .201))
(define-fun .203 () (_ FP 8 24) (+ .3 .198 .202))
(define-fun .206 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0860000029206275939941)))
(define-fun .207 () (_ FP 8 24) (* .3 .30 .206))
(define-fun .208 () (_ FP 8 24) (+ .3 .203 .207))
(define-fun .210 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.800000011920928955078))
(define-fun .211 () (_ FP 8 24) (* .3 .34 .210))
(define-fun .212 () (_ FP 8 24) (+ .3 .208 .211))
(define-fun .214 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.925999999046325683594))
(define-fun .215 () (_ FP 8 24) (* .3 .38 .214))
(define-fun .216 () (_ FP 8 24) (+ .3 .212 .215))
(define-fun .217 () Bool (<= .184 .216))
(assert .217)
(define-fun .219 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.968999981880187988281))
(define-fun .222 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.707000017166137695313)))
(define-fun .223 () (_ FP 8 24) (* .3 .14 .222))
(define-fun .224 () (_ FP 8 24) (+ .3 .12 .223))
(define-fun .226 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.833000004291534423828))
(define-fun .227 () (_ FP 8 24) (* .3 .18 .226))
(define-fun .228 () (_ FP 8 24) (+ .3 .224 .227))
(define-fun .231 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.703000009059906005859)))
(define-fun .232 () (_ FP 8 24) (* .3 .22 .231))
(define-fun .233 () (_ FP 8 24) (+ .3 .228 .232))
(define-fun .236 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.240999996662139892578)))
(define-fun .237 () (_ FP 8 24) (* .3 .26 .236))
(define-fun .238 () (_ FP 8 24) (+ .3 .233 .237))
(define-fun .240 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0820000022649765014648))
(define-fun .241 () (_ FP 8 24) (* .3 .30 .240))
(define-fun .242 () (_ FP 8 24) (+ .3 .238 .241))
(define-fun .245 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0810000002384185791016)))
(define-fun .246 () (_ FP 8 24) (* .3 .34 .245))
(define-fun .247 () (_ FP 8 24) (+ .3 .242 .246))
(define-fun .250 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.935000002384185791016)))
(define-fun .251 () (_ FP 8 24) (* .3 .38 .250))
(define-fun .252 () (_ FP 8 24) (+ .3 .247 .251))
(define-fun .253 () Bool (<= .219 .252))
(assert .253)
(define-fun .256 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.527999997138977050781)))
(define-fun .258 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.5590000152587890625))
(define-fun .259 () (_ FP 8 24) (* .3 .14 .258))
(define-fun .260 () (_ FP 8 24) (+ .3 .12 .259))
(define-fun .261 () (_ FP 8 24) (* .3 .18 .258))
(define-fun .262 () (_ FP 8 24) (+ .3 .260 .261))
(define-fun .264 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.486999988555908203125))
(define-fun .265 () (_ FP 8 24) (* .3 .22 .264))
(define-fun .266 () (_ FP 8 24) (+ .3 .262 .265))
(define-fun .269 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.391999989748001098633)))
(define-fun .270 () (_ FP 8 24) (* .3 .26 .269))
(define-fun .271 () (_ FP 8 24) (+ .3 .266 .270))
(define-fun .274 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.377999991178512573242)))
(define-fun .275 () (_ FP 8 24) (* .3 .30 .274))
(define-fun .276 () (_ FP 8 24) (+ .3 .271 .275))
(define-fun .278 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.625999987125396728516))
(define-fun .279 () (_ FP 8 24) (* .3 .34 .278))
(define-fun .280 () (_ FP 8 24) (+ .3 .276 .279))
(define-fun .283 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.351999998092651367188)))
(define-fun .284 () (_ FP 8 24) (* .3 .38 .283))
(define-fun .285 () (_ FP 8 24) (+ .3 .280 .284))
(define-fun .286 () Bool (<= .285 .256))
(assert .286)
(define-fun .289 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.472000002861022949219)))
(define-fun .291 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.884000003337860107422))
(define-fun .292 () (_ FP 8 24) (* .3 .14 .291))
(define-fun .293 () (_ FP 8 24) (+ .3 .12 .292))
(define-fun .296 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.661000013351440429688)))
(define-fun .297 () (_ FP 8 24) (* .3 .18 .296))
(define-fun .298 () (_ FP 8 24) (+ .3 .293 .297))
(define-fun .300 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.131999999284744262695))
(define-fun .301 () (_ FP 8 24) (* .3 .22 .300))
(define-fun .302 () (_ FP 8 24) (+ .3 .298 .301))
(define-fun .304 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.799000024795532226563))
(define-fun .305 () (_ FP 8 24) (* .3 .26 .304))
(define-fun .306 () (_ FP 8 24) (+ .3 .302 .305))
(define-fun .309 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.172999992966651916504)))
(define-fun .310 () (_ FP 8 24) (* .3 .30 .309))
(define-fun .311 () (_ FP 8 24) (+ .3 .306 .310))
(define-fun .314 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.977999985218048095703)))
(define-fun .315 () (_ FP 8 24) (* .3 .34 .314))
(define-fun .316 () (_ FP 8 24) (+ .3 .311 .315))
(define-fun .319 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.052000001072883605957)))
(define-fun .320 () (_ FP 8 24) (* .3 .38 .319))
(define-fun .321 () (_ FP 8 24) (+ .3 .316 .320))
(define-fun .322 () Bool (<= .289 .321))
(assert .322)
(define-fun .325 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.643999993801116943359)))
(define-fun .327 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0949999988079071044922))
(define-fun .328 () (_ FP 8 24) (* .3 .14 .327))
(define-fun .329 () (_ FP 8 24) (+ .3 .12 .328))
(define-fun .332 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.796000003814697265625)))
(define-fun .333 () (_ FP 8 24) (* .3 .18 .332))
(define-fun .334 () (_ FP 8 24) (+ .3 .329 .333))
(define-fun .337 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.116999998688697814941)))
(define-fun .338 () (_ FP 8 24) (* .3 .22 .337))
(define-fun .339 () (_ FP 8 24) (+ .3 .334 .338))
(define-fun .342 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.606000006198883056641)))
(define-fun .343 () (_ FP 8 24) (* .3 .26 .342))
(define-fun .344 () (_ FP 8 24) (+ .3 .339 .343))
(define-fun .346 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.133000001311302185059))
(define-fun .347 () (_ FP 8 24) (* .3 .30 .346))
(define-fun .348 () (_ FP 8 24) (+ .3 .344 .347))
(define-fun .351 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.708000004291534423828)))
(define-fun .352 () (_ FP 8 24) (* .3 .34 .351))
(define-fun .353 () (_ FP 8 24) (+ .3 .348 .352))
(define-fun .355 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00100000004749745130539))
(define-fun .356 () (_ FP 8 24) (* .3 .38 .355))
(define-fun .357 () (_ FP 8 24) (+ .3 .353 .356))
(define-fun .358 () Bool (<= .357 .325))
(assert .358)
(define-fun .361 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.728999972343444824219)))
(define-fun .363 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.463999986648559570313))
(define-fun .364 () (_ FP 8 24) (* .3 .14 .363))
(define-fun .365 () (_ FP 8 24) (+ .3 .12 .364))
(define-fun .368 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.194999992847442626953)))
(define-fun .369 () (_ FP 8 24) (* .3 .18 .368))
(define-fun .370 () (_ FP 8 24) (+ .3 .365 .369))
(define-fun .373 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.185000002384185791016)))
(define-fun .374 () (_ FP 8 24) (* .3 .22 .373))
(define-fun .375 () (_ FP 8 24) (+ .3 .370 .374))
(define-fun .377 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.284000009298324584961))
(define-fun .378 () (_ FP 8 24) (* .3 .26 .377))
(define-fun .379 () (_ FP 8 24) (+ .3 .375 .378))
(define-fun .382 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.544000029563903808594)))
(define-fun .383 () (_ FP 8 24) (* .3 .30 .382))
(define-fun .384 () (_ FP 8 24) (+ .3 .379 .383))
(define-fun .386 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.644999980926513671875))
(define-fun .387 () (_ FP 8 24) (* .3 .34 .386))
(define-fun .388 () (_ FP 8 24) (+ .3 .384 .387))
(define-fun .391 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.150999993085861206055)))
(define-fun .392 () (_ FP 8 24) (* .3 .38 .391))
(define-fun .393 () (_ FP 8 24) (+ .3 .388 .392))
(define-fun .394 () Bool (<= .393 .361))
(assert .394)
(define-fun .397 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.12800000607967376709)))
(define-fun .400 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00600000005215406417847)))
(define-fun .401 () (_ FP 8 24) (* .3 .14 .400))
(define-fun .402 () (_ FP 8 24) (+ .3 .12 .401))
(define-fun .405 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.736000001430511474609)))
(define-fun .406 () (_ FP 8 24) (* .3 .18 .405))
(define-fun .407 () (_ FP 8 24) (+ .3 .402 .406))
(define-fun .409 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.679000020027160644531))
(define-fun .410 () (_ FP 8 24) (* .3 .22 .409))
(define-fun .411 () (_ FP 8 24) (+ .3 .407 .410))
(define-fun .413 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.134000003337860107422))
(define-fun .414 () (_ FP 8 24) (* .3 .26 .413))
(define-fun .415 () (_ FP 8 24) (+ .3 .411 .414))
(define-fun .417 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.843999981880187988281))
(define-fun .418 () (_ FP 8 24) (* .3 .30 .417))
(define-fun .419 () (_ FP 8 24) (+ .3 .415 .418))
(define-fun .422 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.208000004291534423828)))
(define-fun .423 () (_ FP 8 24) (* .3 .34 .422))
(define-fun .424 () (_ FP 8 24) (+ .3 .419 .423))
(define-fun .426 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.17800000309944152832))
(define-fun .427 () (_ FP 8 24) (* .3 .38 .426))
(define-fun .428 () (_ FP 8 24) (+ .3 .424 .427))
(define-fun .429 () Bool (<= .397 .428))
(assert .429)
(define-fun .432 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.545000016689300537109)))
(define-fun .435 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.84899997711181640625)))
(define-fun .436 () (_ FP 8 24) (* .3 .14 .435))
(define-fun .437 () (_ FP 8 24) (+ .3 .12 .436))
(define-fun .440 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.518000006675720214844)))
(define-fun .441 () (_ FP 8 24) (* .3 .18 .440))
(define-fun .442 () (_ FP 8 24) (+ .3 .437 .441))
(define-fun .445 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.298999994993209838867)))
(define-fun .446 () (_ FP 8 24) (* .3 .22 .445))
(define-fun .447 () (_ FP 8 24) (+ .3 .442 .446))
(define-fun .450 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.455000013113021850586)))
(define-fun .451 () (_ FP 8 24) (* .3 .26 .450))
(define-fun .452 () (_ FP 8 24) (+ .3 .447 .451))
(define-fun .454 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.234999999403953552246))
(define-fun .455 () (_ FP 8 24) (* .3 .30 .454))
(define-fun .456 () (_ FP 8 24) (+ .3 .452 .455))
(define-fun .459 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.561999976634979248047)))
(define-fun .460 () (_ FP 8 24) (* .3 .34 .459))
(define-fun .461 () (_ FP 8 24) (+ .3 .456 .460))
(define-fun .464 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.254999995231628417969)))
(define-fun .465 () (_ FP 8 24) (* .3 .38 .464))
(define-fun .466 () (_ FP 8 24) (+ .3 .461 .465))
(define-fun .467 () Bool (<= .432 .466))
(assert .467)
(define-fun .470 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.640999972820281982422)))
(define-fun .472 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.510999977588653564453))
(define-fun .473 () (_ FP 8 24) (* .3 .14 .472))
(define-fun .474 () (_ FP 8 24) (+ .3 .12 .473))
(define-fun .477 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.499000012874603271484)))
(define-fun .478 () (_ FP 8 24) (* .3 .18 .477))
(define-fun .479 () (_ FP 8 24) (+ .3 .474 .478))
(define-fun .481 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.8090000152587890625))
(define-fun .482 () (_ FP 8 24) (* .3 .22 .481))
(define-fun .483 () (_ FP 8 24) (+ .3 .479 .482))
(define-fun .484 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.884000003337860107422)))
(define-fun .485 () (_ FP 8 24) (* .3 .26 .484))
(define-fun .486 () (_ FP 8 24) (+ .3 .483 .485))
(define-fun .488 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0480000004172325134277))
(define-fun .489 () (_ FP 8 24) (* .3 .30 .488))
(define-fun .490 () (_ FP 8 24) (+ .3 .486 .489))
(define-fun .493 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.430000007152557373047)))
(define-fun .494 () (_ FP 8 24) (* .3 .34 .493))
(define-fun .495 () (_ FP 8 24) (+ .3 .490 .494))
(define-fun .498 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0160000007599592208862)))
(define-fun .499 () (_ FP 8 24) (* .3 .38 .498))
(define-fun .500 () (_ FP 8 24) (+ .3 .495 .499))
(define-fun .501 () Bool (<= .470 .500))
(assert .501)
(define-fun .503 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.108999997377395629883))
(define-fun .506 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.189999997615814208984)))
(define-fun .507 () (_ FP 8 24) (* .3 .14 .506))
(define-fun .508 () (_ FP 8 24) (+ .3 .12 .507))
(define-fun .510 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.432999998331069946289))
(define-fun .511 () (_ FP 8 24) (* .3 .18 .510))
(define-fun .512 () (_ FP 8 24) (+ .3 .508 .511))
(define-fun .514 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.913999974727630615234))
(define-fun .515 () (_ FP 8 24) (* .3 .22 .514))
(define-fun .516 () (_ FP 8 24) (+ .3 .512 .515))
(define-fun .519 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.584999978542327880859)))
(define-fun .520 () (_ FP 8 24) (* .3 .26 .519))
(define-fun .521 () (_ FP 8 24) (+ .3 .516 .520))
(define-fun .524 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.791000008583068847656)))
(define-fun .525 () (_ FP 8 24) (* .3 .30 .524))
(define-fun .526 () (_ FP 8 24) (+ .3 .521 .525))
(define-fun .529 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0599999986588954925537)))
(define-fun .530 () (_ FP 8 24) (* .3 .34 .529))
(define-fun .531 () (_ FP 8 24) (+ .3 .526 .530))
(define-fun .533 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.230000004172325134277))
(define-fun .534 () (_ FP 8 24) (* .3 .38 .533))
(define-fun .535 () (_ FP 8 24) (+ .3 .531 .534))
(define-fun .536 () Bool (<= .535 .503))
(assert .536)
(define-fun .539 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.560999989509582519531)))
(define-fun .541 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.861000001430511474609))
(define-fun .542 () (_ FP 8 24) (* .3 .14 .541))
(define-fun .543 () (_ FP 8 24) (+ .3 .12 .542))
(define-fun .545 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.851999998092651367188))
(define-fun .546 () (_ FP 8 24) (* .3 .18 .545))
(define-fun .547 () (_ FP 8 24) (+ .3 .543 .546))
(define-fun .550 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.388999998569488525391)))
(define-fun .551 () (_ FP 8 24) (* .3 .22 .550))
(define-fun .552 () (_ FP 8 24) (+ .3 .547 .551))
(define-fun .555 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.374000012874603271484)))
(define-fun .556 () (_ FP 8 24) (* .3 .26 .555))
(define-fun .557 () (_ FP 8 24) (+ .3 .552 .556))
(define-fun .559 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.177000001072883605957))
(define-fun .560 () (_ FP 8 24) (* .3 .30 .559))
(define-fun .561 () (_ FP 8 24) (+ .3 .557 .560))
(define-fun .563 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.405999988317489624023))
(define-fun .564 () (_ FP 8 24) (* .3 .34 .563))
(define-fun .565 () (_ FP 8 24) (+ .3 .561 .564))
(define-fun .567 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.411000013351440429688))
(define-fun .568 () (_ FP 8 24) (* .3 .38 .567))
(define-fun .569 () (_ FP 8 24) (+ .3 .565 .568))
(define-fun .570 () Bool (<= .569 .539))
(assert .570)
(define-fun .572 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.201000005006790161133))
(define-fun .574 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.847999989986419677734))
(define-fun .575 () (_ FP 8 24) (* .3 .14 .574))
(define-fun .576 () (_ FP 8 24) (+ .3 .12 .575))
(define-fun .579 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.555999994277954101563)))
(define-fun .580 () (_ FP 8 24) (* .3 .18 .579))
(define-fun .581 () (_ FP 8 24) (+ .3 .576 .580))
(define-fun .584 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.135000005364418029785)))
(define-fun .585 () (_ FP 8 24) (* .3 .22 .584))
(define-fun .586 () (_ FP 8 24) (+ .3 .581 .585))
(define-fun .587 () (_ FP 8 24) (* .3 .26 .550))
(define-fun .588 () (_ FP 8 24) (+ .3 .586 .587))
(define-fun .591 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.550000011920928955078)))
(define-fun .592 () (_ FP 8 24) (* .3 .30 .591))
(define-fun .593 () (_ FP 8 24) (+ .3 .588 .592))
(define-fun .596 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.209999993443489074707)))
(define-fun .597 () (_ FP 8 24) (* .3 .34 .596))
(define-fun .598 () (_ FP 8 24) (+ .3 .593 .597))
(define-fun .600 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.39500001072883605957))
(define-fun .601 () (_ FP 8 24) (* .3 .38 .600))
(define-fun .602 () (_ FP 8 24) (+ .3 .598 .601))
(define-fun .603 () Bool (<= .602 .572))
(assert .603)
(define-fun .186 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.801999986171722412109))
(define-fun .605 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.773000001907348632813))
(define-fun .606 () (_ FP 8 24) (* .3 .14 .309))
(define-fun .607 () (_ FP 8 24) (+ .3 .12 .606))
(define-fun .609 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0130000002682209014893))
(define-fun .610 () (_ FP 8 24) (* .3 .18 .609))
(define-fun .611 () (_ FP 8 24) (+ .3 .607 .610))
(define-fun .612 () (_ FP 8 24) (* .3 .22 .454))
(define-fun .613 () (_ FP 8 24) (+ .3 .611 .612))
(define-fun .615 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.675000011920928955078))
(define-fun .616 () (_ FP 8 24) (* .3 .26 .615))
(define-fun .617 () (_ FP 8 24) (+ .3 .613 .616))
(define-fun .618 () (_ FP 8 24) (* .3 .30 .186))
(define-fun .619 () (_ FP 8 24) (+ .3 .617 .618))
(define-fun .621 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.241999998688697814941))
(define-fun .622 () (_ FP 8 24) (* .3 .34 .621))
(define-fun .623 () (_ FP 8 24) (+ .3 .619 .622))
(define-fun .626 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.654999971389770507813)))
(define-fun .627 () (_ FP 8 24) (* .3 .38 .626))
(define-fun .628 () (_ FP 8 24) (+ .3 .623 .627))
(define-fun .629 () Bool (<= .605 .628))
(assert .629)
(check-sat)
