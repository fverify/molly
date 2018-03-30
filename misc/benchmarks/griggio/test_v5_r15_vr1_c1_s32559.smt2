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
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.138999998569488525391))
(define-fun .41 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.225999996066093444824))
(define-fun .42 () (_ FP 8 24) (* .3 .14 .41))
(define-fun .43 () (_ FP 8 24) (+ .3 .12 .42))
(define-fun .46 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.556999981403350830078)))
(define-fun .47 () (_ FP 8 24) (* .3 .18 .46))
(define-fun .48 () (_ FP 8 24) (+ .3 .43 .47))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.787999987602233886719))
(define-fun .51 () (_ FP 8 24) (* .3 .22 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .48 .51))
(define-fun .55 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.136999994516372680664)))
(define-fun .56 () (_ FP 8 24) (* .3 .26 .55))
(define-fun .57 () (_ FP 8 24) (+ .3 .52 .56))
(define-fun .58 () (_ FP 8 24) (* .3 .12 .30))
(define-fun .59 () (_ FP 8 24) (+ .3 .57 .58))
(define-fun .60 () Bool (<= .39 .59))
(assert .60)
(define-fun .62 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.497999995946884155273))
(define-fun .65 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.962000012397766113281)))
(define-fun .66 () (_ FP 8 24) (* .3 .14 .65))
(define-fun .67 () (_ FP 8 24) (+ .3 .12 .66))
(define-fun .70 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.857999980449676513672)))
(define-fun .71 () (_ FP 8 24) (* .3 .18 .70))
(define-fun .72 () (_ FP 8 24) (+ .3 .67 .71))
(define-fun .75 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0879999995231628417969)))
(define-fun .76 () (_ FP 8 24) (* .3 .22 .75))
(define-fun .77 () (_ FP 8 24) (+ .3 .72 .76))
(define-fun .80 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.671999990940093994141)))
(define-fun .81 () (_ FP 8 24) (* .3 .26 .80))
(define-fun .82 () (_ FP 8 24) (+ .3 .77 .81))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.916000008583068847656)))
(define-fun .86 () (_ FP 8 24) (* .3 .30 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .82 .86))
(define-fun .88 () Bool (<= .62 .87))
(assert .88)
(define-fun .91 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.670000016689300537109)))
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.547999978065490722656)))
(define-fun .95 () (_ FP 8 24) (* .3 .14 .94))
(define-fun .96 () (_ FP 8 24) (+ .3 .12 .95))
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.217999994754791259766)))
(define-fun .100 () (_ FP 8 24) (* .3 .18 .99))
(define-fun .101 () (_ FP 8 24) (+ .3 .96 .100))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.393999993801116943359))
(define-fun .104 () (_ FP 8 24) (* .3 .22 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .101 .104))
(define-fun .107 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.377999991178512573242))
(define-fun .108 () (_ FP 8 24) (* .3 .26 .107))
(define-fun .109 () (_ FP 8 24) (+ .3 .105 .108))
(define-fun .110 () (_ FP 8 24) (* .3 .30 .75))
(define-fun .111 () (_ FP 8 24) (+ .3 .109 .110))
(define-fun .112 () Bool (<= .111 .91))
(assert .112)
(define-fun .114 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.544000029563903808594))
(define-fun .117 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.42800000309944152832)))
(define-fun .118 () (_ FP 8 24) (* .3 .14 .117))
(define-fun .119 () (_ FP 8 24) (+ .3 .12 .118))
(define-fun .122 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.583000004291534423828)))
(define-fun .123 () (_ FP 8 24) (* .3 .18 .122))
(define-fun .124 () (_ FP 8 24) (+ .3 .119 .123))
(define-fun .126 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.279000014066696166992))
(define-fun .127 () (_ FP 8 24) (* .3 .22 .126))
(define-fun .128 () (_ FP 8 24) (+ .3 .124 .127))
(define-fun .130 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.145999997854232788086))
(define-fun .131 () (_ FP 8 24) (* .3 .26 .130))
(define-fun .132 () (_ FP 8 24) (+ .3 .128 .131))
(define-fun .135 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.177000001072883605957)))
(define-fun .136 () (_ FP 8 24) (* .3 .30 .135))
(define-fun .137 () (_ FP 8 24) (+ .3 .132 .136))
(define-fun .138 () Bool (<= .114 .137))
(assert .138)
(define-fun .141 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.168999999761581420898)))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.975000023841857910156)))
(define-fun .145 () (_ FP 8 24) (* .3 .14 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .12 .145))
(define-fun .149 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.925000011920928955078)))
(define-fun .150 () (_ FP 8 24) (* .3 .18 .149))
(define-fun .151 () (_ FP 8 24) (+ .3 .146 .150))
(define-fun .153 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.987999975681304931641))
(define-fun .154 () (_ FP 8 24) (* .3 .22 .153))
(define-fun .155 () (_ FP 8 24) (+ .3 .151 .154))
(define-fun .158 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.28900000452995300293)))
(define-fun .159 () (_ FP 8 24) (* .3 .26 .158))
(define-fun .160 () (_ FP 8 24) (+ .3 .155 .159))
(define-fun .163 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.755999982357025146484)))
(define-fun .164 () (_ FP 8 24) (* .3 .30 .163))
(define-fun .165 () (_ FP 8 24) (+ .3 .160 .164))
(define-fun .166 () Bool (<= .141 .165))
(assert .166)
(define-fun .169 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.656000018119812011719)))
(define-fun .171 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.381999999284744262695))
(define-fun .172 () (_ FP 8 24) (* .3 .14 .171))
(define-fun .173 () (_ FP 8 24) (+ .3 .12 .172))
(define-fun .175 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.330000013113021850586))
(define-fun .176 () (_ FP 8 24) (* .3 .18 .175))
(define-fun .177 () (_ FP 8 24) (+ .3 .173 .176))
(define-fun .179 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.887000024318695068359))
(define-fun .180 () (_ FP 8 24) (* .3 .22 .179))
(define-fun .181 () (_ FP 8 24) (+ .3 .177 .180))
(define-fun .183 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.623000025749206542969))
(define-fun .184 () (_ FP 8 24) (* .3 .26 .183))
(define-fun .185 () (_ FP 8 24) (+ .3 .181 .184))
(define-fun .187 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.560000002384185791016))
(define-fun .188 () (_ FP 8 24) (* .3 .30 .187))
(define-fun .189 () (_ FP 8 24) (+ .3 .185 .188))
(define-fun .190 () Bool (<= .189 .169))
(assert .190)
(define-fun .192 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.802999973297119140625))
(define-fun .194 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.505999982357025146484))
(define-fun .195 () (_ FP 8 24) (* .3 .14 .194))
(define-fun .196 () (_ FP 8 24) (+ .3 .12 .195))
(define-fun .199 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0829999968409538269043)))
(define-fun .200 () (_ FP 8 24) (* .3 .18 .199))
(define-fun .201 () (_ FP 8 24) (+ .3 .196 .200))
(define-fun .204 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.606000006198883056641)))
(define-fun .205 () (_ FP 8 24) (* .3 .22 .204))
(define-fun .206 () (_ FP 8 24) (+ .3 .201 .205))
(define-fun .208 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.907000005245208740234))
(define-fun .209 () (_ FP 8 24) (* .3 .26 .208))
(define-fun .210 () (_ FP 8 24) (+ .3 .206 .209))
(define-fun .213 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.347999989986419677734)))
(define-fun .214 () (_ FP 8 24) (* .3 .30 .213))
(define-fun .215 () (_ FP 8 24) (+ .3 .210 .214))
(define-fun .216 () Bool (<= .215 .192))
(assert .216)
(define-fun .218 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.574999988079071044922))
(define-fun .221 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.101999998092651367188)))
(define-fun .222 () (_ FP 8 24) (* .3 .14 .221))
(define-fun .223 () (_ FP 8 24) (+ .3 .12 .222))
(define-fun .226 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0989999994635581970215)))
(define-fun .227 () (_ FP 8 24) (* .3 .18 .226))
(define-fun .228 () (_ FP 8 24) (+ .3 .223 .227))
(define-fun .230 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.449000000953674316406))
(define-fun .231 () (_ FP 8 24) (* .3 .22 .230))
(define-fun .232 () (_ FP 8 24) (+ .3 .228 .231))
(define-fun .235 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.601000010967254638672)))
(define-fun .236 () (_ FP 8 24) (* .3 .26 .235))
(define-fun .237 () (_ FP 8 24) (+ .3 .232 .236))
(define-fun .240 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.46700000762939453125)))
(define-fun .241 () (_ FP 8 24) (* .3 .30 .240))
(define-fun .242 () (_ FP 8 24) (+ .3 .237 .241))
(define-fun .243 () Bool (<= .242 .218))
(assert .243)
(define-fun .245 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.197999998927116394043))
(define-fun .247 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.943000018596649169922))
(define-fun .248 () (_ FP 8 24) (* .3 .14 .247))
(define-fun .249 () (_ FP 8 24) (+ .3 .12 .248))
(define-fun .251 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.333999991416931152344))
(define-fun .252 () (_ FP 8 24) (* .3 .18 .251))
(define-fun .253 () (_ FP 8 24) (+ .3 .249 .252))
(define-fun .255 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.173999994993209838867))
(define-fun .256 () (_ FP 8 24) (* .3 .22 .255))
(define-fun .257 () (_ FP 8 24) (+ .3 .253 .256))
(define-fun .259 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.722999989986419677734))
(define-fun .260 () (_ FP 8 24) (* .3 .26 .259))
(define-fun .261 () (_ FP 8 24) (+ .3 .257 .260))
(define-fun .264 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.538999974727630615234)))
(define-fun .265 () (_ FP 8 24) (* .3 .30 .264))
(define-fun .266 () (_ FP 8 24) (+ .3 .261 .265))
(define-fun .267 () Bool (<= .266 .245))
(assert .267)
(define-fun .270 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0209999997168779373169)))
(define-fun .273 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.360000014305114746094)))
(define-fun .274 () (_ FP 8 24) (* .3 .14 .273))
(define-fun .275 () (_ FP 8 24) (+ .3 .12 .274))
(define-fun .278 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.592999994754791259766)))
(define-fun .279 () (_ FP 8 24) (* .3 .18 .278))
(define-fun .280 () (_ FP 8 24) (+ .3 .275 .279))
(define-fun .283 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.643000006675720214844)))
(define-fun .284 () (_ FP 8 24) (* .3 .22 .283))
(define-fun .285 () (_ FP 8 24) (+ .3 .280 .284))
(define-fun .287 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.757000029087066650391))
(define-fun .288 () (_ FP 8 24) (* .3 .26 .287))
(define-fun .289 () (_ FP 8 24) (+ .3 .285 .288))
(define-fun .291 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.978999972343444824219))
(define-fun .292 () (_ FP 8 24) (* .3 .30 .291))
(define-fun .293 () (_ FP 8 24) (+ .3 .289 .292))
(define-fun .294 () Bool (<= .293 .270))
(assert .294)
(define-fun .296 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.425999999046325683594))
(define-fun .299 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.860000014305114746094)))
(define-fun .300 () (_ FP 8 24) (* .3 .14 .299))
(define-fun .301 () (_ FP 8 24) (+ .3 .12 .300))
(define-fun .304 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.542999982833862304688)))
(define-fun .305 () (_ FP 8 24) (* .3 .18 .304))
(define-fun .306 () (_ FP 8 24) (+ .3 .301 .305))
(define-fun .308 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.509999990463256835938))
(define-fun .309 () (_ FP 8 24) (* .3 .22 .308))
(define-fun .310 () (_ FP 8 24) (+ .3 .306 .309))
(define-fun .313 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.20000000298023223877)))
(define-fun .314 () (_ FP 8 24) (* .3 .26 .313))
(define-fun .315 () (_ FP 8 24) (+ .3 .310 .314))
(define-fun .317 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.884000003337860107422))
(define-fun .318 () (_ FP 8 24) (* .3 .30 .317))
(define-fun .319 () (_ FP 8 24) (+ .3 .315 .318))
(define-fun .320 () Bool (<= .319 .296))
(assert .320)
(define-fun .322 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.476000010967254638672))
(define-fun .324 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.824000000953674316406))
(define-fun .325 () (_ FP 8 24) (* .3 .14 .324))
(define-fun .326 () (_ FP 8 24) (+ .3 .12 .325))
(define-fun .328 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.532000005245208740234))
(define-fun .329 () (_ FP 8 24) (* .3 .18 .328))
(define-fun .330 () (_ FP 8 24) (+ .3 .326 .329))
(define-fun .332 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.871999979019165039063))
(define-fun .333 () (_ FP 8 24) (* .3 .22 .332))
(define-fun .334 () (_ FP 8 24) (+ .3 .330 .333))
(define-fun .337 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.118000000715255737305)))
(define-fun .338 () (_ FP 8 24) (* .3 .26 .337))
(define-fun .339 () (_ FP 8 24) (+ .3 .334 .338))
(define-fun .342 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.175999999046325683594)))
(define-fun .343 () (_ FP 8 24) (* .3 .30 .342))
(define-fun .344 () (_ FP 8 24) (+ .3 .339 .343))
(define-fun .345 () Bool (<= .344 .322))
(assert .345)
(define-fun .347 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0179999992251396179199))
(define-fun .349 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.970000028610229492188))
(define-fun .350 () (_ FP 8 24) (* .3 .14 .349))
(define-fun .351 () (_ FP 8 24) (+ .3 .12 .350))
(define-fun .354 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.291999995708465576172)))
(define-fun .355 () (_ FP 8 24) (* .3 .18 .354))
(define-fun .356 () (_ FP 8 24) (+ .3 .351 .355))
(define-fun .359 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.744000017642974853516)))
(define-fun .360 () (_ FP 8 24) (* .3 .22 .359))
(define-fun .361 () (_ FP 8 24) (+ .3 .356 .360))
(define-fun .363 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.170000001788139343262))
(define-fun .364 () (_ FP 8 24) (* .3 .26 .363))
(define-fun .365 () (_ FP 8 24) (+ .3 .361 .364))
(define-fun .368 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0740000009536743164063)))
(define-fun .369 () (_ FP 8 24) (* .3 .30 .368))
(define-fun .370 () (_ FP 8 24) (+ .3 .365 .369))
(define-fun .371 () Bool (<= .370 .347))
(assert .371)
(define-fun .148 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.925000011920928955078))
(define-fun .373 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.845000028610229492188))
(define-fun .376 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.739000022411346435547)))
(define-fun .377 () (_ FP 8 24) (* .3 .14 .376))
(define-fun .378 () (_ FP 8 24) (+ .3 .12 .377))
(define-fun .381 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0900000035762786865234)))
(define-fun .382 () (_ FP 8 24) (* .3 .18 .381))
(define-fun .383 () (_ FP 8 24) (+ .3 .378 .382))
(define-fun .384 () (_ FP 8 24) (* .3 .22 .148))
(define-fun .385 () (_ FP 8 24) (+ .3 .383 .384))
(define-fun .387 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.193000003695487976074))
(define-fun .388 () (_ FP 8 24) (* .3 .26 .387))
(define-fun .389 () (_ FP 8 24) (+ .3 .385 .388))
(define-fun .391 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.467999994754791259766))
(define-fun .392 () (_ FP 8 24) (* .3 .30 .391))
(define-fun .393 () (_ FP 8 24) (+ .3 .389 .392))
(define-fun .394 () Bool (<= .373 .393))
(assert .394)
(define-fun .397 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.474000006914138793945)))
(define-fun .400 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0189999993890523910522)))
(define-fun .401 () (_ FP 8 24) (* .3 .14 .400))
(define-fun .402 () (_ FP 8 24) (+ .3 .12 .401))
(define-fun .404 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.111000001430511474609))
(define-fun .405 () (_ FP 8 24) (* .3 .18 .404))
(define-fun .406 () (_ FP 8 24) (+ .3 .402 .405))
(define-fun .409 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.77600002288818359375)))
(define-fun .410 () (_ FP 8 24) (* .3 .22 .409))
(define-fun .411 () (_ FP 8 24) (+ .3 .406 .410))
(define-fun .414 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.870999991893768310547)))
(define-fun .415 () (_ FP 8 24) (* .3 .26 .414))
(define-fun .416 () (_ FP 8 24) (+ .3 .411 .415))
(define-fun .419 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.23299999535083770752)))
(define-fun .420 () (_ FP 8 24) (* .3 .30 .419))
(define-fun .421 () (_ FP 8 24) (+ .3 .416 .420))
(define-fun .422 () Bool (<= .421 .397))
(assert .422)
(check-sat)
