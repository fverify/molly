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
(define-fun .40 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.237000003457069396973)))
(define-fun .42 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0199999995529651641846))
(define-fun .43 () (_ FP 8 24) (* .3 .14 .42))
(define-fun .44 () (_ FP 8 24) (+ .3 .12 .43))
(define-fun .46 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.814999997615814208984))
(define-fun .47 () (_ FP 8 24) (* .3 .18 .46))
(define-fun .48 () (_ FP 8 24) (+ .3 .44 .47))
(define-fun .51 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0649999976158142089844)))
(define-fun .52 () (_ FP 8 24) (* .3 .22 .51))
(define-fun .53 () (_ FP 8 24) (+ .3 .48 .52))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.16400000452995300293)))
(define-fun .57 () (_ FP 8 24) (* .3 .26 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .53 .57))
(define-fun .60 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.456000000238418579102))
(define-fun .61 () (_ FP 8 24) (* .3 .30 .60))
(define-fun .62 () (_ FP 8 24) (+ .3 .58 .61))
(define-fun .63 () Bool (<= .62 .40))
(assert .63)
(define-fun .66 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.189999997615814208984)))
(define-fun .68 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.699000000953674316406))
(define-fun .69 () (_ FP 8 24) (* .3 .14 .68))
(define-fun .70 () (_ FP 8 24) (+ .3 .12 .69))
(define-fun .72 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.984000027179718017578))
(define-fun .73 () (_ FP 8 24) (* .3 .18 .72))
(define-fun .74 () (_ FP 8 24) (+ .3 .70 .73))
(define-fun .77 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.760999977588653564453)))
(define-fun .78 () (_ FP 8 24) (* .3 .22 .77))
(define-fun .79 () (_ FP 8 24) (+ .3 .74 .78))
(define-fun .81 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.904999971389770507813))
(define-fun .82 () (_ FP 8 24) (* .3 .26 .81))
(define-fun .83 () (_ FP 8 24) (+ .3 .79 .82))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.763000011444091796875))
(define-fun .86 () (_ FP 8 24) (* .3 .30 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .83 .86))
(define-fun .88 () Bool (<= .87 .66))
(assert .88)
(define-fun .90 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.587000012397766113281))
(define-fun .92 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.547999978065490722656))
(define-fun .93 () (_ FP 8 24) (* .3 .14 .92))
(define-fun .94 () (_ FP 8 24) (+ .3 .12 .93))
(define-fun .96 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.137999996542930603027))
(define-fun .97 () (_ FP 8 24) (* .3 .18 .96))
(define-fun .98 () (_ FP 8 24) (+ .3 .94 .97))
(define-fun .101 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0230000000447034835815)))
(define-fun .102 () (_ FP 8 24) (* .3 .22 .101))
(define-fun .103 () (_ FP 8 24) (+ .3 .98 .102))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.560000002384185791016))
(define-fun .106 () (_ FP 8 24) (* .3 .26 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .103 .106))
(define-fun .110 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.903999984264373779297)))
(define-fun .111 () (_ FP 8 24) (* .3 .30 .110))
(define-fun .112 () (_ FP 8 24) (+ .3 .107 .111))
(define-fun .113 () Bool (<= .90 .112))
(assert .113)
(define-fun .115 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.130999997258186340332))
(define-fun .118 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.215000003576278686523)))
(define-fun .119 () (_ FP 8 24) (* .3 .14 .118))
(define-fun .120 () (_ FP 8 24) (+ .3 .12 .119))
(define-fun .122 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.829999983310699462891))
(define-fun .123 () (_ FP 8 24) (* .3 .18 .122))
(define-fun .124 () (_ FP 8 24) (+ .3 .120 .123))
(define-fun .127 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.188999995589256286621)))
(define-fun .128 () (_ FP 8 24) (* .3 .22 .127))
(define-fun .129 () (_ FP 8 24) (+ .3 .124 .128))
(define-fun .132 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.924000024795532226563)))
(define-fun .133 () (_ FP 8 24) (* .3 .26 .132))
(define-fun .134 () (_ FP 8 24) (+ .3 .129 .133))
(define-fun .136 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.246000006794929504395))
(define-fun .137 () (_ FP 8 24) (* .3 .30 .136))
(define-fun .138 () (_ FP 8 24) (+ .3 .134 .137))
(define-fun .139 () Bool (<= .138 .115))
(assert .139)
(define-fun .141 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.996999979019165039063))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.141000002622604370117)))
(define-fun .145 () (_ FP 8 24) (* .3 .14 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .12 .145))
(define-fun .149 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0500000007450580596924)))
(define-fun .150 () (_ FP 8 24) (* .3 .18 .149))
(define-fun .151 () (_ FP 8 24) (+ .3 .146 .150))
(define-fun .154 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.563000023365020751953)))
(define-fun .155 () (_ FP 8 24) (* .3 .22 .154))
(define-fun .156 () (_ FP 8 24) (+ .3 .151 .155))
(define-fun .158 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0250000003725290298462))
(define-fun .159 () (_ FP 8 24) (* .3 .26 .158))
(define-fun .160 () (_ FP 8 24) (+ .3 .156 .159))
(define-fun .162 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.703000009059906005859))
(define-fun .163 () (_ FP 8 24) (* .3 .30 .162))
(define-fun .164 () (_ FP 8 24) (+ .3 .160 .163))
(define-fun .165 () Bool (<= .164 .141))
(assert .165)
(define-fun .167 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.717999994754791259766))
(define-fun .169 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0820000022649765014648))
(define-fun .170 () (_ FP 8 24) (* .3 .14 .169))
(define-fun .171 () (_ FP 8 24) (+ .3 .12 .170))
(define-fun .173 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.781000018119812011719))
(define-fun .174 () (_ FP 8 24) (* .3 .18 .173))
(define-fun .175 () (_ FP 8 24) (+ .3 .171 .174))
(define-fun .178 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.533999979496002197266)))
(define-fun .179 () (_ FP 8 24) (* .3 .22 .178))
(define-fun .180 () (_ FP 8 24) (+ .3 .175 .179))
(define-fun .183 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.597999989986419677734)))
(define-fun .184 () (_ FP 8 24) (* .3 .26 .183))
(define-fun .185 () (_ FP 8 24) (+ .3 .180 .184))
(define-fun .187 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.549000024795532226563))
(define-fun .188 () (_ FP 8 24) (* .3 .30 .187))
(define-fun .189 () (_ FP 8 24) (+ .3 .185 .188))
(define-fun .190 () Bool (<= .167 .189))
(assert .190)
(define-fun .192 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.615000009536743164063))
(define-fun .194 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.435000002384185791016))
(define-fun .195 () (_ FP 8 24) (* .3 .14 .194))
(define-fun .196 () (_ FP 8 24) (+ .3 .12 .195))
(define-fun .199 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.175999999046325683594)))
(define-fun .200 () (_ FP 8 24) (* .3 .18 .199))
(define-fun .201 () (_ FP 8 24) (+ .3 .196 .200))
(define-fun .203 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.866999983787536621094))
(define-fun .204 () (_ FP 8 24) (* .3 .22 .203))
(define-fun .205 () (_ FP 8 24) (+ .3 .201 .204))
(define-fun .208 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.947000026702880859375)))
(define-fun .209 () (_ FP 8 24) (* .3 .26 .208))
(define-fun .210 () (_ FP 8 24) (+ .3 .205 .209))
(define-fun .211 () (_ FP 8 24) (* .3 .30 .208))
(define-fun .212 () (_ FP 8 24) (+ .3 .210 .211))
(define-fun .213 () Bool (<= .192 .212))
(assert .213)
(define-fun .215 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.778999984264373779297))
(define-fun .218 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.607999980449676513672)))
(define-fun .219 () (_ FP 8 24) (* .3 .14 .218))
(define-fun .220 () (_ FP 8 24) (+ .3 .12 .219))
(define-fun .223 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.460000008344650268555)))
(define-fun .224 () (_ FP 8 24) (* .3 .18 .223))
(define-fun .225 () (_ FP 8 24) (+ .3 .220 .224))
(define-fun .228 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.558000028133392333984)))
(define-fun .229 () (_ FP 8 24) (* .3 .22 .228))
(define-fun .230 () (_ FP 8 24) (+ .3 .225 .229))
(define-fun .232 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.361999988555908203125))
(define-fun .233 () (_ FP 8 24) (* .3 .26 .232))
(define-fun .234 () (_ FP 8 24) (+ .3 .230 .233))
(define-fun .237 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.950999975204467773438)))
(define-fun .238 () (_ FP 8 24) (* .3 .30 .237))
(define-fun .239 () (_ FP 8 24) (+ .3 .234 .238))
(define-fun .240 () Bool (<= .239 .215))
(assert .240)
(define-fun .243 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.856999993324279785156)))
(define-fun .245 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.741999983787536621094))
(define-fun .246 () (_ FP 8 24) (* .3 .14 .245))
(define-fun .247 () (_ FP 8 24) (+ .3 .12 .246))
(define-fun .250 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.187000006437301635742)))
(define-fun .251 () (_ FP 8 24) (* .3 .18 .250))
(define-fun .252 () (_ FP 8 24) (+ .3 .247 .251))
(define-fun .255 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.223000004887580871582)))
(define-fun .256 () (_ FP 8 24) (* .3 .22 .255))
(define-fun .257 () (_ FP 8 24) (+ .3 .252 .256))
(define-fun .260 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.244000002741813659668)))
(define-fun .261 () (_ FP 8 24) (* .3 .26 .260))
(define-fun .262 () (_ FP 8 24) (+ .3 .257 .261))
(define-fun .265 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.21099999547004699707)))
(define-fun .266 () (_ FP 8 24) (* .3 .30 .265))
(define-fun .267 () (_ FP 8 24) (+ .3 .262 .266))
(define-fun .268 () Bool (<= .243 .267))
(assert .268)
(define-fun .271 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.671999990940093994141)))
(define-fun .273 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.307000011205673217773))
(define-fun .274 () (_ FP 8 24) (* .3 .14 .273))
(define-fun .275 () (_ FP 8 24) (+ .3 .12 .274))
(define-fun .278 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.263000011444091796875)))
(define-fun .279 () (_ FP 8 24) (* .3 .18 .278))
(define-fun .280 () (_ FP 8 24) (+ .3 .275 .279))
(define-fun .281 () (_ FP 8 24) (* .3 .22 .237))
(define-fun .282 () (_ FP 8 24) (+ .3 .280 .281))
(define-fun .284 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.340999990701675415039))
(define-fun .285 () (_ FP 8 24) (* .3 .26 .284))
(define-fun .286 () (_ FP 8 24) (+ .3 .282 .285))
(define-fun .288 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.47999998927116394043))
(define-fun .289 () (_ FP 8 24) (* .3 .30 .288))
(define-fun .290 () (_ FP 8 24) (+ .3 .286 .289))
(define-fun .291 () Bool (<= .290 .271))
(assert .291)
(define-fun .126 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.188999995589256286621))
(define-fun .293 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.212999999523162841797))
(define-fun .295 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.143999993801116943359))
(define-fun .296 () (_ FP 8 24) (* .3 .14 .295))
(define-fun .297 () (_ FP 8 24) (+ .3 .12 .296))
(define-fun .298 () (_ FP 8 24) (* .3 .18 .126))
(define-fun .299 () (_ FP 8 24) (+ .3 .297 .298))
(define-fun .302 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.372999995946884155273)))
(define-fun .303 () (_ FP 8 24) (* .3 .22 .302))
(define-fun .304 () (_ FP 8 24) (+ .3 .299 .303))
(define-fun .307 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.889999985694885253906)))
(define-fun .308 () (_ FP 8 24) (* .3 .26 .307))
(define-fun .309 () (_ FP 8 24) (+ .3 .304 .308))
(define-fun .312 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.845000028610229492188)))
(define-fun .313 () (_ FP 8 24) (* .3 .30 .312))
(define-fun .314 () (_ FP 8 24) (+ .3 .309 .313))
(define-fun .315 () Bool (<= .293 .314))
(assert .315)
(define-fun .317 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.180999994277954101563))
(define-fun .318 () (_ FP 8 24) (* .3 .14 .317))
(define-fun .319 () (_ FP 8 24) (+ .3 .12 .318))
(define-fun .320 () (_ FP 8 24) (* .3 .18 .312))
(define-fun .321 () (_ FP 8 24) (+ .3 .319 .320))
(define-fun .324 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.908999979496002197266)))
(define-fun .325 () (_ FP 8 24) (* .3 .22 .324))
(define-fun .326 () (_ FP 8 24) (+ .3 .321 .325))
(define-fun .329 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.527000010013580322266)))
(define-fun .330 () (_ FP 8 24) (* .3 .26 .329))
(define-fun .331 () (_ FP 8 24) (+ .3 .326 .330))
(define-fun .334 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.634000003337860107422)))
(define-fun .335 () (_ FP 8 24) (* .3 .30 .334))
(define-fun .336 () (_ FP 8 24) (+ .3 .331 .335))
(define-fun .337 () Bool (<= .167 .336))
(assert .337)
(define-fun .339 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.151999995112419128418))
(define-fun .341 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.492000013589859008789))
(define-fun .342 () (_ FP 8 24) (* .3 .14 .341))
(define-fun .343 () (_ FP 8 24) (+ .3 .12 .342))
(define-fun .346 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.44699999690055847168)))
(define-fun .347 () (_ FP 8 24) (* .3 .18 .346))
(define-fun .348 () (_ FP 8 24) (+ .3 .343 .347))
(define-fun .350 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.711000025272369384766))
(define-fun .351 () (_ FP 8 24) (* .3 .22 .350))
(define-fun .352 () (_ FP 8 24) (+ .3 .348 .351))
(define-fun .354 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.296000003814697265625))
(define-fun .355 () (_ FP 8 24) (* .3 .26 .354))
(define-fun .356 () (_ FP 8 24) (+ .3 .352 .355))
(define-fun .359 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.421000003814697265625)))
(define-fun .360 () (_ FP 8 24) (* .3 .30 .359))
(define-fun .361 () (_ FP 8 24) (+ .3 .356 .360))
(define-fun .362 () Bool (<= .339 .361))
(assert .362)
(define-fun .365 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.287000000476837158203)))
(define-fun .367 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.584999978542327880859))
(define-fun .368 () (_ FP 8 24) (* .3 .14 .367))
(define-fun .369 () (_ FP 8 24) (+ .3 .12 .368))
(define-fun .371 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.90100002288818359375))
(define-fun .372 () (_ FP 8 24) (* .3 .18 .371))
(define-fun .373 () (_ FP 8 24) (+ .3 .369 .372))
(define-fun .374 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.547999978065490722656)))
(define-fun .375 () (_ FP 8 24) (* .3 .22 .374))
(define-fun .376 () (_ FP 8 24) (+ .3 .373 .375))
(define-fun .378 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.391999989748001098633))
(define-fun .379 () (_ FP 8 24) (* .3 .26 .378))
(define-fun .380 () (_ FP 8 24) (+ .3 .376 .379))
(define-fun .382 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.335000008344650268555))
(define-fun .383 () (_ FP 8 24) (* .3 .30 .382))
(define-fun .384 () (_ FP 8 24) (+ .3 .380 .383))
(define-fun .385 () Bool (<= .365 .384))
(assert .385)
(define-fun .387 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.579999983310699462891))
(define-fun .388 () (_ FP 8 24) (* .3 .14 .96))
(define-fun .389 () (_ FP 8 24) (+ .3 .12 .388))
(define-fun .392 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.150000005960464477539)))
(define-fun .393 () (_ FP 8 24) (* .3 .18 .392))
(define-fun .394 () (_ FP 8 24) (+ .3 .389 .393))
(define-fun .396 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.439999997615814208984))
(define-fun .397 () (_ FP 8 24) (* .3 .22 .396))
(define-fun .398 () (_ FP 8 24) (+ .3 .394 .397))
(define-fun .401 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.345999985933303833008)))
(define-fun .402 () (_ FP 8 24) (* .3 .26 .401))
(define-fun .403 () (_ FP 8 24) (+ .3 .398 .402))
(define-fun .405 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0280000008642673492432))
(define-fun .406 () (_ FP 8 24) (* .3 .30 .405))
(define-fun .407 () (_ FP 8 24) (+ .3 .403 .406))
(define-fun .408 () Bool (<= .387 .407))
(assert .408)
(check-sat)