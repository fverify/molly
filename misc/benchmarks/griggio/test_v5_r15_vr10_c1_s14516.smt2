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
(define-fun .39 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.658999979496002197266))
(define-fun .42 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.740999996662139892578)))
(define-fun .43 () (_ FP 8 24) (* .3 .14 .42))
(define-fun .44 () (_ FP 8 24) (+ .3 .12 .43))
(define-fun .47 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.838999986648559570313)))
(define-fun .48 () (_ FP 8 24) (* .3 .18 .47))
(define-fun .49 () (_ FP 8 24) (+ .3 .44 .48))
(define-fun .51 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.510999977588653564453))
(define-fun .52 () (_ FP 8 24) (* .3 .22 .51))
(define-fun .53 () (_ FP 8 24) (+ .3 .49 .52))
(define-fun .55 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.792999982833862304688))
(define-fun .56 () (_ FP 8 24) (* .3 .26 .55))
(define-fun .57 () (_ FP 8 24) (+ .3 .53 .56))
(define-fun .59 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.994000017642974853516))
(define-fun .60 () (_ FP 8 24) (* .3 .30 .59))
(define-fun .61 () (_ FP 8 24) (+ .3 .57 .60))
(define-fun .62 () Bool (<= .61 .39))
(assert .62)
(define-fun .64 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0680000036954879760742))
(define-fun .67 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.46700000762939453125)))
(define-fun .68 () (_ FP 8 24) (* .3 .14 .67))
(define-fun .69 () (_ FP 8 24) (+ .3 .12 .68))
(define-fun .71 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.828999996185302734375))
(define-fun .72 () (_ FP 8 24) (* .3 .18 .71))
(define-fun .73 () (_ FP 8 24) (+ .3 .69 .72))
(define-fun .75 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.435999989509582519531))
(define-fun .76 () (_ FP 8 24) (* .3 .22 .75))
(define-fun .77 () (_ FP 8 24) (+ .3 .73 .76))
(define-fun .79 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.495999991893768310547))
(define-fun .80 () (_ FP 8 24) (* .3 .26 .79))
(define-fun .81 () (_ FP 8 24) (+ .3 .77 .80))
(define-fun .83 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0670000016689300537109))
(define-fun .84 () (_ FP 8 24) (* .3 .30 .83))
(define-fun .85 () (_ FP 8 24) (+ .3 .81 .84))
(define-fun .86 () Bool (<= .85 .64))
(assert .86)
(define-fun .89 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.39500001072883605957)))
(define-fun .92 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.986999988555908203125)))
(define-fun .93 () (_ FP 8 24) (* .3 .14 .92))
(define-fun .94 () (_ FP 8 24) (+ .3 .12 .93))
(define-fun .96 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.270999997854232788086))
(define-fun .97 () (_ FP 8 24) (* .3 .18 .96))
(define-fun .98 () (_ FP 8 24) (+ .3 .94 .97))
(define-fun .100 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.772000014781951904297))
(define-fun .101 () (_ FP 8 24) (* .3 .22 .100))
(define-fun .102 () (_ FP 8 24) (+ .3 .98 .101))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.797999978065490722656)))
(define-fun .106 () (_ FP 8 24) (* .3 .26 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .102 .106))
(define-fun .109 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.737999975681304931641))
(define-fun .110 () (_ FP 8 24) (* .3 .30 .109))
(define-fun .111 () (_ FP 8 24) (+ .3 .107 .110))
(define-fun .112 () Bool (<= .111 .89))
(assert .112)
(define-fun .114 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.305999994277954101563))
(define-fun .117 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0860000029206275939941)))
(define-fun .118 () (_ FP 8 24) (* .3 .14 .117))
(define-fun .119 () (_ FP 8 24) (+ .3 .12 .118))
(define-fun .122 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.345999985933303833008)))
(define-fun .123 () (_ FP 8 24) (* .3 .18 .122))
(define-fun .124 () (_ FP 8 24) (+ .3 .119 .123))
(define-fun .127 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0979999974370002746582)))
(define-fun .128 () (_ FP 8 24) (* .3 .22 .127))
(define-fun .129 () (_ FP 8 24) (+ .3 .124 .128))
(define-fun .131 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0900000035762786865234))
(define-fun .132 () (_ FP 8 24) (* .3 .26 .131))
(define-fun .133 () (_ FP 8 24) (+ .3 .129 .132))
(define-fun .135 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.453000009059906005859))
(define-fun .136 () (_ FP 8 24) (* .3 .30 .135))
(define-fun .137 () (_ FP 8 24) (+ .3 .133 .136))
(define-fun .138 () Bool (<= .137 .114))
(assert .138)
(define-fun .140 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.367000013589859008789))
(define-fun .143 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.349999994039535522461)))
(define-fun .144 () (_ FP 8 24) (* .3 .14 .143))
(define-fun .145 () (_ FP 8 24) (+ .3 .12 .144))
(define-fun .147 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0160000007599592208862))
(define-fun .148 () (_ FP 8 24) (* .3 .18 .147))
(define-fun .149 () (_ FP 8 24) (+ .3 .145 .148))
(define-fun .152 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.109999999403953552246)))
(define-fun .153 () (_ FP 8 24) (* .3 .22 .152))
(define-fun .154 () (_ FP 8 24) (+ .3 .149 .153))
(define-fun .156 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0480000004172325134277))
(define-fun .157 () (_ FP 8 24) (* .3 .26 .156))
(define-fun .158 () (_ FP 8 24) (+ .3 .154 .157))
(define-fun .160 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0379999987781047821045))
(define-fun .161 () (_ FP 8 24) (* .3 .30 .160))
(define-fun .162 () (_ FP 8 24) (+ .3 .158 .161))
(define-fun .163 () Bool (<= .162 .140))
(assert .163)
(define-fun .166 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.12800000607967376709)))
(define-fun .169 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.889999985694885253906)))
(define-fun .170 () (_ FP 8 24) (* .3 .14 .169))
(define-fun .171 () (_ FP 8 24) (+ .3 .12 .170))
(define-fun .173 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.335000008344650268555))
(define-fun .174 () (_ FP 8 24) (* .3 .18 .173))
(define-fun .175 () (_ FP 8 24) (+ .3 .171 .174))
(define-fun .178 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.518999993801116943359)))
(define-fun .179 () (_ FP 8 24) (* .3 .22 .178))
(define-fun .180 () (_ FP 8 24) (+ .3 .175 .179))
(define-fun .182 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.425999999046325683594))
(define-fun .183 () (_ FP 8 24) (* .3 .26 .182))
(define-fun .184 () (_ FP 8 24) (+ .3 .180 .183))
(define-fun .187 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.823000013828277587891)))
(define-fun .188 () (_ FP 8 24) (* .3 .30 .187))
(define-fun .189 () (_ FP 8 24) (+ .3 .184 .188))
(define-fun .190 () Bool (<= .189 .166))
(assert .190)
(define-fun .192 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.259999990463256835938))
(define-fun .194 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.391999989748001098633))
(define-fun .195 () (_ FP 8 24) (* .3 .14 .194))
(define-fun .196 () (_ FP 8 24) (+ .3 .12 .195))
(define-fun .198 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.239999994635581970215))
(define-fun .199 () (_ FP 8 24) (* .3 .18 .198))
(define-fun .200 () (_ FP 8 24) (+ .3 .196 .199))
(define-fun .203 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.331000000238418579102)))
(define-fun .204 () (_ FP 8 24) (* .3 .22 .203))
(define-fun .205 () (_ FP 8 24) (+ .3 .200 .204))
(define-fun .208 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.708999991416931152344)))
(define-fun .209 () (_ FP 8 24) (* .3 .26 .208))
(define-fun .210 () (_ FP 8 24) (+ .3 .205 .209))
(define-fun .213 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.841000020503997802734)))
(define-fun .214 () (_ FP 8 24) (* .3 .30 .213))
(define-fun .215 () (_ FP 8 24) (+ .3 .210 .214))
(define-fun .216 () Bool (<= .215 .192))
(assert .216)
(define-fun .218 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.268999993801116943359))
(define-fun .221 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.987999975681304931641)))
(define-fun .222 () (_ FP 8 24) (* .3 .14 .221))
(define-fun .223 () (_ FP 8 24) (+ .3 .12 .222))
(define-fun .226 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.293999999761581420898)))
(define-fun .227 () (_ FP 8 24) (* .3 .18 .226))
(define-fun .228 () (_ FP 8 24) (+ .3 .223 .227))
(define-fun .231 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0460000000894069671631)))
(define-fun .232 () (_ FP 8 24) (* .3 .22 .231))
(define-fun .233 () (_ FP 8 24) (+ .3 .228 .232))
(define-fun .236 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.600000023841857910156)))
(define-fun .237 () (_ FP 8 24) (* .3 .26 .236))
(define-fun .238 () (_ FP 8 24) (+ .3 .233 .237))
(define-fun .241 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.638000011444091796875)))
(define-fun .242 () (_ FP 8 24) (* .3 .30 .241))
(define-fun .243 () (_ FP 8 24) (+ .3 .238 .242))
(define-fun .244 () Bool (<= .218 .243))
(assert .244)
(define-fun .246 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.623000025749206542969))
(define-fun .248 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.296999990940093994141))
(define-fun .249 () (_ FP 8 24) (* .3 .14 .248))
(define-fun .250 () (_ FP 8 24) (+ .3 .12 .249))
(define-fun .252 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0240000002086162567139))
(define-fun .253 () (_ FP 8 24) (* .3 .18 .252))
(define-fun .254 () (_ FP 8 24) (+ .3 .250 .253))
(define-fun .256 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.861000001430511474609))
(define-fun .257 () (_ FP 8 24) (* .3 .22 .256))
(define-fun .258 () (_ FP 8 24) (+ .3 .254 .257))
(define-fun .260 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.730000019073486328125))
(define-fun .261 () (_ FP 8 24) (* .3 .26 .260))
(define-fun .262 () (_ FP 8 24) (+ .3 .258 .261))
(define-fun .265 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.575999975204467773438)))
(define-fun .266 () (_ FP 8 24) (* .3 .30 .265))
(define-fun .267 () (_ FP 8 24) (+ .3 .262 .266))
(define-fun .268 () Bool (<= .246 .267))
(assert .268)
(define-fun .270 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.882000029087066650391))
(define-fun .272 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.773000001907348632813))
(define-fun .273 () (_ FP 8 24) (* .3 .14 .272))
(define-fun .274 () (_ FP 8 24) (+ .3 .12 .273))
(define-fun .276 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.903999984264373779297))
(define-fun .277 () (_ FP 8 24) (* .3 .18 .276))
(define-fun .278 () (_ FP 8 24) (+ .3 .274 .277))
(define-fun .280 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.442000001668930053711))
(define-fun .281 () (_ FP 8 24) (* .3 .22 .280))
(define-fun .282 () (_ FP 8 24) (+ .3 .278 .281))
(define-fun .284 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.508000016212463378906))
(define-fun .285 () (_ FP 8 24) (* .3 .26 .284))
(define-fun .286 () (_ FP 8 24) (+ .3 .282 .285))
(define-fun .289 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.458000004291534423828)))
(define-fun .290 () (_ FP 8 24) (* .3 .30 .289))
(define-fun .291 () (_ FP 8 24) (+ .3 .286 .290))
(define-fun .292 () Bool (<= .270 .291))
(assert .292)
(define-fun .294 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.483999997377395629883))
(define-fun .296 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.418000012636184692383))
(define-fun .297 () (_ FP 8 24) (* .3 .14 .296))
(define-fun .298 () (_ FP 8 24) (+ .3 .12 .297))
(define-fun .301 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.391000002622604370117)))
(define-fun .302 () (_ FP 8 24) (* .3 .18 .301))
(define-fun .303 () (_ FP 8 24) (+ .3 .298 .302))
(define-fun .305 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.377999991178512573242))
(define-fun .306 () (_ FP 8 24) (* .3 .22 .305))
(define-fun .307 () (_ FP 8 24) (+ .3 .303 .306))
(define-fun .310 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.075999997556209564209)))
(define-fun .311 () (_ FP 8 24) (* .3 .26 .310))
(define-fun .312 () (_ FP 8 24) (+ .3 .307 .311))
(define-fun .315 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.167999997735023498535)))
(define-fun .316 () (_ FP 8 24) (* .3 .30 .315))
(define-fun .317 () (_ FP 8 24) (+ .3 .312 .316))
(define-fun .318 () Bool (<= .294 .317))
(assert .318)
(define-fun .321 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0320000015199184417725)))
(define-fun .323 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.976999998092651367188))
(define-fun .324 () (_ FP 8 24) (* .3 .14 .323))
(define-fun .325 () (_ FP 8 24) (+ .3 .12 .324))
(define-fun .327 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.607999980449676513672))
(define-fun .328 () (_ FP 8 24) (* .3 .18 .327))
(define-fun .329 () (_ FP 8 24) (+ .3 .325 .328))
(define-fun .331 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.170000001788139343262))
(define-fun .332 () (_ FP 8 24) (* .3 .22 .331))
(define-fun .333 () (_ FP 8 24) (+ .3 .329 .332))
(define-fun .335 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.913999974727630615234))
(define-fun .336 () (_ FP 8 24) (* .3 .26 .335))
(define-fun .337 () (_ FP 8 24) (+ .3 .333 .336))
(define-fun .339 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.754999995231628417969))
(define-fun .340 () (_ FP 8 24) (* .3 .30 .339))
(define-fun .341 () (_ FP 8 24) (+ .3 .337 .340))
(define-fun .342 () Bool (<= .321 .341))
(assert .342)
(define-fun .345 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.633000016212463378906)))
(define-fun .347 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.481999993324279785156))
(define-fun .348 () (_ FP 8 24) (* .3 .14 .347))
(define-fun .349 () (_ FP 8 24) (+ .3 .12 .348))
(define-fun .352 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.630999982357025146484)))
(define-fun .353 () (_ FP 8 24) (* .3 .18 .352))
(define-fun .354 () (_ FP 8 24) (+ .3 .349 .353))
(define-fun .357 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.709999978542327880859)))
(define-fun .358 () (_ FP 8 24) (* .3 .22 .357))
(define-fun .359 () (_ FP 8 24) (+ .3 .354 .358))
(define-fun .361 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.405000001192092895508))
(define-fun .362 () (_ FP 8 24) (* .3 .26 .361))
(define-fun .363 () (_ FP 8 24) (+ .3 .359 .362))
(define-fun .364 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.976999998092651367188)))
(define-fun .365 () (_ FP 8 24) (* .3 .30 .364))
(define-fun .366 () (_ FP 8 24) (+ .3 .363 .365))
(define-fun .367 () Bool (<= .345 .366))
(assert .367)
(define-fun .351 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.630999982357025146484))
(define-fun .369 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.763000011444091796875))
(define-fun .371 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.187000006437301635742))
(define-fun .372 () (_ FP 8 24) (* .3 .14 .371))
(define-fun .373 () (_ FP 8 24) (+ .3 .12 .372))
(define-fun .375 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.423000007867813110352))
(define-fun .376 () (_ FP 8 24) (* .3 .18 .375))
(define-fun .377 () (_ FP 8 24) (+ .3 .373 .376))
(define-fun .380 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.582000017166137695313)))
(define-fun .381 () (_ FP 8 24) (* .3 .22 .380))
(define-fun .382 () (_ FP 8 24) (+ .3 .377 .381))
(define-fun .383 () (_ FP 8 24) (* .3 .26 .351))
(define-fun .384 () (_ FP 8 24) (+ .3 .382 .383))
(define-fun .387 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.634999990463256835938)))
(define-fun .388 () (_ FP 8 24) (* .3 .30 .387))
(define-fun .389 () (_ FP 8 24) (+ .3 .384 .388))
(define-fun .390 () Bool (<= .369 .389))
(assert .390)
(define-fun .392 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.704999983310699462891))
(define-fun .394 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.59899997711181640625))
(define-fun .395 () (_ FP 8 24) (* .3 .14 .394))
(define-fun .396 () (_ FP 8 24) (+ .3 .12 .395))
(define-fun .399 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.926999986171722412109)))
(define-fun .400 () (_ FP 8 24) (* .3 .18 .399))
(define-fun .401 () (_ FP 8 24) (+ .3 .396 .400))
(define-fun .403 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.0))
(define-fun .404 () (_ FP 8 24) (* .3 .22 .403))
(define-fun .405 () (_ FP 8 24) (+ .3 .401 .404))
(define-fun .408 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.351999998092651367188)))
(define-fun .409 () (_ FP 8 24) (* .3 .26 .408))
(define-fun .410 () (_ FP 8 24) (+ .3 .405 .409))
(define-fun .412 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.439000010490417480469))
(define-fun .413 () (_ FP 8 24) (* .3 .30 .412))
(define-fun .414 () (_ FP 8 24) (+ .3 .410 .413))
(define-fun .415 () Bool (<= .392 .414))
(assert .415)
(check-sat)
