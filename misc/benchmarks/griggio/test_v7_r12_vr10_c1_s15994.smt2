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
(define-fun .47 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.689999997615814208984))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.635999977588653564453)))
(define-fun .51 () (_ FP 8 24) (* .3 .14 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .12 .51))
(define-fun .55 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.75)))
(define-fun .56 () (_ FP 8 24) (* .3 .18 .55))
(define-fun .57 () (_ FP 8 24) (+ .3 .52 .56))
(define-fun .60 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.769999980926513671875)))
(define-fun .61 () (_ FP 8 24) (* .3 .22 .60))
(define-fun .62 () (_ FP 8 24) (+ .3 .57 .61))
(define-fun .64 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0640000030398368835449))
(define-fun .65 () (_ FP 8 24) (* .3 .26 .64))
(define-fun .66 () (_ FP 8 24) (+ .3 .62 .65))
(define-fun .69 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.936999976634979248047)))
(define-fun .70 () (_ FP 8 24) (* .3 .30 .69))
(define-fun .71 () (_ FP 8 24) (+ .3 .66 .70))
(define-fun .74 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.870999991893768310547)))
(define-fun .75 () (_ FP 8 24) (* .3 .34 .74))
(define-fun .76 () (_ FP 8 24) (+ .3 .71 .75))
(define-fun .78 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.620000004768371582031))
(define-fun .79 () (_ FP 8 24) (* .3 .38 .78))
(define-fun .80 () (_ FP 8 24) (+ .3 .76 .79))
(define-fun .81 () Bool (<= .47 .80))
(assert .81)
(define-fun .83 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.814000010490417480469))
(define-fun .84 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.814000010490417480469)))
(define-fun .86 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.261999994516372680664))
(define-fun .87 () (_ FP 8 24) (* .3 .14 .86))
(define-fun .88 () (_ FP 8 24) (+ .3 .12 .87))
(define-fun .90 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.811999976634979248047))
(define-fun .91 () (_ FP 8 24) (* .3 .18 .90))
(define-fun .92 () (_ FP 8 24) (+ .3 .88 .91))
(define-fun .95 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.846000015735626220703)))
(define-fun .96 () (_ FP 8 24) (* .3 .22 .95))
(define-fun .97 () (_ FP 8 24) (+ .3 .92 .96))
(define-fun .100 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.349999994039535522461)))
(define-fun .101 () (_ FP 8 24) (* .3 .26 .100))
(define-fun .102 () (_ FP 8 24) (+ .3 .97 .101))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.902000010013580322266)))
(define-fun .106 () (_ FP 8 24) (* .3 .30 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .102 .106))
(define-fun .110 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0649999976158142089844)))
(define-fun .111 () (_ FP 8 24) (* .3 .34 .110))
(define-fun .112 () (_ FP 8 24) (+ .3 .107 .111))
(define-fun .113 () (_ FP 8 24) (* .3 .38 .83))
(define-fun .114 () (_ FP 8 24) (+ .3 .112 .113))
(define-fun .115 () Bool (<= .84 .114))
(assert .115)
(define-fun .118 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.843999981880187988281)))
(define-fun .121 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.788999974727630615234)))
(define-fun .122 () (_ FP 8 24) (* .3 .14 .121))
(define-fun .123 () (_ FP 8 24) (+ .3 .12 .122))
(define-fun .125 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.591000020503997802734))
(define-fun .126 () (_ FP 8 24) (* .3 .18 .125))
(define-fun .127 () (_ FP 8 24) (+ .3 .123 .126))
(define-fun .130 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.694000005722045898438)))
(define-fun .131 () (_ FP 8 24) (* .3 .22 .130))
(define-fun .132 () (_ FP 8 24) (+ .3 .127 .131))
(define-fun .133 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0640000030398368835449)))
(define-fun .134 () (_ FP 8 24) (* .3 .26 .133))
(define-fun .135 () (_ FP 8 24) (+ .3 .132 .134))
(define-fun .137 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.287999987602233886719))
(define-fun .138 () (_ FP 8 24) (* .3 .30 .137))
(define-fun .139 () (_ FP 8 24) (+ .3 .135 .138))
(define-fun .141 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.697000026702880859375))
(define-fun .142 () (_ FP 8 24) (* .3 .34 .141))
(define-fun .143 () (_ FP 8 24) (+ .3 .139 .142))
(define-fun .146 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.144999995827674865723)))
(define-fun .147 () (_ FP 8 24) (* .3 .38 .146))
(define-fun .148 () (_ FP 8 24) (+ .3 .143 .147))
(define-fun .149 () Bool (<= .118 .148))
(assert .149)
(define-fun .152 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.123000003397464752197)))
(define-fun .155 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.469999998807907104492)))
(define-fun .156 () (_ FP 8 24) (* .3 .14 .155))
(define-fun .157 () (_ FP 8 24) (+ .3 .12 .156))
(define-fun .159 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.550999999046325683594))
(define-fun .160 () (_ FP 8 24) (* .3 .18 .159))
(define-fun .161 () (_ FP 8 24) (+ .3 .157 .160))
(define-fun .163 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.112999998033046722412))
(define-fun .164 () (_ FP 8 24) (* .3 .22 .163))
(define-fun .165 () (_ FP 8 24) (+ .3 .161 .164))
(define-fun .167 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0170000009238719940186))
(define-fun .168 () (_ FP 8 24) (* .3 .26 .167))
(define-fun .169 () (_ FP 8 24) (+ .3 .165 .168))
(define-fun .171 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.197999998927116394043))
(define-fun .172 () (_ FP 8 24) (* .3 .30 .171))
(define-fun .173 () (_ FP 8 24) (+ .3 .169 .172))
(define-fun .176 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.224000006914138793945)))
(define-fun .177 () (_ FP 8 24) (* .3 .34 .176))
(define-fun .178 () (_ FP 8 24) (+ .3 .173 .177))
(define-fun .180 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.28900000452995300293))
(define-fun .181 () (_ FP 8 24) (* .3 .38 .180))
(define-fun .182 () (_ FP 8 24) (+ .3 .178 .181))
(define-fun .183 () Bool (<= .182 .152))
(assert .183)
(define-fun .185 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.967999994754791259766))
(define-fun .188 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.703000009059906005859)))
(define-fun .189 () (_ FP 8 24) (* .3 .14 .188))
(define-fun .190 () (_ FP 8 24) (+ .3 .12 .189))
(define-fun .193 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.177000001072883605957)))
(define-fun .194 () (_ FP 8 24) (* .3 .18 .193))
(define-fun .195 () (_ FP 8 24) (+ .3 .190 .194))
(define-fun .198 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.270999997854232788086)))
(define-fun .199 () (_ FP 8 24) (* .3 .22 .198))
(define-fun .200 () (_ FP 8 24) (+ .3 .195 .199))
(define-fun .203 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.518000006675720214844)))
(define-fun .204 () (_ FP 8 24) (* .3 .26 .203))
(define-fun .205 () (_ FP 8 24) (+ .3 .200 .204))
(define-fun .208 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.694999992847442626953)))
(define-fun .209 () (_ FP 8 24) (* .3 .30 .208))
(define-fun .210 () (_ FP 8 24) (+ .3 .205 .209))
(define-fun .212 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.326999992132186889648))
(define-fun .213 () (_ FP 8 24) (* .3 .34 .212))
(define-fun .214 () (_ FP 8 24) (+ .3 .210 .213))
(define-fun .216 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.10700000077486038208))
(define-fun .217 () (_ FP 8 24) (* .3 .38 .216))
(define-fun .218 () (_ FP 8 24) (+ .3 .214 .217))
(define-fun .219 () Bool (<= .218 .185))
(assert .219)
(define-fun .222 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.712999999523162841797)))
(define-fun .225 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.771000027656555175781)))
(define-fun .226 () (_ FP 8 24) (* .3 .14 .225))
(define-fun .227 () (_ FP 8 24) (+ .3 .12 .226))
(define-fun .230 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.736999988555908203125)))
(define-fun .231 () (_ FP 8 24) (* .3 .18 .230))
(define-fun .232 () (_ FP 8 24) (+ .3 .227 .231))
(define-fun .233 () (_ FP 8 24) (* .3 .22 .121))
(define-fun .234 () (_ FP 8 24) (+ .3 .232 .233))
(define-fun .237 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.47999998927116394043)))
(define-fun .238 () (_ FP 8 24) (* .3 .26 .237))
(define-fun .239 () (_ FP 8 24) (+ .3 .234 .238))
(define-fun .242 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.275000005960464477539)))
(define-fun .243 () (_ FP 8 24) (* .3 .30 .242))
(define-fun .244 () (_ FP 8 24) (+ .3 .239 .243))
(define-fun .245 () (_ FP 8 24) (* .3 .34 .78))
(define-fun .246 () (_ FP 8 24) (+ .3 .244 .245))
(define-fun .248 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.187000006437301635742))
(define-fun .249 () (_ FP 8 24) (* .3 .38 .248))
(define-fun .250 () (_ FP 8 24) (+ .3 .246 .249))
(define-fun .251 () Bool (<= .222 .250))
(assert .251)
(define-fun .221 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.712999999523162841797))
(define-fun .254 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.264999985694885253906)))
(define-fun .256 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.689000010490417480469))
(define-fun .257 () (_ FP 8 24) (* .3 .14 .256))
(define-fun .258 () (_ FP 8 24) (+ .3 .12 .257))
(define-fun .261 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.181999996304512023926)))
(define-fun .262 () (_ FP 8 24) (* .3 .18 .261))
(define-fun .263 () (_ FP 8 24) (+ .3 .258 .262))
(define-fun .265 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.953000009059906005859))
(define-fun .266 () (_ FP 8 24) (* .3 .22 .265))
(define-fun .267 () (_ FP 8 24) (+ .3 .263 .266))
(define-fun .269 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0799999982118606567383))
(define-fun .270 () (_ FP 8 24) (* .3 .26 .269))
(define-fun .271 () (_ FP 8 24) (+ .3 .267 .270))
(define-fun .272 () (_ FP 8 24) (* .3 .30 .221))
(define-fun .273 () (_ FP 8 24) (+ .3 .271 .272))
(define-fun .275 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.345999985933303833008))
(define-fun .276 () (_ FP 8 24) (* .3 .34 .275))
(define-fun .277 () (_ FP 8 24) (+ .3 .273 .276))
(define-fun .280 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.902999997138977050781)))
(define-fun .281 () (_ FP 8 24) (* .3 .38 .280))
(define-fun .282 () (_ FP 8 24) (+ .3 .277 .281))
(define-fun .283 () Bool (<= .282 .254))
(assert .283)
(define-fun .285 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.453999996185302734375))
(define-fun .287 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.479000002145767211914))
(define-fun .288 () (_ FP 8 24) (* .3 .14 .287))
(define-fun .289 () (_ FP 8 24) (+ .3 .12 .288))
(define-fun .291 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.377999991178512573242))
(define-fun .292 () (_ FP 8 24) (* .3 .18 .291))
(define-fun .293 () (_ FP 8 24) (+ .3 .289 .292))
(define-fun .295 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.522000014781951904297))
(define-fun .296 () (_ FP 8 24) (* .3 .22 .295))
(define-fun .297 () (_ FP 8 24) (+ .3 .293 .296))
(define-fun .299 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.777000010013580322266))
(define-fun .300 () (_ FP 8 24) (* .3 .26 .299))
(define-fun .301 () (_ FP 8 24) (+ .3 .297 .300))
(define-fun .304 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.708999991416931152344)))
(define-fun .305 () (_ FP 8 24) (* .3 .30 .304))
(define-fun .306 () (_ FP 8 24) (+ .3 .301 .305))
(define-fun .309 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.307000011205673217773)))
(define-fun .310 () (_ FP 8 24) (* .3 .34 .309))
(define-fun .311 () (_ FP 8 24) (+ .3 .306 .310))
(define-fun .313 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.953999996185302734375))
(define-fun .314 () (_ FP 8 24) (* .3 .38 .313))
(define-fun .315 () (_ FP 8 24) (+ .3 .311 .314))
(define-fun .316 () Bool (<= .315 .285))
(assert .316)
(define-fun .319 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.920000016689300537109)))
(define-fun .321 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00400000018998980522156))
(define-fun .322 () (_ FP 8 24) (* .3 .14 .321))
(define-fun .323 () (_ FP 8 24) (+ .3 .12 .322))
(define-fun .326 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.246000006794929504395)))
(define-fun .327 () (_ FP 8 24) (* .3 .18 .326))
(define-fun .328 () (_ FP 8 24) (+ .3 .323 .327))
(define-fun .330 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.643999993801116943359))
(define-fun .331 () (_ FP 8 24) (* .3 .22 .330))
(define-fun .332 () (_ FP 8 24) (+ .3 .328 .331))
(define-fun .334 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.518999993801116943359))
(define-fun .335 () (_ FP 8 24) (* .3 .26 .334))
(define-fun .336 () (_ FP 8 24) (+ .3 .332 .335))
(define-fun .338 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.402999997138977050781))
(define-fun .339 () (_ FP 8 24) (* .3 .30 .338))
(define-fun .340 () (_ FP 8 24) (+ .3 .336 .339))
(define-fun .342 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.449999988079071044922))
(define-fun .343 () (_ FP 8 24) (* .3 .34 .342))
(define-fun .344 () (_ FP 8 24) (+ .3 .340 .343))
(define-fun .345 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.643999993801116943359)))
(define-fun .346 () (_ FP 8 24) (* .3 .38 .345))
(define-fun .347 () (_ FP 8 24) (+ .3 .344 .346))
(define-fun .348 () Bool (<= .319 .347))
(assert .348)
(define-fun .350 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.617999970912933349609))
(define-fun .353 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.728999972343444824219)))
(define-fun .354 () (_ FP 8 24) (* .3 .18 .353))
(define-fun .355 () (_ FP 8 24) (+ .3 .289 .354))
(define-fun .357 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.537000000476837158203))
(define-fun .358 () (_ FP 8 24) (* .3 .22 .357))
(define-fun .359 () (_ FP 8 24) (+ .3 .355 .358))
(define-fun .361 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.837000012397766113281))
(define-fun .362 () (_ FP 8 24) (* .3 .26 .361))
(define-fun .363 () (_ FP 8 24) (+ .3 .359 .362))
(define-fun .366 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.8090000152587890625)))
(define-fun .367 () (_ FP 8 24) (* .3 .30 .366))
(define-fun .368 () (_ FP 8 24) (+ .3 .363 .367))
(define-fun .370 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.829999983310699462891))
(define-fun .371 () (_ FP 8 24) (* .3 .34 .370))
(define-fun .372 () (_ FP 8 24) (+ .3 .368 .371))
(define-fun .375 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.797999978065490722656)))
(define-fun .376 () (_ FP 8 24) (* .3 .38 .375))
(define-fun .377 () (_ FP 8 24) (+ .3 .372 .376))
(define-fun .378 () Bool (<= .377 .350))
(assert .378)
(define-fun .381 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.693000018596649169922)))
(define-fun .383 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.763000011444091796875))
(define-fun .384 () (_ FP 8 24) (* .3 .14 .383))
(define-fun .385 () (_ FP 8 24) (+ .3 .12 .384))
(define-fun .388 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.182999998331069946289)))
(define-fun .389 () (_ FP 8 24) (* .3 .18 .388))
(define-fun .390 () (_ FP 8 24) (+ .3 .385 .389))
(define-fun .391 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.518999993801116943359)))
(define-fun .392 () (_ FP 8 24) (* .3 .22 .391))
(define-fun .393 () (_ FP 8 24) (+ .3 .390 .392))
(define-fun .394 () (_ FP 8 24) (* .3 .26 .188))
(define-fun .395 () (_ FP 8 24) (+ .3 .393 .394))
(define-fun .397 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.832000017166137695313))
(define-fun .398 () (_ FP 8 24) (* .3 .30 .397))
(define-fun .399 () (_ FP 8 24) (+ .3 .395 .398))
(define-fun .401 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0769999995827674865723))
(define-fun .402 () (_ FP 8 24) (* .3 .34 .401))
(define-fun .403 () (_ FP 8 24) (+ .3 .399 .402))
(define-fun .405 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.16099999845027923584))
(define-fun .406 () (_ FP 8 24) (* .3 .38 .405))
(define-fun .407 () (_ FP 8 24) (+ .3 .403 .406))
(define-fun .408 () Bool (<= .407 .381))
(assert .408)
(define-fun .410 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.104000002145767211914))
(define-fun .412 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.449000000953674316406))
(define-fun .413 () (_ FP 8 24) (* .3 .14 .412))
(define-fun .414 () (_ FP 8 24) (+ .3 .12 .413))
(define-fun .416 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.704999983310699462891))
(define-fun .417 () (_ FP 8 24) (* .3 .18 .416))
(define-fun .418 () (_ FP 8 24) (+ .3 .414 .417))
(define-fun .420 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.448000013828277587891))
(define-fun .421 () (_ FP 8 24) (* .3 .22 .420))
(define-fun .422 () (_ FP 8 24) (+ .3 .418 .421))
(define-fun .423 () (_ FP 8 24) (* .3 .26 .353))
(define-fun .424 () (_ FP 8 24) (+ .3 .422 .423))
(define-fun .426 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.217999994754791259766))
(define-fun .427 () (_ FP 8 24) (* .3 .30 .426))
(define-fun .428 () (_ FP 8 24) (+ .3 .424 .427))
(define-fun .430 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.634999990463256835938))
(define-fun .431 () (_ FP 8 24) (* .3 .34 .430))
(define-fun .432 () (_ FP 8 24) (+ .3 .428 .431))
(define-fun .434 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.720000028610229492188))
(define-fun .435 () (_ FP 8 24) (* .3 .38 .434))
(define-fun .436 () (_ FP 8 24) (+ .3 .432 .435))
(define-fun .437 () Bool (<= .436 .410))
(assert .437)
(check-sat)
