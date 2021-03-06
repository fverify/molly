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
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.893000006675720214844)))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.328000009059906005859))
(define-fun .51 () (_ FP 8 24) (* .3 .14 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .12 .51))
(define-fun .54 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.982999980449676513672))
(define-fun .55 () (_ FP 8 24) (* .3 .18 .54))
(define-fun .56 () (_ FP 8 24) (+ .3 .52 .55))
(define-fun .59 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.298000007867813110352)))
(define-fun .60 () (_ FP 8 24) (* .3 .22 .59))
(define-fun .61 () (_ FP 8 24) (+ .3 .56 .60))
(define-fun .64 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.917999982833862304688)))
(define-fun .65 () (_ FP 8 24) (* .3 .26 .64))
(define-fun .66 () (_ FP 8 24) (+ .3 .61 .65))
(define-fun .69 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.187999993562698364258)))
(define-fun .70 () (_ FP 8 24) (* .3 .30 .69))
(define-fun .71 () (_ FP 8 24) (+ .3 .66 .70))
(define-fun .74 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.730000019073486328125)))
(define-fun .75 () (_ FP 8 24) (* .3 .34 .74))
(define-fun .76 () (_ FP 8 24) (+ .3 .71 .75))
(define-fun .78 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.638999998569488525391))
(define-fun .79 () (_ FP 8 24) (* .3 .38 .78))
(define-fun .80 () (_ FP 8 24) (+ .3 .76 .79))
(define-fun .81 () Bool (<= .48 .80))
(assert .81)
(define-fun .83 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.579999983310699462891))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.42800000309944152832))
(define-fun .86 () (_ FP 8 24) (* .3 .14 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .12 .86))
(define-fun .89 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.208000004291534423828))
(define-fun .90 () (_ FP 8 24) (* .3 .18 .89))
(define-fun .91 () (_ FP 8 24) (+ .3 .87 .90))
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.289999991655349731445)))
(define-fun .95 () (_ FP 8 24) (* .3 .22 .94))
(define-fun .96 () (_ FP 8 24) (+ .3 .91 .95))
(define-fun .98 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.532000005245208740234))
(define-fun .99 () (_ FP 8 24) (* .3 .26 .98))
(define-fun .100 () (_ FP 8 24) (+ .3 .96 .99))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.804000020027160644531)))
(define-fun .104 () (_ FP 8 24) (* .3 .30 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .100 .104))
(define-fun .108 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.146999999880790710449)))
(define-fun .109 () (_ FP 8 24) (* .3 .34 .108))
(define-fun .110 () (_ FP 8 24) (+ .3 .105 .109))
(define-fun .113 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.268000006675720214844)))
(define-fun .114 () (_ FP 8 24) (* .3 .38 .113))
(define-fun .115 () (_ FP 8 24) (+ .3 .110 .114))
(define-fun .116 () Bool (<= .83 .115))
(assert .116)
(define-fun .119 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.287999987602233886719)))
(define-fun .122 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.740000009536743164063)))
(define-fun .123 () (_ FP 8 24) (* .3 .14 .122))
(define-fun .124 () (_ FP 8 24) (+ .3 .12 .123))
(define-fun .126 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.405000001192092895508))
(define-fun .127 () (_ FP 8 24) (* .3 .18 .126))
(define-fun .128 () (_ FP 8 24) (+ .3 .124 .127))
(define-fun .131 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.402999997138977050781)))
(define-fun .132 () (_ FP 8 24) (* .3 .22 .131))
(define-fun .133 () (_ FP 8 24) (+ .3 .128 .132))
(define-fun .136 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.919000029563903808594)))
(define-fun .137 () (_ FP 8 24) (* .3 .26 .136))
(define-fun .138 () (_ FP 8 24) (+ .3 .133 .137))
(define-fun .141 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.192000001668930053711)))
(define-fun .142 () (_ FP 8 24) (* .3 .30 .141))
(define-fun .143 () (_ FP 8 24) (+ .3 .138 .142))
(define-fun .146 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.712000012397766113281)))
(define-fun .147 () (_ FP 8 24) (* .3 .34 .146))
(define-fun .148 () (_ FP 8 24) (+ .3 .143 .147))
(define-fun .150 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.324999988079071044922))
(define-fun .151 () (_ FP 8 24) (* .3 .38 .150))
(define-fun .152 () (_ FP 8 24) (+ .3 .148 .151))
(define-fun .153 () Bool (<= .152 .119))
(assert .153)
(define-fun .156 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.483999997377395629883)))
(define-fun .158 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0359999984502792358398))
(define-fun .159 () (_ FP 8 24) (* .3 .14 .158))
(define-fun .160 () (_ FP 8 24) (+ .3 .12 .159))
(define-fun .162 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.342999994754791259766))
(define-fun .163 () (_ FP 8 24) (* .3 .18 .162))
(define-fun .164 () (_ FP 8 24) (+ .3 .160 .163))
(define-fun .167 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.112999998033046722412)))
(define-fun .168 () (_ FP 8 24) (* .3 .22 .167))
(define-fun .169 () (_ FP 8 24) (+ .3 .164 .168))
(define-fun .171 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.778999984264373779297))
(define-fun .172 () (_ FP 8 24) (* .3 .26 .171))
(define-fun .173 () (_ FP 8 24) (+ .3 .169 .172))
(define-fun .176 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.663999974727630615234)))
(define-fun .177 () (_ FP 8 24) (* .3 .30 .176))
(define-fun .178 () (_ FP 8 24) (+ .3 .173 .177))
(define-fun .180 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.483000010251998901367))
(define-fun .181 () (_ FP 8 24) (* .3 .34 .180))
(define-fun .182 () (_ FP 8 24) (+ .3 .178 .181))
(define-fun .185 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.172999992966651916504)))
(define-fun .186 () (_ FP 8 24) (* .3 .38 .185))
(define-fun .187 () (_ FP 8 24) (+ .3 .182 .186))
(define-fun .188 () Bool (<= .156 .187))
(assert .188)
(define-fun .47 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.893000006675720214844))
(define-fun .190 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.307000011205673217773))
(define-fun .193 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.614000022411346435547)))
(define-fun .194 () (_ FP 8 24) (* .3 .14 .193))
(define-fun .195 () (_ FP 8 24) (+ .3 .12 .194))
(define-fun .198 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.758000016212463378906)))
(define-fun .199 () (_ FP 8 24) (* .3 .18 .198))
(define-fun .200 () (_ FP 8 24) (+ .3 .195 .199))
(define-fun .202 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.550000011920928955078))
(define-fun .203 () (_ FP 8 24) (* .3 .22 .202))
(define-fun .204 () (_ FP 8 24) (+ .3 .200 .203))
(define-fun .207 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.104999996721744537354)))
(define-fun .208 () (_ FP 8 24) (* .3 .26 .207))
(define-fun .209 () (_ FP 8 24) (+ .3 .204 .208))
(define-fun .211 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.412000000476837158203))
(define-fun .212 () (_ FP 8 24) (* .3 .30 .211))
(define-fun .213 () (_ FP 8 24) (+ .3 .209 .212))
(define-fun .214 () (_ FP 8 24) (* .3 .34 .47))
(define-fun .215 () (_ FP 8 24) (+ .3 .213 .214))
(define-fun .218 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.497999995946884155273)))
(define-fun .219 () (_ FP 8 24) (* .3 .38 .218))
(define-fun .220 () (_ FP 8 24) (+ .3 .215 .219))
(define-fun .221 () Bool (<= .220 .190))
(assert .221)
(define-fun .223 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.759999990463256835938))
(define-fun .226 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.705999970436096191406)))
(define-fun .227 () (_ FP 8 24) (* .3 .14 .226))
(define-fun .228 () (_ FP 8 24) (+ .3 .12 .227))
(define-fun .230 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.9409999847412109375))
(define-fun .231 () (_ FP 8 24) (* .3 .18 .230))
(define-fun .232 () (_ FP 8 24) (+ .3 .228 .231))
(define-fun .234 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.846000015735626220703))
(define-fun .235 () (_ FP 8 24) (* .3 .22 .234))
(define-fun .236 () (_ FP 8 24) (+ .3 .232 .235))
(define-fun .239 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.725000023841857910156)))
(define-fun .240 () (_ FP 8 24) (* .3 .26 .239))
(define-fun .241 () (_ FP 8 24) (+ .3 .236 .240))
(define-fun .244 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.827000021934509277344)))
(define-fun .245 () (_ FP 8 24) (* .3 .30 .244))
(define-fun .246 () (_ FP 8 24) (+ .3 .241 .245))
(define-fun .248 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.127000004053115844727))
(define-fun .249 () (_ FP 8 24) (* .3 .34 .248))
(define-fun .250 () (_ FP 8 24) (+ .3 .246 .249))
(define-fun .253 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.28299999237060546875)))
(define-fun .254 () (_ FP 8 24) (* .3 .38 .253))
(define-fun .255 () (_ FP 8 24) (+ .3 .250 .254))
(define-fun .256 () Bool (<= .255 .223))
(assert .256)
(define-fun .259 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.649999976158142089844)))
(define-fun .262 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.533999979496002197266)))
(define-fun .263 () (_ FP 8 24) (* .3 .14 .262))
(define-fun .264 () (_ FP 8 24) (+ .3 .12 .263))
(define-fun .266 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.902999997138977050781))
(define-fun .267 () (_ FP 8 24) (* .3 .18 .266))
(define-fun .268 () (_ FP 8 24) (+ .3 .264 .267))
(define-fun .270 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.572000026702880859375))
(define-fun .271 () (_ FP 8 24) (* .3 .22 .270))
(define-fun .272 () (_ FP 8 24) (+ .3 .268 .271))
(define-fun .275 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.23299999535083770752)))
(define-fun .276 () (_ FP 8 24) (* .3 .26 .275))
(define-fun .277 () (_ FP 8 24) (+ .3 .272 .276))
(define-fun .279 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.564999997615814208984))
(define-fun .280 () (_ FP 8 24) (* .3 .30 .279))
(define-fun .281 () (_ FP 8 24) (+ .3 .277 .280))
(define-fun .283 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.206000000238418579102))
(define-fun .284 () (_ FP 8 24) (* .3 .34 .283))
(define-fun .285 () (_ FP 8 24) (+ .3 .281 .284))
(define-fun .287 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.416999995708465576172))
(define-fun .288 () (_ FP 8 24) (* .3 .38 .287))
(define-fun .289 () (_ FP 8 24) (+ .3 .285 .288))
(define-fun .290 () Bool (<= .289 .259))
(assert .290)
(define-fun .293 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.421999990940093994141)))
(define-fun .296 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.305000007152557373047)))
(define-fun .297 () (_ FP 8 24) (* .3 .14 .296))
(define-fun .298 () (_ FP 8 24) (+ .3 .12 .297))
(define-fun .300 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.689999997615814208984))
(define-fun .301 () (_ FP 8 24) (* .3 .18 .300))
(define-fun .302 () (_ FP 8 24) (+ .3 .298 .301))
(define-fun .304 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.540000021457672119141))
(define-fun .305 () (_ FP 8 24) (* .3 .22 .304))
(define-fun .306 () (_ FP 8 24) (+ .3 .302 .305))
(define-fun .308 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.929000020027160644531))
(define-fun .309 () (_ FP 8 24) (* .3 .26 .308))
(define-fun .310 () (_ FP 8 24) (+ .3 .306 .309))
(define-fun .312 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.156000003218650817871))
(define-fun .313 () (_ FP 8 24) (* .3 .30 .312))
(define-fun .314 () (_ FP 8 24) (+ .3 .310 .313))
(define-fun .317 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.509000003337860107422)))
(define-fun .318 () (_ FP 8 24) (* .3 .34 .317))
(define-fun .319 () (_ FP 8 24) (+ .3 .314 .318))
(define-fun .322 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.764999985694885253906)))
(define-fun .323 () (_ FP 8 24) (* .3 .38 .322))
(define-fun .324 () (_ FP 8 24) (+ .3 .319 .323))
(define-fun .325 () Bool (<= .324 .293))
(assert .325)
(define-fun .328 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.296000003814697265625)))
(define-fun .330 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0500000007450580596924))
(define-fun .331 () (_ FP 8 24) (* .3 .14 .330))
(define-fun .332 () (_ FP 8 24) (+ .3 .12 .331))
(define-fun .335 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.602999985218048095703)))
(define-fun .336 () (_ FP 8 24) (* .3 .18 .335))
(define-fun .337 () (_ FP 8 24) (+ .3 .332 .336))
(define-fun .339 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.851999998092651367188))
(define-fun .340 () (_ FP 8 24) (* .3 .22 .339))
(define-fun .341 () (_ FP 8 24) (+ .3 .337 .340))
(define-fun .343 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.180999994277954101563))
(define-fun .344 () (_ FP 8 24) (* .3 .26 .343))
(define-fun .345 () (_ FP 8 24) (+ .3 .341 .344))
(define-fun .347 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.282000005245208740234))
(define-fun .348 () (_ FP 8 24) (* .3 .30 .347))
(define-fun .349 () (_ FP 8 24) (+ .3 .345 .348))
(define-fun .351 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.204999998211860656738))
(define-fun .352 () (_ FP 8 24) (* .3 .34 .351))
(define-fun .353 () (_ FP 8 24) (+ .3 .349 .352))
(define-fun .354 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.483000010251998901367)))
(define-fun .355 () (_ FP 8 24) (* .3 .38 .354))
(define-fun .356 () (_ FP 8 24) (+ .3 .353 .355))
(define-fun .357 () Bool (<= .328 .356))
(assert .357)
(define-fun .360 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.899999976158142089844)))
(define-fun .363 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.589999973773956298828)))
(define-fun .364 () (_ FP 8 24) (* .3 .14 .363))
(define-fun .365 () (_ FP 8 24) (+ .3 .12 .364))
(define-fun .368 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.247999995946884155273)))
(define-fun .369 () (_ FP 8 24) (* .3 .18 .368))
(define-fun .370 () (_ FP 8 24) (+ .3 .365 .369))
(define-fun .372 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.467999994754791259766))
(define-fun .373 () (_ FP 8 24) (* .3 .22 .372))
(define-fun .374 () (_ FP 8 24) (+ .3 .370 .373))
(define-fun .376 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.841000020503997802734))
(define-fun .377 () (_ FP 8 24) (* .3 .26 .376))
(define-fun .378 () (_ FP 8 24) (+ .3 .374 .377))
(define-fun .380 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.912000000476837158203))
(define-fun .381 () (_ FP 8 24) (* .3 .30 .380))
(define-fun .382 () (_ FP 8 24) (+ .3 .378 .381))
(define-fun .384 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.514999985694885253906))
(define-fun .385 () (_ FP 8 24) (* .3 .34 .384))
(define-fun .386 () (_ FP 8 24) (+ .3 .382 .385))
(define-fun .388 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.261999994516372680664))
(define-fun .389 () (_ FP 8 24) (* .3 .38 .388))
(define-fun .390 () (_ FP 8 24) (+ .3 .386 .389))
(define-fun .391 () Bool (<= .390 .360))
(assert .391)
(define-fun .393 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.133000001311302185059))
(define-fun .396 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.634999990463256835938)))
(define-fun .397 () (_ FP 8 24) (* .3 .14 .396))
(define-fun .398 () (_ FP 8 24) (+ .3 .12 .397))
(define-fun .400 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.070000000298023223877))
(define-fun .401 () (_ FP 8 24) (* .3 .18 .400))
(define-fun .402 () (_ FP 8 24) (+ .3 .398 .401))
(define-fun .404 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0299999993294477462769))
(define-fun .405 () (_ FP 8 24) (* .3 .22 .404))
(define-fun .406 () (_ FP 8 24) (+ .3 .402 .405))
(define-fun .409 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0260000005364418029785)))
(define-fun .410 () (_ FP 8 24) (* .3 .26 .409))
(define-fun .411 () (_ FP 8 24) (+ .3 .406 .410))
(define-fun .413 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.870999991893768310547))
(define-fun .414 () (_ FP 8 24) (* .3 .30 .413))
(define-fun .415 () (_ FP 8 24) (+ .3 .411 .414))
(define-fun .417 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0869999974966049194336))
(define-fun .418 () (_ FP 8 24) (* .3 .34 .417))
(define-fun .419 () (_ FP 8 24) (+ .3 .415 .418))
(define-fun .422 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.853999972343444824219)))
(define-fun .423 () (_ FP 8 24) (* .3 .38 .422))
(define-fun .424 () (_ FP 8 24) (+ .3 .419 .423))
(define-fun .425 () Bool (<= .393 .424))
(assert .425)
(define-fun .428 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.787999987602233886719)))
(define-fun .429 () (_ FP 8 24) (* .3 .14 .428))
(define-fun .430 () (_ FP 8 24) (+ .3 .12 .429))
(define-fun .432 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.319999992847442626953))
(define-fun .433 () (_ FP 8 24) (* .3 .18 .432))
(define-fun .434 () (_ FP 8 24) (+ .3 .430 .433))
(define-fun .437 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.945999979972839355469)))
(define-fun .438 () (_ FP 8 24) (* .3 .22 .437))
(define-fun .439 () (_ FP 8 24) (+ .3 .434 .438))
(define-fun .440 () (_ FP 8 24) (* .3 .26 .131))
(define-fun .441 () (_ FP 8 24) (+ .3 .439 .440))
(define-fun .442 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.851999998092651367188)))
(define-fun .443 () (_ FP 8 24) (* .3 .30 .442))
(define-fun .444 () (_ FP 8 24) (+ .3 .441 .443))
(define-fun .446 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.388999998569488525391))
(define-fun .447 () (_ FP 8 24) (* .3 .34 .446))
(define-fun .448 () (_ FP 8 24) (+ .3 .444 .447))
(define-fun .450 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0879999995231628417969))
(define-fun .451 () (_ FP 8 24) (* .3 .38 .450))
(define-fun .452 () (_ FP 8 24) (+ .3 .448 .451))
(define-fun .453 () Bool (<= .103 .452))
(assert .453)
(define-fun .455 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.345999985933303833008))
(define-fun .458 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.796999990940093994141)))
(define-fun .459 () (_ FP 8 24) (* .3 .14 .458))
(define-fun .460 () (_ FP 8 24) (+ .3 .12 .459))
(define-fun .463 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.694999992847442626953)))
(define-fun .464 () (_ FP 8 24) (* .3 .18 .463))
(define-fun .465 () (_ FP 8 24) (+ .3 .460 .464))
(define-fun .466 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.759999990463256835938)))
(define-fun .467 () (_ FP 8 24) (* .3 .22 .466))
(define-fun .468 () (_ FP 8 24) (+ .3 .465 .467))
(define-fun .471 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.954999983310699462891)))
(define-fun .472 () (_ FP 8 24) (* .3 .26 .471))
(define-fun .473 () (_ FP 8 24) (+ .3 .468 .472))
(define-fun .476 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.643999993801116943359)))
(define-fun .477 () (_ FP 8 24) (* .3 .30 .476))
(define-fun .478 () (_ FP 8 24) (+ .3 .473 .477))
(define-fun .481 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0599999986588954925537)))
(define-fun .482 () (_ FP 8 24) (* .3 .34 .481))
(define-fun .483 () (_ FP 8 24) (+ .3 .478 .482))
(define-fun .485 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.550999999046325683594))
(define-fun .486 () (_ FP 8 24) (* .3 .38 .485))
(define-fun .487 () (_ FP 8 24) (+ .3 .483 .486))
(define-fun .488 () Bool (<= .455 .487))
(assert .488)
(define-fun .102 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.804000020027160644531))
(define-fun .490 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.620000004768371582031))
(define-fun .491 () (_ FP 8 24) (* .3 .14 .102))
(define-fun .492 () (_ FP 8 24) (+ .3 .12 .491))
(define-fun .495 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.458999991416931152344)))
(define-fun .496 () (_ FP 8 24) (* .3 .18 .495))
(define-fun .497 () (_ FP 8 24) (+ .3 .492 .496))
(define-fun .499 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.828999996185302734375))
(define-fun .500 () (_ FP 8 24) (* .3 .22 .499))
(define-fun .501 () (_ FP 8 24) (+ .3 .497 .500))
(define-fun .504 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.883000016212463378906)))
(define-fun .505 () (_ FP 8 24) (* .3 .26 .504))
(define-fun .506 () (_ FP 8 24) (+ .3 .501 .505))
(define-fun .508 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.760999977588653564453))
(define-fun .509 () (_ FP 8 24) (* .3 .30 .508))
(define-fun .510 () (_ FP 8 24) (+ .3 .506 .509))
(define-fun .512 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.421000003814697265625))
(define-fun .513 () (_ FP 8 24) (* .3 .34 .512))
(define-fun .514 () (_ FP 8 24) (+ .3 .510 .513))
(define-fun .517 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.601999998092651367188)))
(define-fun .518 () (_ FP 8 24) (* .3 .38 .517))
(define-fun .519 () (_ FP 8 24) (+ .3 .514 .518))
(define-fun .520 () Bool (<= .519 .490))
(assert .520)
(define-fun .523 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.699999988079071044922)))
(define-fun .525 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.504000008106231689453))
(define-fun .526 () (_ FP 8 24) (* .3 .14 .525))
(define-fun .527 () (_ FP 8 24) (+ .3 .12 .526))
(define-fun .529 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.391000002622604370117))
(define-fun .530 () (_ FP 8 24) (* .3 .18 .529))
(define-fun .531 () (_ FP 8 24) (+ .3 .527 .530))
(define-fun .533 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.430999994277954101563))
(define-fun .534 () (_ FP 8 24) (* .3 .22 .533))
(define-fun .535 () (_ FP 8 24) (+ .3 .531 .534))
(define-fun .538 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.926999986171722412109)))
(define-fun .539 () (_ FP 8 24) (* .3 .26 .538))
(define-fun .540 () (_ FP 8 24) (+ .3 .535 .539))
(define-fun .542 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.326000005006790161133))
(define-fun .543 () (_ FP 8 24) (* .3 .30 .542))
(define-fun .544 () (_ FP 8 24) (+ .3 .540 .543))
(define-fun .546 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.836000025272369384766))
(define-fun .547 () (_ FP 8 24) (* .3 .34 .546))
(define-fun .548 () (_ FP 8 24) (+ .3 .544 .547))
(define-fun .550 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.671000003814697265625))
(define-fun .551 () (_ FP 8 24) (* .3 .38 .550))
(define-fun .552 () (_ FP 8 24) (+ .3 .548 .551))
(define-fun .553 () Bool (<= .552 .523))
(assert .553)
(define-fun .556 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0989999994635581970215)))
(define-fun .559 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.867999970912933349609)))
(define-fun .560 () (_ FP 8 24) (* .3 .14 .559))
(define-fun .561 () (_ FP 8 24) (+ .3 .12 .560))
(define-fun .564 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.104000002145767211914)))
(define-fun .565 () (_ FP 8 24) (* .3 .18 .564))
(define-fun .566 () (_ FP 8 24) (+ .3 .561 .565))
(define-fun .569 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.119000002741813659668)))
(define-fun .570 () (_ FP 8 24) (* .3 .22 .569))
(define-fun .571 () (_ FP 8 24) (+ .3 .566 .570))
(define-fun .573 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.652000010013580322266))
(define-fun .574 () (_ FP 8 24) (* .3 .26 .573))
(define-fun .575 () (_ FP 8 24) (+ .3 .571 .574))
(define-fun .578 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.186000004410743713379)))
(define-fun .579 () (_ FP 8 24) (* .3 .30 .578))
(define-fun .580 () (_ FP 8 24) (+ .3 .575 .579))
(define-fun .582 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.328999996185302734375))
(define-fun .583 () (_ FP 8 24) (* .3 .34 .582))
(define-fun .584 () (_ FP 8 24) (+ .3 .580 .583))
(define-fun .587 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.580999970436096191406)))
(define-fun .588 () (_ FP 8 24) (* .3 .38 .587))
(define-fun .589 () (_ FP 8 24) (+ .3 .584 .588))
(define-fun .590 () Bool (<= .589 .556))
(assert .590)
(define-fun .593 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.518999993801116943359)))
(define-fun .595 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.500999987125396728516))
(define-fun .596 () (_ FP 8 24) (* .3 .14 .595))
(define-fun .597 () (_ FP 8 24) (+ .3 .12 .596))
(define-fun .600 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.671999990940093994141)))
(define-fun .601 () (_ FP 8 24) (* .3 .18 .600))
(define-fun .602 () (_ FP 8 24) (+ .3 .597 .601))
(define-fun .604 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.889999985694885253906))
(define-fun .605 () (_ FP 8 24) (* .3 .22 .604))
(define-fun .606 () (_ FP 8 24) (+ .3 .602 .605))
(define-fun .608 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0410000011324882507324))
(define-fun .609 () (_ FP 8 24) (* .3 .26 .608))
(define-fun .610 () (_ FP 8 24) (+ .3 .606 .609))
(define-fun .612 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.365000009536743164063))
(define-fun .613 () (_ FP 8 24) (* .3 .30 .612))
(define-fun .614 () (_ FP 8 24) (+ .3 .610 .613))
(define-fun .617 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.773999989032745361328)))
(define-fun .618 () (_ FP 8 24) (* .3 .34 .617))
(define-fun .619 () (_ FP 8 24) (+ .3 .614 .618))
(define-fun .621 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.652999997138977050781))
(define-fun .622 () (_ FP 8 24) (* .3 .38 .621))
(define-fun .623 () (_ FP 8 24) (+ .3 .619 .622))
(define-fun .624 () Bool (<= .593 .623))
(assert .624)
(check-sat)
