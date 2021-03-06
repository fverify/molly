(set-logic QF_FPABV)
(declare-fun x0 () (_ FP 8 24))
(declare-fun x1 () (_ FP 8 24))
(declare-fun x2 () (_ FP 8 24))
(declare-fun x3 () (_ FP 8 24))
(declare-fun x4 () (_ FP 8 24))
(declare-fun x5 () (_ FP 8 24))
(declare-fun x6 () (_ FP 8 24))
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
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.984000027179718017578)))
(define-fun .50 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00999999977648258209229))
(define-fun .51 () (_ FP 8 24) (* .3 .14 .50))
(define-fun .52 () (_ FP 8 24) (+ .3 .12 .51))
(define-fun .54 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.286000013351440429688))
(define-fun .55 () (_ FP 8 24) (* .3 .18 .54))
(define-fun .56 () (_ FP 8 24) (+ .3 .52 .55))
(define-fun .59 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.774999976158142089844)))
(define-fun .60 () (_ FP 8 24) (* .3 .22 .59))
(define-fun .61 () (_ FP 8 24) (+ .3 .56 .60))
(define-fun .63 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.912999987602233886719))
(define-fun .64 () (_ FP 8 24) (* .3 .26 .63))
(define-fun .65 () (_ FP 8 24) (+ .3 .61 .64))
(define-fun .68 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.727999985218048095703)))
(define-fun .69 () (_ FP 8 24) (* .3 .30 .68))
(define-fun .70 () (_ FP 8 24) (+ .3 .65 .69))
(define-fun .73 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.888999998569488525391)))
(define-fun .74 () (_ FP 8 24) (* .3 .34 .73))
(define-fun .75 () (_ FP 8 24) (+ .3 .70 .74))
(define-fun .77 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.716000020503997802734))
(define-fun .78 () (_ FP 8 24) (* .3 .38 .77))
(define-fun .79 () (_ FP 8 24) (+ .3 .75 .78))
(define-fun .80 () Bool (<= .48 .79))
(assert .80)
(define-fun .83 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.185000002384185791016)))
(define-fun .86 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0810000002384185791016)))
(define-fun .87 () (_ FP 8 24) (* .3 .14 .86))
(define-fun .88 () (_ FP 8 24) (+ .3 .12 .87))
(define-fun .90 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.168999999761581420898))
(define-fun .91 () (_ FP 8 24) (* .3 .18 .90))
(define-fun .92 () (_ FP 8 24) (+ .3 .88 .91))
(define-fun .95 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.335000008344650268555)))
(define-fun .96 () (_ FP 8 24) (* .3 .22 .95))
(define-fun .97 () (_ FP 8 24) (+ .3 .92 .96))
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.261000007390975952148))
(define-fun .100 () (_ FP 8 24) (* .3 .26 .99))
(define-fun .101 () (_ FP 8 24) (+ .3 .97 .100))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.217999994754791259766))
(define-fun .104 () (_ FP 8 24) (* .3 .30 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .101 .104))
(define-fun .108 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.602999985218048095703)))
(define-fun .109 () (_ FP 8 24) (* .3 .34 .108))
(define-fun .110 () (_ FP 8 24) (+ .3 .105 .109))
(define-fun .112 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.681999981403350830078))
(define-fun .113 () (_ FP 8 24) (* .3 .38 .112))
(define-fun .114 () (_ FP 8 24) (+ .3 .110 .113))
(define-fun .115 () Bool (<= .83 .114))
(assert .115)
(define-fun .118 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.370000004768371582031)))
(define-fun .120 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.660000026226043701172))
(define-fun .121 () (_ FP 8 24) (* .3 .14 .120))
(define-fun .122 () (_ FP 8 24) (+ .3 .12 .121))
(define-fun .125 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0860000029206275939941)))
(define-fun .126 () (_ FP 8 24) (* .3 .18 .125))
(define-fun .127 () (_ FP 8 24) (+ .3 .122 .126))
(define-fun .130 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.709999978542327880859)))
(define-fun .131 () (_ FP 8 24) (* .3 .22 .130))
(define-fun .132 () (_ FP 8 24) (+ .3 .127 .131))
(define-fun .134 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.813000023365020751953))
(define-fun .135 () (_ FP 8 24) (* .3 .26 .134))
(define-fun .136 () (_ FP 8 24) (+ .3 .132 .135))
(define-fun .139 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.550999999046325683594)))
(define-fun .140 () (_ FP 8 24) (* .3 .30 .139))
(define-fun .141 () (_ FP 8 24) (+ .3 .136 .140))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0879999995231628417969)))
(define-fun .145 () (_ FP 8 24) (* .3 .34 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .141 .145))
(define-fun .149 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.488999992609024047852)))
(define-fun .150 () (_ FP 8 24) (* .3 .38 .149))
(define-fun .151 () (_ FP 8 24) (+ .3 .146 .150))
(define-fun .152 () Bool (<= .151 .118))
(assert .152)
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.335000008344650268555))
(define-fun .154 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.842999994754791259766))
(define-fun .155 () (_ FP 8 24) (* .3 .14 .94))
(define-fun .156 () (_ FP 8 24) (+ .3 .12 .155))
(define-fun .159 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.202000007033348083496)))
(define-fun .160 () (_ FP 8 24) (* .3 .18 .159))
(define-fun .161 () (_ FP 8 24) (+ .3 .156 .160))
(define-fun .164 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.361999988555908203125)))
(define-fun .165 () (_ FP 8 24) (* .3 .22 .164))
(define-fun .166 () (_ FP 8 24) (+ .3 .161 .165))
(define-fun .169 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.601999998092651367188)))
(define-fun .170 () (_ FP 8 24) (* .3 .26 .169))
(define-fun .171 () (_ FP 8 24) (+ .3 .166 .170))
(define-fun .174 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.917999982833862304688)))
(define-fun .175 () (_ FP 8 24) (* .3 .30 .174))
(define-fun .176 () (_ FP 8 24) (+ .3 .171 .175))
(define-fun .178 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.961000025272369384766))
(define-fun .179 () (_ FP 8 24) (* .3 .34 .178))
(define-fun .180 () (_ FP 8 24) (+ .3 .176 .179))
(define-fun .182 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.944999992847442626953))
(define-fun .183 () (_ FP 8 24) (* .3 .38 .182))
(define-fun .184 () (_ FP 8 24) (+ .3 .180 .183))
(define-fun .185 () Bool (<= .154 .184))
(assert .185)
(define-fun .188 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.319999992847442626953)))
(define-fun .191 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.987999975681304931641)))
(define-fun .192 () (_ FP 8 24) (* .3 .14 .191))
(define-fun .193 () (_ FP 8 24) (+ .3 .12 .192))
(define-fun .196 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0820000022649765014648)))
(define-fun .197 () (_ FP 8 24) (* .3 .18 .196))
(define-fun .198 () (_ FP 8 24) (+ .3 .193 .197))
(define-fun .201 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.524999976158142089844)))
(define-fun .202 () (_ FP 8 24) (* .3 .22 .201))
(define-fun .203 () (_ FP 8 24) (+ .3 .198 .202))
(define-fun .205 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.344000011682510375977))
(define-fun .206 () (_ FP 8 24) (* .3 .26 .205))
(define-fun .207 () (_ FP 8 24) (+ .3 .203 .206))
(define-fun .209 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.924000024795532226563))
(define-fun .210 () (_ FP 8 24) (* .3 .30 .209))
(define-fun .211 () (_ FP 8 24) (+ .3 .207 .210))
(define-fun .214 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.9409999847412109375)))
(define-fun .215 () (_ FP 8 24) (* .3 .34 .214))
(define-fun .216 () (_ FP 8 24) (+ .3 .211 .215))
(define-fun .219 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.261999994516372680664)))
(define-fun .220 () (_ FP 8 24) (* .3 .38 .219))
(define-fun .221 () (_ FP 8 24) (+ .3 .216 .220))
(define-fun .222 () Bool (<= .221 .188))
(assert .222)
(define-fun .225 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.982999980449676513672)))
(define-fun .226 () (_ FP 8 24) (* .3 .14 .225))
(define-fun .227 () (_ FP 8 24) (+ .3 .12 .226))
(define-fun .229 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.314999997615814208984))
(define-fun .230 () (_ FP 8 24) (* .3 .18 .229))
(define-fun .231 () (_ FP 8 24) (+ .3 .227 .230))
(define-fun .233 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.293000012636184692383))
(define-fun .234 () (_ FP 8 24) (* .3 .22 .233))
(define-fun .235 () (_ FP 8 24) (+ .3 .231 .234))
(define-fun .238 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0630000010132789611816)))
(define-fun .239 () (_ FP 8 24) (* .3 .26 .238))
(define-fun .240 () (_ FP 8 24) (+ .3 .235 .239))
(define-fun .243 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00400000018998980522156)))
(define-fun .244 () (_ FP 8 24) (* .3 .30 .243))
(define-fun .245 () (_ FP 8 24) (+ .3 .240 .244))
(define-fun .246 () (_ FP 8 24) (+ .3 .109 .245))
(define-fun .249 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.930999994277954101563)))
(define-fun .250 () (_ FP 8 24) (* .3 .38 .249))
(define-fun .251 () (_ FP 8 24) (+ .3 .246 .250))
(define-fun .252 () Bool (<= .149 .251))
(assert .252)
(define-fun .254 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.259000003337860107422))
(define-fun .256 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0240000002086162567139))
(define-fun .257 () (_ FP 8 24) (* .3 .14 .256))
(define-fun .258 () (_ FP 8 24) (+ .3 .12 .257))
(define-fun .260 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.577000021934509277344))
(define-fun .261 () (_ FP 8 24) (* .3 .18 .260))
(define-fun .262 () (_ FP 8 24) (+ .3 .258 .261))
(define-fun .265 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.115000002086162567139)))
(define-fun .266 () (_ FP 8 24) (* .3 .22 .265))
(define-fun .267 () (_ FP 8 24) (+ .3 .262 .266))
(define-fun .270 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.52600002288818359375)))
(define-fun .271 () (_ FP 8 24) (* .3 .26 .270))
(define-fun .272 () (_ FP 8 24) (+ .3 .267 .271))
(define-fun .274 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.804000020027160644531))
(define-fun .275 () (_ FP 8 24) (* .3 .30 .274))
(define-fun .276 () (_ FP 8 24) (+ .3 .272 .275))
(define-fun .279 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.224999994039535522461)))
(define-fun .280 () (_ FP 8 24) (* .3 .34 .279))
(define-fun .281 () (_ FP 8 24) (+ .3 .276 .280))
(define-fun .283 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.231000006198883056641))
(define-fun .284 () (_ FP 8 24) (* .3 .38 .283))
(define-fun .285 () (_ FP 8 24) (+ .3 .281 .284))
(define-fun .286 () Bool (<= .254 .285))
(assert .286)
(define-fun .288 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.284999996423721313477))
(define-fun .290 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.241999998688697814941))
(define-fun .291 () (_ FP 8 24) (* .3 .14 .290))
(define-fun .292 () (_ FP 8 24) (+ .3 .12 .291))
(define-fun .295 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.643999993801116943359)))
(define-fun .296 () (_ FP 8 24) (* .3 .18 .295))
(define-fun .297 () (_ FP 8 24) (+ .3 .292 .296))
(define-fun .299 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0299999993294477462769))
(define-fun .300 () (_ FP 8 24) (* .3 .22 .299))
(define-fun .301 () (_ FP 8 24) (+ .3 .297 .300))
(define-fun .302 () (_ FP 8 24) (+ .3 .239 .301))
(define-fun .304 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0250000003725290298462))
(define-fun .305 () (_ FP 8 24) (* .3 .30 .304))
(define-fun .306 () (_ FP 8 24) (+ .3 .302 .305))
(define-fun .309 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.529999971389770507813)))
(define-fun .310 () (_ FP 8 24) (* .3 .34 .309))
(define-fun .311 () (_ FP 8 24) (+ .3 .306 .310))
(define-fun .314 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.507000029087066650391)))
(define-fun .315 () (_ FP 8 24) (* .3 .38 .314))
(define-fun .316 () (_ FP 8 24) (+ .3 .311 .315))
(define-fun .317 () Bool (<= .288 .316))
(assert .317)
(define-fun .319 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.694999992847442626953))
(define-fun .321 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.391000002622604370117))
(define-fun .322 () (_ FP 8 24) (* .3 .14 .321))
(define-fun .323 () (_ FP 8 24) (+ .3 .12 .322))
(define-fun .324 () (_ FP 8 24) (* .3 .18 .120))
(define-fun .325 () (_ FP 8 24) (+ .3 .323 .324))
(define-fun .328 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.24699999392032623291)))
(define-fun .329 () (_ FP 8 24) (* .3 .22 .328))
(define-fun .330 () (_ FP 8 24) (+ .3 .325 .329))
(define-fun .331 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.716000020503997802734)))
(define-fun .332 () (_ FP 8 24) (* .3 .26 .331))
(define-fun .333 () (_ FP 8 24) (+ .3 .330 .332))
(define-fun .335 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.150999993085861206055))
(define-fun .336 () (_ FP 8 24) (* .3 .30 .335))
(define-fun .337 () (_ FP 8 24) (+ .3 .333 .336))
(define-fun .339 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.910000026226043701172))
(define-fun .340 () (_ FP 8 24) (* .3 .34 .339))
(define-fun .341 () (_ FP 8 24) (+ .3 .337 .340))
(define-fun .344 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.211999997496604919434)))
(define-fun .345 () (_ FP 8 24) (* .3 .38 .344))
(define-fun .346 () (_ FP 8 24) (+ .3 .341 .345))
(define-fun .347 () Bool (<= .346 .319))
(assert .347)
(define-fun .348 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.660000026226043701172)))
(define-fun .349 () (_ FP 8 24) (* .3 .14 .348))
(define-fun .350 () (_ FP 8 24) (+ .3 .12 .349))
(define-fun .353 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.745000004768371582031)))
(define-fun .354 () (_ FP 8 24) (* .3 .18 .353))
(define-fun .355 () (_ FP 8 24) (+ .3 .350 .354))
(define-fun .356 () (_ FP 8 24) (* .3 .22 .83))
(define-fun .357 () (_ FP 8 24) (+ .3 .355 .356))
(define-fun .360 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.592999994754791259766)))
(define-fun .361 () (_ FP 8 24) (* .3 .26 .360))
(define-fun .362 () (_ FP 8 24) (+ .3 .357 .361))
(define-fun .365 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.788999974727630615234)))
(define-fun .366 () (_ FP 8 24) (* .3 .30 .365))
(define-fun .367 () (_ FP 8 24) (+ .3 .362 .366))
(define-fun .369 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.405000001192092895508))
(define-fun .370 () (_ FP 8 24) (* .3 .34 .369))
(define-fun .371 () (_ FP 8 24) (+ .3 .367 .370))
(define-fun .373 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0949999988079071044922))
(define-fun .374 () (_ FP 8 24) (* .3 .38 .373))
(define-fun .375 () (_ FP 8 24) (+ .3 .371 .374))
(define-fun .376 () Bool (<= .256 .375))
(assert .376)
(define-fun .378 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.153999999165534973145))
(define-fun .381 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.423999994993209838867)))
(define-fun .382 () (_ FP 8 24) (* .3 .14 .381))
(define-fun .383 () (_ FP 8 24) (+ .3 .12 .382))
(define-fun .385 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.363999992609024047852))
(define-fun .386 () (_ FP 8 24) (* .3 .18 .385))
(define-fun .387 () (_ FP 8 24) (+ .3 .383 .386))
(define-fun .389 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.30300000309944152832))
(define-fun .390 () (_ FP 8 24) (* .3 .22 .389))
(define-fun .391 () (_ FP 8 24) (+ .3 .387 .390))
(define-fun .393 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.790000021457672119141))
(define-fun .394 () (_ FP 8 24) (* .3 .26 .393))
(define-fun .395 () (_ FP 8 24) (+ .3 .391 .394))
(define-fun .397 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00600000005215406417847))
(define-fun .398 () (_ FP 8 24) (* .3 .30 .397))
(define-fun .399 () (_ FP 8 24) (+ .3 .395 .398))
(define-fun .402 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.679000020027160644531)))
(define-fun .403 () (_ FP 8 24) (* .3 .34 .402))
(define-fun .404 () (_ FP 8 24) (+ .3 .399 .403))
(define-fun .406 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.465999990701675415039))
(define-fun .407 () (_ FP 8 24) (* .3 .38 .406))
(define-fun .408 () (_ FP 8 24) (+ .3 .404 .407))
(define-fun .409 () Bool (<= .378 .408))
(assert .409)
(define-fun .412 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.959999978542327880859)))
(define-fun .415 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.523999989032745361328)))
(define-fun .416 () (_ FP 8 24) (* .3 .14 .415))
(define-fun .417 () (_ FP 8 24) (+ .3 .12 .416))
(define-fun .420 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.136999994516372680664)))
(define-fun .421 () (_ FP 8 24) (* .3 .18 .420))
(define-fun .422 () (_ FP 8 24) (+ .3 .417 .421))
(define-fun .425 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.646000027656555175781)))
(define-fun .426 () (_ FP 8 24) (* .3 .22 .425))
(define-fun .427 () (_ FP 8 24) (+ .3 .422 .426))
(define-fun .430 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.395999997854232788086)))
(define-fun .431 () (_ FP 8 24) (* .3 .26 .430))
(define-fun .432 () (_ FP 8 24) (+ .3 .427 .431))
(define-fun .435 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.791000008583068847656)))
(define-fun .436 () (_ FP 8 24) (* .3 .30 .435))
(define-fun .437 () (_ FP 8 24) (+ .3 .432 .436))
(define-fun .439 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.758000016212463378906))
(define-fun .440 () (_ FP 8 24) (* .3 .34 .439))
(define-fun .441 () (_ FP 8 24) (+ .3 .437 .440))
(define-fun .444 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0850000008940696716309)))
(define-fun .445 () (_ FP 8 24) (* .3 .38 .444))
(define-fun .446 () (_ FP 8 24) (+ .3 .441 .445))
(define-fun .447 () Bool (<= .412 .446))
(assert .447)
(check-sat)
