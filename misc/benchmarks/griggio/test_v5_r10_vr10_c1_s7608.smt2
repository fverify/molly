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
(define-fun .40 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0509999990463256835938)))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.818000018596649169922)))
(define-fun .44 () (_ FP 8 24) (* .3 .14 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .12 .44))
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.702000021934509277344)))
(define-fun .49 () (_ FP 8 24) (* .3 .18 .48))
(define-fun .50 () (_ FP 8 24) (+ .3 .45 .49))
(define-fun .53 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0140000004321336746216)))
(define-fun .54 () (_ FP 8 24) (* .3 .22 .53))
(define-fun .55 () (_ FP 8 24) (+ .3 .50 .54))
(define-fun .58 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.155000001192092895508)))
(define-fun .59 () (_ FP 8 24) (* .3 .26 .58))
(define-fun .60 () (_ FP 8 24) (+ .3 .55 .59))
(define-fun .63 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.546000003814697265625)))
(define-fun .64 () (_ FP 8 24) (* .3 .30 .63))
(define-fun .65 () (_ FP 8 24) (+ .3 .60 .64))
(define-fun .66 () Bool (<= .65 .40))
(assert .66)
(define-fun .68 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.400000005960464477539))
(define-fun .71 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.428999990224838256836)))
(define-fun .72 () (_ FP 8 24) (* .3 .14 .71))
(define-fun .73 () (_ FP 8 24) (+ .3 .12 .72))
(define-fun .76 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.421000003814697265625)))
(define-fun .77 () (_ FP 8 24) (* .3 .18 .76))
(define-fun .78 () (_ FP 8 24) (+ .3 .73 .77))
(define-fun .80 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.521000027656555175781))
(define-fun .81 () (_ FP 8 24) (* .3 .22 .80))
(define-fun .82 () (_ FP 8 24) (+ .3 .78 .81))
(define-fun .85 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.734000027179718017578)))
(define-fun .86 () (_ FP 8 24) (* .3 .26 .85))
(define-fun .87 () (_ FP 8 24) (+ .3 .82 .86))
(define-fun .90 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.405000001192092895508)))
(define-fun .91 () (_ FP 8 24) (* .3 .30 .90))
(define-fun .92 () (_ FP 8 24) (+ .3 .87 .91))
(define-fun .93 () Bool (<= .68 .92))
(assert .93)
(define-fun .96 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.941999971866607666016)))
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.547999978065490722656)))
(define-fun .100 () (_ FP 8 24) (* .3 .14 .99))
(define-fun .101 () (_ FP 8 24) (+ .3 .12 .100))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0989999994635581970215))
(define-fun .104 () (_ FP 8 24) (* .3 .18 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .101 .104))
(define-fun .108 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.958000004291534423828)))
(define-fun .109 () (_ FP 8 24) (* .3 .22 .108))
(define-fun .110 () (_ FP 8 24) (+ .3 .105 .109))
(define-fun .112 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.556999981403350830078))
(define-fun .113 () (_ FP 8 24) (* .3 .26 .112))
(define-fun .114 () (_ FP 8 24) (+ .3 .110 .113))
(define-fun .116 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.231000006198883056641))
(define-fun .117 () (_ FP 8 24) (* .3 .30 .116))
(define-fun .118 () (_ FP 8 24) (+ .3 .114 .117))
(define-fun .119 () Bool (<= .118 .96))
(assert .119)
(define-fun .121 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.851000010967254638672))
(define-fun .124 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.266000002622604370117)))
(define-fun .125 () (_ FP 8 24) (* .3 .14 .124))
(define-fun .126 () (_ FP 8 24) (+ .3 .12 .125))
(define-fun .129 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.245000004768371582031)))
(define-fun .130 () (_ FP 8 24) (* .3 .18 .129))
(define-fun .131 () (_ FP 8 24) (+ .3 .126 .130))
(define-fun .134 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.580999970436096191406)))
(define-fun .135 () (_ FP 8 24) (* .3 .22 .134))
(define-fun .136 () (_ FP 8 24) (+ .3 .131 .135))
(define-fun .139 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.750999987125396728516)))
(define-fun .140 () (_ FP 8 24) (* .3 .26 .139))
(define-fun .141 () (_ FP 8 24) (+ .3 .136 .140))
(define-fun .144 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.735000014305114746094)))
(define-fun .145 () (_ FP 8 24) (* .3 .30 .144))
(define-fun .146 () (_ FP 8 24) (+ .3 .141 .145))
(define-fun .147 () Bool (<= .121 .146))
(assert .147)
(define-fun .149 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.293000012636184692383))
(define-fun .152 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.739000022411346435547)))
(define-fun .153 () (_ FP 8 24) (* .3 .14 .152))
(define-fun .154 () (_ FP 8 24) (+ .3 .12 .153))
(define-fun .156 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.375))
(define-fun .157 () (_ FP 8 24) (* .3 .18 .156))
(define-fun .158 () (_ FP 8 24) (+ .3 .154 .157))
(define-fun .160 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.391999989748001098633))
(define-fun .161 () (_ FP 8 24) (* .3 .22 .160))
(define-fun .162 () (_ FP 8 24) (+ .3 .158 .161))
(define-fun .165 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.639999985694885253906)))
(define-fun .166 () (_ FP 8 24) (* .3 .26 .165))
(define-fun .167 () (_ FP 8 24) (+ .3 .162 .166))
(define-fun .170 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0390000008046627044678)))
(define-fun .171 () (_ FP 8 24) (* .3 .30 .170))
(define-fun .172 () (_ FP 8 24) (+ .3 .167 .171))
(define-fun .173 () Bool (<= .172 .149))
(assert .173)
(define-fun .175 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.582000017166137695313))
(define-fun .178 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.275999993085861206055)))
(define-fun .179 () (_ FP 8 24) (* .3 .14 .178))
(define-fun .180 () (_ FP 8 24) (+ .3 .12 .179))
(define-fun .182 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.172999992966651916504))
(define-fun .183 () (_ FP 8 24) (* .3 .18 .182))
(define-fun .184 () (_ FP 8 24) (+ .3 .180 .183))
(define-fun .186 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.808000028133392333984))
(define-fun .187 () (_ FP 8 24) (* .3 .22 .186))
(define-fun .188 () (_ FP 8 24) (+ .3 .184 .187))
(define-fun .190 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.305999994277954101563))
(define-fun .191 () (_ FP 8 24) (* .3 .26 .190))
(define-fun .192 () (_ FP 8 24) (+ .3 .188 .191))
(define-fun .195 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.998000025749206542969)))
(define-fun .196 () (_ FP 8 24) (* .3 .30 .195))
(define-fun .197 () (_ FP 8 24) (+ .3 .192 .196))
(define-fun .198 () Bool (<= .175 .197))
(assert .198)
(define-fun .201 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.768999993801116943359)))
(define-fun .203 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.563000023365020751953))
(define-fun .204 () (_ FP 8 24) (* .3 .14 .203))
(define-fun .205 () (_ FP 8 24) (+ .3 .12 .204))
(define-fun .207 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.686999976634979248047))
(define-fun .208 () (_ FP 8 24) (* .3 .18 .207))
(define-fun .209 () (_ FP 8 24) (+ .3 .205 .208))
(define-fun .212 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.908999979496002197266)))
(define-fun .213 () (_ FP 8 24) (* .3 .22 .212))
(define-fun .214 () (_ FP 8 24) (+ .3 .209 .213))
(define-fun .216 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.21099999547004699707))
(define-fun .217 () (_ FP 8 24) (* .3 .26 .216))
(define-fun .218 () (_ FP 8 24) (+ .3 .214 .217))
(define-fun .220 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.805999994277954101563))
(define-fun .221 () (_ FP 8 24) (* .3 .30 .220))
(define-fun .222 () (_ FP 8 24) (+ .3 .218 .221))
(define-fun .223 () Bool (<= .222 .201))
(assert .223)
(define-fun .226 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.767000019550323486328)))
(define-fun .229 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.669000029563903808594)))
(define-fun .230 () (_ FP 8 24) (* .3 .14 .229))
(define-fun .231 () (_ FP 8 24) (+ .3 .12 .230))
(define-fun .233 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.862999975681304931641))
(define-fun .234 () (_ FP 8 24) (* .3 .18 .233))
(define-fun .235 () (_ FP 8 24) (+ .3 .231 .234))
(define-fun .236 () (_ FP 8 24) (* .3 .22 .144))
(define-fun .237 () (_ FP 8 24) (+ .3 .235 .236))
(define-fun .239 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.163000002503395080566))
(define-fun .240 () (_ FP 8 24) (* .3 .26 .239))
(define-fun .241 () (_ FP 8 24) (+ .3 .237 .240))
(define-fun .244 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0230000000447034835815)))
(define-fun .245 () (_ FP 8 24) (* .3 .30 .244))
(define-fun .246 () (_ FP 8 24) (+ .3 .241 .245))
(define-fun .247 () Bool (<= .226 .246))
(assert .247)
(define-fun .250 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.555999994277954101563)))
(define-fun .252 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.402999997138977050781))
(define-fun .253 () (_ FP 8 24) (* .3 .14 .252))
(define-fun .254 () (_ FP 8 24) (+ .3 .12 .253))
(define-fun .257 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.177000001072883605957)))
(define-fun .258 () (_ FP 8 24) (* .3 .18 .257))
(define-fun .259 () (_ FP 8 24) (+ .3 .254 .258))
(define-fun .262 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.370999991893768310547)))
(define-fun .263 () (_ FP 8 24) (* .3 .22 .262))
(define-fun .264 () (_ FP 8 24) (+ .3 .259 .263))
(define-fun .266 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.257999986410140991211))
(define-fun .267 () (_ FP 8 24) (* .3 .26 .266))
(define-fun .268 () (_ FP 8 24) (+ .3 .264 .267))
(define-fun .271 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.712999999523162841797)))
(define-fun .272 () (_ FP 8 24) (* .3 .30 .271))
(define-fun .273 () (_ FP 8 24) (+ .3 .268 .272))
(define-fun .274 () Bool (<= .273 .250))
(assert .274)
(define-fun .277 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.962999999523162841797)))
(define-fun .279 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.676999986171722412109))
(define-fun .280 () (_ FP 8 24) (* .3 .14 .279))
(define-fun .281 () (_ FP 8 24) (+ .3 .12 .280))
(define-fun .283 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.755999982357025146484))
(define-fun .284 () (_ FP 8 24) (* .3 .18 .283))
(define-fun .285 () (_ FP 8 24) (+ .3 .281 .284))
(define-fun .288 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.801999986171722412109)))
(define-fun .289 () (_ FP 8 24) (* .3 .22 .288))
(define-fun .290 () (_ FP 8 24) (+ .3 .285 .289))
(define-fun .293 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0579999983310699462891)))
(define-fun .294 () (_ FP 8 24) (* .3 .26 .293))
(define-fun .295 () (_ FP 8 24) (+ .3 .290 .294))
(define-fun .298 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.523999989032745361328)))
(define-fun .299 () (_ FP 8 24) (* .3 .30 .298))
(define-fun .300 () (_ FP 8 24) (+ .3 .295 .299))
(define-fun .301 () Bool (<= .277 .300))
(assert .301)
(check-sat)
