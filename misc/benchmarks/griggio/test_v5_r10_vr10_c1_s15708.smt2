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
(define-fun .40 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.328000009059906005859)))
(define-fun .43 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.386999994516372680664)))
(define-fun .44 () (_ FP 8 24) (* .3 .14 .43))
(define-fun .45 () (_ FP 8 24) (+ .3 .12 .44))
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.101000003516674041748)))
(define-fun .49 () (_ FP 8 24) (* .3 .18 .48))
(define-fun .50 () (_ FP 8 24) (+ .3 .45 .49))
(define-fun .53 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.737999975681304931641)))
(define-fun .54 () (_ FP 8 24) (* .3 .22 .53))
(define-fun .55 () (_ FP 8 24) (+ .3 .50 .54))
(define-fun .57 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.187999993562698364258))
(define-fun .58 () (_ FP 8 24) (* .3 .26 .57))
(define-fun .59 () (_ FP 8 24) (+ .3 .55 .58))
(define-fun .62 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.477999985218048095703)))
(define-fun .63 () (_ FP 8 24) (* .3 .30 .62))
(define-fun .64 () (_ FP 8 24) (+ .3 .59 .63))
(define-fun .65 () Bool (<= .64 .40))
(assert .65)
(define-fun .68 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.14200000464916229248)))
(define-fun .71 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.208000004291534423828)))
(define-fun .72 () (_ FP 8 24) (* .3 .14 .71))
(define-fun .73 () (_ FP 8 24) (+ .3 .12 .72))
(define-fun .75 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.786000013351440429688))
(define-fun .76 () (_ FP 8 24) (* .3 .18 .75))
(define-fun .77 () (_ FP 8 24) (+ .3 .73 .76))
(define-fun .79 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0630000010132789611816))
(define-fun .80 () (_ FP 8 24) (* .3 .22 .79))
(define-fun .81 () (_ FP 8 24) (+ .3 .77 .80))
(define-fun .83 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.652000010013580322266))
(define-fun .84 () (_ FP 8 24) (* .3 .26 .83))
(define-fun .85 () (_ FP 8 24) (+ .3 .81 .84))
(define-fun .88 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.892000019550323486328)))
(define-fun .89 () (_ FP 8 24) (* .3 .30 .88))
(define-fun .90 () (_ FP 8 24) (+ .3 .85 .89))
(define-fun .91 () Bool (<= .68 .90))
(assert .91)
(define-fun .94 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.453999996185302734375)))
(define-fun .97 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.131999999284744262695)))
(define-fun .98 () (_ FP 8 24) (* .3 .14 .97))
(define-fun .99 () (_ FP 8 24) (+ .3 .12 .98))
(define-fun .101 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.790000021457672119141))
(define-fun .102 () (_ FP 8 24) (* .3 .18 .101))
(define-fun .103 () (_ FP 8 24) (+ .3 .99 .102))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.481999993324279785156))
(define-fun .106 () (_ FP 8 24) (* .3 .22 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .103 .106))
(define-fun .110 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.878000020980834960938)))
(define-fun .111 () (_ FP 8 24) (* .3 .26 .110))
(define-fun .112 () (_ FP 8 24) (+ .3 .107 .111))
(define-fun .115 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.119999997317790985107)))
(define-fun .116 () (_ FP 8 24) (* .3 .30 .115))
(define-fun .117 () (_ FP 8 24) (+ .3 .112 .116))
(define-fun .118 () Bool (<= .117 .94))
(assert .118)
(define-fun .120 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.44699999690055847168))
(define-fun .123 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.465000003576278686523)))
(define-fun .124 () (_ FP 8 24) (* .3 .14 .123))
(define-fun .125 () (_ FP 8 24) (+ .3 .12 .124))
(define-fun .127 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 1.0))
(define-fun .128 () (_ FP 8 24) (* .3 .18 .127))
(define-fun .129 () (_ FP 8 24) (+ .3 .125 .128))
(define-fun .131 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0619999989867210388184))
(define-fun .132 () (_ FP 8 24) (* .3 .22 .131))
(define-fun .133 () (_ FP 8 24) (+ .3 .129 .132))
(define-fun .135 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.716000020503997802734))
(define-fun .136 () (_ FP 8 24) (* .3 .26 .135))
(define-fun .137 () (_ FP 8 24) (+ .3 .133 .136))
(define-fun .139 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.536000013351440429688))
(define-fun .140 () (_ FP 8 24) (* .3 .30 .139))
(define-fun .141 () (_ FP 8 24) (+ .3 .137 .140))
(define-fun .142 () Bool (<= .120 .141))
(assert .142)
(define-fun .145 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.301999986171722412109)))
(define-fun .147 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.941999971866607666016))
(define-fun .148 () (_ FP 8 24) (* .3 .14 .147))
(define-fun .149 () (_ FP 8 24) (+ .3 .12 .148))
(define-fun .151 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.12800000607967376709))
(define-fun .152 () (_ FP 8 24) (* .3 .18 .151))
(define-fun .153 () (_ FP 8 24) (+ .3 .149 .152))
(define-fun .156 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.638999998569488525391)))
(define-fun .157 () (_ FP 8 24) (* .3 .22 .156))
(define-fun .158 () (_ FP 8 24) (+ .3 .153 .157))
(define-fun .160 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.680000007152557373047))
(define-fun .161 () (_ FP 8 24) (* .3 .26 .160))
(define-fun .162 () (_ FP 8 24) (+ .3 .158 .161))
(define-fun .164 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00200000009499490261078))
(define-fun .165 () (_ FP 8 24) (* .3 .30 .164))
(define-fun .166 () (_ FP 8 24) (+ .3 .162 .165))
(define-fun .167 () Bool (<= .145 .166))
(assert .167)
(define-fun .170 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.879999995231628417969)))
(define-fun .172 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.606000006198883056641))
(define-fun .173 () (_ FP 8 24) (* .3 .14 .172))
(define-fun .174 () (_ FP 8 24) (+ .3 .12 .173))
(define-fun .177 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.800000011920928955078)))
(define-fun .178 () (_ FP 8 24) (* .3 .18 .177))
(define-fun .179 () (_ FP 8 24) (+ .3 .174 .178))
(define-fun .182 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.679000020027160644531)))
(define-fun .183 () (_ FP 8 24) (* .3 .22 .182))
(define-fun .184 () (_ FP 8 24) (+ .3 .179 .183))
(define-fun .185 () (_ FP 8 24) (* .3 .26 .97))
(define-fun .186 () (_ FP 8 24) (+ .3 .184 .185))
(define-fun .188 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.924000024795532226563))
(define-fun .189 () (_ FP 8 24) (* .3 .30 .188))
(define-fun .190 () (_ FP 8 24) (+ .3 .186 .189))
(define-fun .191 () Bool (<= .170 .190))
(assert .191)
(define-fun .87 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.892000019550323486328))
(define-fun .93 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.453999996185302734375))
(define-fun .193 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.842999994754791259766))
(define-fun .194 () (_ FP 8 24) (* .3 .14 .93))
(define-fun .195 () (_ FP 8 24) (+ .3 .12 .194))
(define-fun .197 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.345999985933303833008))
(define-fun .198 () (_ FP 8 24) (* .3 .18 .197))
(define-fun .199 () (_ FP 8 24) (+ .3 .195 .198))
(define-fun .201 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.537999987602233886719))
(define-fun .202 () (_ FP 8 24) (* .3 .22 .201))
(define-fun .203 () (_ FP 8 24) (+ .3 .199 .202))
(define-fun .204 () (_ FP 8 24) (* .3 .26 .87))
(define-fun .205 () (_ FP 8 24) (+ .3 .203 .204))
(define-fun .208 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.141000002622604370117)))
(define-fun .209 () (_ FP 8 24) (* .3 .30 .208))
(define-fun .210 () (_ FP 8 24) (+ .3 .205 .209))
(define-fun .211 () Bool (<= .210 .193))
(assert .211)
(define-fun .213 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.319999992847442626953))
(define-fun .215 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.649999976158142089844))
(define-fun .216 () (_ FP 8 24) (* .3 .14 .215))
(define-fun .217 () (_ FP 8 24) (+ .3 .12 .216))
(define-fun .220 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00800000037997961044312)))
(define-fun .221 () (_ FP 8 24) (* .3 .18 .220))
(define-fun .222 () (_ FP 8 24) (+ .3 .217 .221))
(define-fun .224 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.866999983787536621094))
(define-fun .225 () (_ FP 8 24) (* .3 .22 .224))
(define-fun .226 () (_ FP 8 24) (+ .3 .222 .225))
(define-fun .228 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.456000000238418579102))
(define-fun .229 () (_ FP 8 24) (* .3 .26 .228))
(define-fun .230 () (_ FP 8 24) (+ .3 .226 .229))
(define-fun .233 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0780000016093254089355)))
(define-fun .234 () (_ FP 8 24) (* .3 .30 .233))
(define-fun .235 () (_ FP 8 24) (+ .3 .230 .234))
(define-fun .236 () Bool (<= .235 .213))
(assert .236)
(define-fun .239 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.222000002861022949219)))
(define-fun .241 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.467999994754791259766))
(define-fun .242 () (_ FP 8 24) (* .3 .14 .241))
(define-fun .243 () (_ FP 8 24) (+ .3 .12 .242))
(define-fun .246 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.759999990463256835938)))
(define-fun .247 () (_ FP 8 24) (* .3 .18 .246))
(define-fun .248 () (_ FP 8 24) (+ .3 .243 .247))
(define-fun .250 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.293000012636184692383))
(define-fun .251 () (_ FP 8 24) (* .3 .22 .250))
(define-fun .252 () (_ FP 8 24) (+ .3 .248 .251))
(define-fun .254 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0769999995827674865723))
(define-fun .255 () (_ FP 8 24) (* .3 .26 .254))
(define-fun .256 () (_ FP 8 24) (+ .3 .252 .255))
(define-fun .258 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.405999988317489624023))
(define-fun .259 () (_ FP 8 24) (* .3 .30 .258))
(define-fun .260 () (_ FP 8 24) (+ .3 .256 .259))
(define-fun .261 () Bool (<= .260 .239))
(assert .261)
(define-fun .263 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.168999999761581420898))
(define-fun .265 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.476000010967254638672))
(define-fun .266 () (_ FP 8 24) (* .3 .14 .265))
(define-fun .267 () (_ FP 8 24) (+ .3 .12 .266))
(define-fun .269 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.819999992847442626953))
(define-fun .270 () (_ FP 8 24) (* .3 .18 .269))
(define-fun .271 () (_ FP 8 24) (+ .3 .267 .270))
(define-fun .273 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.34200000762939453125))
(define-fun .274 () (_ FP 8 24) (* .3 .22 .273))
(define-fun .275 () (_ FP 8 24) (+ .3 .271 .274))
(define-fun .278 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.40799999237060546875)))
(define-fun .279 () (_ FP 8 24) (* .3 .26 .278))
(define-fun .280 () (_ FP 8 24) (+ .3 .275 .279))
(define-fun .282 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.472000002861022949219))
(define-fun .283 () (_ FP 8 24) (* .3 .30 .282))
(define-fun .284 () (_ FP 8 24) (+ .3 .280 .283))
(define-fun .285 () Bool (<= .284 .263))
(assert .285)
(check-sat)
