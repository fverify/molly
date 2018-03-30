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
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.578999996185302734375)))
(define-fun .51 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.587999999523162841797)))
(define-fun .52 () (_ FP 8 24) (* .3 .14 .51))
(define-fun .53 () (_ FP 8 24) (+ .3 .12 .52))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.570999979972839355469)))
(define-fun .57 () (_ FP 8 24) (* .3 .18 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .53 .57))
(define-fun .61 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.781000018119812011719)))
(define-fun .62 () (_ FP 8 24) (* .3 .22 .61))
(define-fun .63 () (_ FP 8 24) (+ .3 .58 .62))
(define-fun .65 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.25))
(define-fun .66 () (_ FP 8 24) (* .3 .26 .65))
(define-fun .67 () (_ FP 8 24) (+ .3 .63 .66))
(define-fun .70 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.830999970436096191406)))
(define-fun .71 () (_ FP 8 24) (* .3 .30 .70))
(define-fun .72 () (_ FP 8 24) (+ .3 .67 .71))
(define-fun .75 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.349000006914138793945)))
(define-fun .76 () (_ FP 8 24) (* .3 .34 .75))
(define-fun .77 () (_ FP 8 24) (+ .3 .72 .76))
(define-fun .79 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.455000013113021850586))
(define-fun .80 () (_ FP 8 24) (* .3 .38 .79))
(define-fun .81 () (_ FP 8 24) (+ .3 .77 .80))
(define-fun .82 () Bool (<= .48 .81))
(assert .82)
(define-fun .84 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.419999986886978149414))
(define-fun .87 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00999999977648258209229)))
(define-fun .88 () (_ FP 8 24) (* .3 .14 .87))
(define-fun .89 () (_ FP 8 24) (+ .3 .12 .88))
(define-fun .92 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.845000028610229492188)))
(define-fun .93 () (_ FP 8 24) (* .3 .18 .92))
(define-fun .94 () (_ FP 8 24) (+ .3 .89 .93))
(define-fun .97 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0649999976158142089844)))
(define-fun .98 () (_ FP 8 24) (* .3 .22 .97))
(define-fun .99 () (_ FP 8 24) (+ .3 .94 .98))
(define-fun .101 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.463999986648559570313))
(define-fun .102 () (_ FP 8 24) (* .3 .26 .101))
(define-fun .103 () (_ FP 8 24) (+ .3 .99 .102))
(define-fun .105 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0450000017881393432617))
(define-fun .106 () (_ FP 8 24) (* .3 .30 .105))
(define-fun .107 () (_ FP 8 24) (+ .3 .103 .106))
(define-fun .110 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.361000001430511474609)))
(define-fun .111 () (_ FP 8 24) (* .3 .34 .110))
(define-fun .112 () (_ FP 8 24) (+ .3 .107 .111))
(define-fun .114 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.307999998331069946289))
(define-fun .115 () (_ FP 8 24) (* .3 .38 .114))
(define-fun .116 () (_ FP 8 24) (+ .3 .112 .115))
(define-fun .117 () Bool (<= .84 .116))
(assert .117)
(define-fun .120 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.660000026226043701172)))
(define-fun .122 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.101000003516674041748))
(define-fun .123 () (_ FP 8 24) (* .3 .14 .122))
(define-fun .124 () (_ FP 8 24) (+ .3 .12 .123))
(define-fun .126 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.435999989509582519531))
(define-fun .127 () (_ FP 8 24) (* .3 .18 .126))
(define-fun .128 () (_ FP 8 24) (+ .3 .124 .127))
(define-fun .130 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.275999993085861206055))
(define-fun .131 () (_ FP 8 24) (* .3 .22 .130))
(define-fun .132 () (_ FP 8 24) (+ .3 .128 .131))
(define-fun .134 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.072999998927116394043))
(define-fun .135 () (_ FP 8 24) (* .3 .26 .134))
(define-fun .136 () (_ FP 8 24) (+ .3 .132 .135))
(define-fun .138 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.326000005006790161133))
(define-fun .139 () (_ FP 8 24) (* .3 .30 .138))
(define-fun .140 () (_ FP 8 24) (+ .3 .136 .139))
(define-fun .143 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.451000005006790161133)))
(define-fun .144 () (_ FP 8 24) (* .3 .34 .143))
(define-fun .145 () (_ FP 8 24) (+ .3 .140 .144))
(define-fun .148 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.698000013828277587891)))
(define-fun .149 () (_ FP 8 24) (* .3 .38 .148))
(define-fun .150 () (_ FP 8 24) (+ .3 .145 .149))
(define-fun .151 () Bool (<= .150 .120))
(assert .151)
(define-fun .154 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.27000001072883605957)))
(define-fun .157 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.828000009059906005859)))
(define-fun .158 () (_ FP 8 24) (* .3 .14 .157))
(define-fun .159 () (_ FP 8 24) (+ .3 .12 .158))
(define-fun .162 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.958000004291534423828)))
(define-fun .163 () (_ FP 8 24) (* .3 .18 .162))
(define-fun .164 () (_ FP 8 24) (+ .3 .159 .163))
(define-fun .167 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.648999989032745361328)))
(define-fun .168 () (_ FP 8 24) (* .3 .22 .167))
(define-fun .169 () (_ FP 8 24) (+ .3 .164 .168))
(define-fun .171 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0309999994933605194092))
(define-fun .172 () (_ FP 8 24) (* .3 .26 .171))
(define-fun .173 () (_ FP 8 24) (+ .3 .169 .172))
(define-fun .176 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.797999978065490722656)))
(define-fun .177 () (_ FP 8 24) (* .3 .30 .176))
(define-fun .178 () (_ FP 8 24) (+ .3 .173 .177))
(define-fun .181 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.118000000715255737305)))
(define-fun .182 () (_ FP 8 24) (* .3 .34 .181))
(define-fun .183 () (_ FP 8 24) (+ .3 .178 .182))
(define-fun .186 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.391999989748001098633)))
(define-fun .187 () (_ FP 8 24) (* .3 .38 .186))
(define-fun .188 () (_ FP 8 24) (+ .3 .183 .187))
(define-fun .189 () Bool (<= .188 .154))
(assert .189)
(define-fun .191 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.838999986648559570313))
(define-fun .193 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.861999988555908203125))
(define-fun .194 () (_ FP 8 24) (* .3 .14 .193))
(define-fun .195 () (_ FP 8 24) (+ .3 .12 .194))
(define-fun .197 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.301999986171722412109))
(define-fun .198 () (_ FP 8 24) (* .3 .18 .197))
(define-fun .199 () (_ FP 8 24) (+ .3 .195 .198))
(define-fun .202 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.314999997615814208984)))
(define-fun .203 () (_ FP 8 24) (* .3 .22 .202))
(define-fun .204 () (_ FP 8 24) (+ .3 .199 .203))
(define-fun .206 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.680999994277954101563))
(define-fun .207 () (_ FP 8 24) (* .3 .26 .206))
(define-fun .208 () (_ FP 8 24) (+ .3 .204 .207))
(define-fun .210 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.564999997615814208984))
(define-fun .211 () (_ FP 8 24) (* .3 .30 .210))
(define-fun .212 () (_ FP 8 24) (+ .3 .208 .211))
(define-fun .215 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.500999987125396728516)))
(define-fun .216 () (_ FP 8 24) (* .3 .34 .215))
(define-fun .217 () (_ FP 8 24) (+ .3 .212 .216))
(define-fun .219 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.120999999344348907471))
(define-fun .220 () (_ FP 8 24) (* .3 .38 .219))
(define-fun .221 () (_ FP 8 24) (+ .3 .217 .220))
(define-fun .222 () Bool (<= .191 .221))
(assert .222)
(define-fun .185 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.391999989748001098633))
(define-fun .225 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.586000025272369384766)))
(define-fun .227 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.00700000021606683731079))
(define-fun .228 () (_ FP 8 24) (* .3 .14 .227))
(define-fun .229 () (_ FP 8 24) (+ .3 .12 .228))
(define-fun .232 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.483000010251998901367)))
(define-fun .233 () (_ FP 8 24) (* .3 .18 .232))
(define-fun .234 () (_ FP 8 24) (+ .3 .229 .233))
(define-fun .237 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.638000011444091796875)))
(define-fun .238 () (_ FP 8 24) (* .3 .22 .237))
(define-fun .239 () (_ FP 8 24) (+ .3 .234 .238))
(define-fun .242 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.21099999547004699707)))
(define-fun .243 () (_ FP 8 24) (* .3 .26 .242))
(define-fun .244 () (_ FP 8 24) (+ .3 .239 .243))
(define-fun .245 () (_ FP 8 24) (* .3 .30 .185))
(define-fun .246 () (_ FP 8 24) (+ .3 .244 .245))
(define-fun .248 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.0719999969005584716797))
(define-fun .249 () (_ FP 8 24) (* .3 .34 .248))
(define-fun .250 () (_ FP 8 24) (+ .3 .246 .249))
(define-fun .253 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.976000010967254638672)))
(define-fun .254 () (_ FP 8 24) (* .3 .38 .253))
(define-fun .255 () (_ FP 8 24) (+ .3 .250 .254))
(define-fun .256 () Bool (<= .225 .255))
(assert .256)
(define-fun .259 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0630000010132789611816)))
(define-fun .262 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.337000012397766113281)))
(define-fun .263 () (_ FP 8 24) (* .3 .14 .262))
(define-fun .264 () (_ FP 8 24) (+ .3 .12 .263))
(define-fun .266 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.330000013113021850586))
(define-fun .267 () (_ FP 8 24) (* .3 .18 .266))
(define-fun .268 () (_ FP 8 24) (+ .3 .264 .267))
(define-fun .270 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.312999993562698364258))
(define-fun .271 () (_ FP 8 24) (* .3 .22 .270))
(define-fun .272 () (_ FP 8 24) (+ .3 .268 .271))
(define-fun .275 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.869000017642974853516)))
(define-fun .276 () (_ FP 8 24) (* .3 .26 .275))
(define-fun .277 () (_ FP 8 24) (+ .3 .272 .276))
(define-fun .279 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.732999980449676513672))
(define-fun .280 () (_ FP 8 24) (* .3 .30 .279))
(define-fun .281 () (_ FP 8 24) (+ .3 .277 .280))
(define-fun .283 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.739000022411346435547))
(define-fun .284 () (_ FP 8 24) (* .3 .34 .283))
(define-fun .285 () (_ FP 8 24) (+ .3 .281 .284))
(define-fun .287 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.804000020027160644531))
(define-fun .288 () (_ FP 8 24) (* .3 .38 .287))
(define-fun .289 () (_ FP 8 24) (+ .3 .285 .288))
(define-fun .290 () Bool (<= .259 .289))
(assert .290)
(check-sat)
