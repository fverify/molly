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
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0659999996423721313477)))
(define-fun .51 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.308999985456466674805)))
(define-fun .52 () (_ FP 8 24) (* .3 .14 .51))
(define-fun .53 () (_ FP 8 24) (+ .3 .12 .52))
(define-fun .56 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.787999987602233886719)))
(define-fun .57 () (_ FP 8 24) (* .3 .18 .56))
(define-fun .58 () (_ FP 8 24) (+ .3 .53 .57))
(define-fun .61 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.416000008583068847656)))
(define-fun .62 () (_ FP 8 24) (* .3 .22 .61))
(define-fun .63 () (_ FP 8 24) (+ .3 .58 .62))
(define-fun .66 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.435999989509582519531)))
(define-fun .67 () (_ FP 8 24) (* .3 .26 .66))
(define-fun .68 () (_ FP 8 24) (+ .3 .63 .67))
(define-fun .70 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.936999976634979248047))
(define-fun .71 () (_ FP 8 24) (* .3 .30 .70))
(define-fun .72 () (_ FP 8 24) (+ .3 .68 .71))
(define-fun .75 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.140000000596046447754)))
(define-fun .76 () (_ FP 8 24) (* .3 .34 .75))
(define-fun .77 () (_ FP 8 24) (+ .3 .72 .76))
(define-fun .79 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.374000012874603271484))
(define-fun .80 () (_ FP 8 24) (* .3 .38 .79))
(define-fun .81 () (_ FP 8 24) (+ .3 .77 .80))
(define-fun .82 () Bool (<= .48 .81))
(assert .82)
(define-fun .84 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.716000020503997802734))
(define-fun .86 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.143000006675720214844))
(define-fun .87 () (_ FP 8 24) (* .3 .14 .86))
(define-fun .88 () (_ FP 8 24) (+ .3 .12 .87))
(define-fun .90 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.17800000309944152832))
(define-fun .91 () (_ FP 8 24) (* .3 .18 .90))
(define-fun .92 () (_ FP 8 24) (+ .3 .88 .91))
(define-fun .95 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.465000003576278686523)))
(define-fun .96 () (_ FP 8 24) (* .3 .22 .95))
(define-fun .97 () (_ FP 8 24) (+ .3 .92 .96))
(define-fun .99 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.806999981403350830078))
(define-fun .100 () (_ FP 8 24) (* .3 .26 .99))
(define-fun .101 () (_ FP 8 24) (+ .3 .97 .100))
(define-fun .103 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.671999990940093994141))
(define-fun .104 () (_ FP 8 24) (* .3 .30 .103))
(define-fun .105 () (_ FP 8 24) (+ .3 .101 .104))
(define-fun .107 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.127000004053115844727))
(define-fun .108 () (_ FP 8 24) (* .3 .34 .107))
(define-fun .109 () (_ FP 8 24) (+ .3 .105 .108))
(define-fun .112 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.173999994993209838867)))
(define-fun .113 () (_ FP 8 24) (* .3 .38 .112))
(define-fun .114 () (_ FP 8 24) (+ .3 .109 .113))
(define-fun .115 () Bool (<= .114 .84))
(assert .115)
(define-fun .118 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.28299999237060546875)))
(define-fun .121 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.802999973297119140625)))
(define-fun .122 () (_ FP 8 24) (* .3 .14 .121))
(define-fun .123 () (_ FP 8 24) (+ .3 .12 .122))
(define-fun .125 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.814000010490417480469))
(define-fun .126 () (_ FP 8 24) (* .3 .18 .125))
(define-fun .127 () (_ FP 8 24) (+ .3 .123 .126))
(define-fun .130 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.933000028133392333984)))
(define-fun .131 () (_ FP 8 24) (* .3 .22 .130))
(define-fun .132 () (_ FP 8 24) (+ .3 .127 .131))
(define-fun .135 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.456999987363815307617)))
(define-fun .136 () (_ FP 8 24) (* .3 .26 .135))
(define-fun .137 () (_ FP 8 24) (+ .3 .132 .136))
(define-fun .139 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.300999999046325683594))
(define-fun .140 () (_ FP 8 24) (* .3 .30 .139))
(define-fun .141 () (_ FP 8 24) (+ .3 .137 .140))
(define-fun .143 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.203999996185302734375))
(define-fun .144 () (_ FP 8 24) (* .3 .34 .143))
(define-fun .145 () (_ FP 8 24) (+ .3 .141 .144))
(define-fun .147 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.628000020980834960938))
(define-fun .148 () (_ FP 8 24) (* .3 .38 .147))
(define-fun .149 () (_ FP 8 24) (+ .3 .145 .148))
(define-fun .150 () Bool (<= .149 .118))
(assert .150)
(define-fun .153 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.839999973773956298828)))
(define-fun .155 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.924000024795532226563))
(define-fun .156 () (_ FP 8 24) (* .3 .14 .155))
(define-fun .157 () (_ FP 8 24) (+ .3 .12 .156))
(define-fun .160 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.582000017166137695313)))
(define-fun .161 () (_ FP 8 24) (* .3 .18 .160))
(define-fun .162 () (_ FP 8 24) (+ .3 .157 .161))
(define-fun .165 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.642000019550323486328)))
(define-fun .166 () (_ FP 8 24) (* .3 .22 .165))
(define-fun .167 () (_ FP 8 24) (+ .3 .162 .166))
(define-fun .169 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.768999993801116943359))
(define-fun .170 () (_ FP 8 24) (* .3 .26 .169))
(define-fun .171 () (_ FP 8 24) (+ .3 .167 .170))
(define-fun .174 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.310000002384185791016)))
(define-fun .175 () (_ FP 8 24) (* .3 .30 .174))
(define-fun .176 () (_ FP 8 24) (+ .3 .171 .175))
(define-fun .178 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.428999990224838256836))
(define-fun .179 () (_ FP 8 24) (* .3 .34 .178))
(define-fun .180 () (_ FP 8 24) (+ .3 .176 .179))
(define-fun .182 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.833999991416931152344))
(define-fun .183 () (_ FP 8 24) (* .3 .38 .182))
(define-fun .184 () (_ FP 8 24) (+ .3 .180 .183))
(define-fun .185 () Bool (<= .153 .184))
(assert .185)
(define-fun .188 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.816999971866607666016)))
(define-fun .191 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.0430000014603137969971)))
(define-fun .192 () (_ FP 8 24) (* .3 .14 .191))
(define-fun .193 () (_ FP 8 24) (+ .3 .12 .192))
(define-fun .196 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.500999987125396728516)))
(define-fun .197 () (_ FP 8 24) (* .3 .18 .196))
(define-fun .198 () (_ FP 8 24) (+ .3 .193 .197))
(define-fun .201 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.84899997711181640625)))
(define-fun .202 () (_ FP 8 24) (* .3 .22 .201))
(define-fun .203 () (_ FP 8 24) (+ .3 .198 .202))
(define-fun .204 () (_ FP 8 24) (+ .3 .136 .203))
(define-fun .206 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.46099999547004699707))
(define-fun .207 () (_ FP 8 24) (* .3 .30 .206))
(define-fun .208 () (_ FP 8 24) (+ .3 .204 .207))
(define-fun .211 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.00600000005215406417847)))
(define-fun .212 () (_ FP 8 24) (* .3 .34 .211))
(define-fun .213 () (_ FP 8 24) (+ .3 .208 .212))
(define-fun .215 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.358000010251998901367))
(define-fun .216 () (_ FP 8 24) (* .3 .38 .215))
(define-fun .217 () (_ FP 8 24) (+ .3 .213 .216))
(define-fun .218 () Bool (<= .188 .217))
(assert .218)
(define-fun .221 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.550000011920928955078)))
(define-fun .224 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.643999993801116943359)))
(define-fun .225 () (_ FP 8 24) (* .3 .14 .224))
(define-fun .226 () (_ FP 8 24) (+ .3 .12 .225))
(define-fun .227 () (_ FP 8 24) (* .3 .18 .147))
(define-fun .228 () (_ FP 8 24) (+ .3 .226 .227))
(define-fun .229 () (_ FP 8 24) (* .3 .22 .121))
(define-fun .230 () (_ FP 8 24) (+ .3 .228 .229))
(define-fun .233 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.490000009536743164063)))
(define-fun .234 () (_ FP 8 24) (* .3 .26 .233))
(define-fun .235 () (_ FP 8 24) (+ .3 .230 .234))
(define-fun .238 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.393999993801116943359)))
(define-fun .239 () (_ FP 8 24) (* .3 .30 .238))
(define-fun .240 () (_ FP 8 24) (+ .3 .235 .239))
(define-fun .243 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.144999995827674865723)))
(define-fun .244 () (_ FP 8 24) (* .3 .34 .243))
(define-fun .245 () (_ FP 8 24) (+ .3 .240 .244))
(define-fun .248 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.397000014781951904297)))
(define-fun .249 () (_ FP 8 24) (* .3 .38 .248))
(define-fun .250 () (_ FP 8 24) (+ .3 .245 .249))
(define-fun .251 () Bool (<= .221 .250))
(assert .251)
(define-fun .254 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.268999993801116943359)))
(define-fun .257 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.606000006198883056641)))
(define-fun .258 () (_ FP 8 24) (* .3 .14 .257))
(define-fun .259 () (_ FP 8 24) (+ .3 .12 .258))
(define-fun .261 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.712000012397766113281))
(define-fun .262 () (_ FP 8 24) (* .3 .18 .261))
(define-fun .263 () (_ FP 8 24) (+ .3 .259 .262))
(define-fun .266 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.231000006198883056641)))
(define-fun .267 () (_ FP 8 24) (* .3 .22 .266))
(define-fun .268 () (_ FP 8 24) (+ .3 .263 .267))
(define-fun .271 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.439999997615814208984)))
(define-fun .272 () (_ FP 8 24) (* .3 .26 .271))
(define-fun .273 () (_ FP 8 24) (+ .3 .268 .272))
(define-fun .275 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.293999999761581420898))
(define-fun .276 () (_ FP 8 24) (* .3 .30 .275))
(define-fun .277 () (_ FP 8 24) (+ .3 .273 .276))
(define-fun .279 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero 0.78299999237060546875))
(define-fun .280 () (_ FP 8 24) (* .3 .34 .279))
(define-fun .281 () (_ FP 8 24) (+ .3 .277 .280))
(define-fun .284 () (_ FP 8 24) ((_ asFloat 8 24) roundTowardZero (- 0.112999998033046722412)))
(define-fun .285 () (_ FP 8 24) (* .3 .38 .284))
(define-fun .286 () (_ FP 8 24) (+ .3 .281 .285))
(define-fun .287 () Bool (<= .286 .254))
(assert .287)
(check-sat)
