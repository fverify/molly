(set-logic QF_FPABV)
(declare-fun b137 () (_ FP 11 53))
(declare-fun b333 () (_ FP 8 24))
(declare-fun b338 () (_ FP 8 24))
(declare-fun b95 () (_ FP 11 53))
(declare-fun b63 () (_ FP 8 24))
(declare-fun b104 () (_ FP 11 53))
(declare-fun b367 () (_ FP 8 24))
(declare-fun b72 () (_ FP 8 24))
(declare-fun b120 () (_ FP 11 53))
(declare-fun b219 () (_ FP 8 24))
(declare-fun b321 () (_ FP 8 24))
(declare-fun b357 () (_ FP 8 24))
(declare-fun b222 () (_ FP 8 24))
(declare-fun b323 () (_ FP 8 24))
(declare-fun b328 () (_ FP 8 24))
(declare-fun b82 () (_ FP 11 53))
(declare-fun b347 () (_ FP 8 24))
(declare-fun b154 () (_ FP 11 53))
(declare-fun b362 () (_ FP 8 24))
(declare-fun b316 () (_ FP 8 24))
(declare-fun b65 () (_ FP 8 24))
(declare-fun b352 () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) b63)
(define-fun .10 () (_ FP 8 24) (* .3 .9 .9))
(define-fun .11 () (_ FP 8 24) (- .10))
(define-fun .12 () (_ FP 8 24) (* .3 .9 .11))
(define-fun .13 () (_ FP 11 53) ((_ asFloat 11 53) .3 .12))
(define-fun .14 () (_ FP 11 53) b82)
(define-fun .15 () (_ FP 11 53) (/ .3 .13 .14))
(define-fun .16 () (_ FP 8 24) ((_ asFloat 8 24) .3 .15))
(define-fun .17 () (_ FP 8 24) b367)
(define-fun .18 () Bool (= .16 .17))
(define-fun .19 () Bool (not .18))
(define-fun .20 () (_ FP 8 24) (* .3 .11 .16))
(define-fun .21 () (_ FP 11 53) ((_ asFloat 11 53) .3 .20))
(define-fun .22 () (_ FP 11 53) b104)
(define-fun .23 () (_ FP 11 53) (/ .3 .21 .22))
(define-fun .24 () (_ FP 8 24) ((_ asFloat 8 24) .3 .23))
(define-fun .25 () (_ FP 8 24) b362)
(define-fun .26 () Bool (= .24 .25))
(define-fun .27 () Bool (not .26))
(define-fun .28 () (_ FP 8 24) (* .3 .11 .24))
(define-fun .29 () (_ FP 11 53) ((_ asFloat 11 53) .3 .28))
(define-fun .30 () (_ FP 11 53) b120)
(define-fun .31 () (_ FP 11 53) (/ .3 .29 .30))
(define-fun .32 () (_ FP 8 24) ((_ asFloat 8 24) .3 .31))
(define-fun .33 () (_ FP 8 24) b357)
(define-fun .34 () Bool (= .32 .33))
(define-fun .35 () Bool (not .34))
(define-fun .36 () (_ FP 8 24) (* .3 .11 .32))
(define-fun .37 () (_ FP 11 53) ((_ asFloat 11 53) .3 .36))
(define-fun .38 () (_ FP 11 53) b137)
(define-fun .39 () (_ FP 11 53) (/ .3 .37 .38))
(define-fun .40 () (_ FP 8 24) ((_ asFloat 8 24) .3 .39))
(define-fun .41 () (_ FP 8 24) b352)
(define-fun .42 () Bool (= .40 .41))
(define-fun .43 () Bool (not .42))
(define-fun .44 () (_ FP 8 24) (* .3 .11 .40))
(define-fun .45 () (_ FP 11 53) ((_ asFloat 11 53) .3 .44))
(define-fun .46 () (_ FP 11 53) b154)
(define-fun .47 () (_ FP 11 53) (/ .3 .45 .46))
(define-fun .48 () (_ FP 8 24) ((_ asFloat 8 24) .3 .47))
(define-fun .49 () (_ FP 8 24) b347)
(define-fun .50 () Bool (= .48 .49))
(define-fun .51 () Bool (not .50))
(define-fun .52 () (_ FP 8 24) b321)
(define-fun .53 () (_ FP 8 24) b338)
(define-fun .54 () Bool (= .52 .53))
(define-fun .55 () Bool (not .54))
(define-fun .56 () (_ FP 8 24) b333)
(define-fun .57 () Bool (= .53 .56))
(define-fun .58 () Bool (not .57))
(define-fun .59 () (_ FP 8 24) b328)
(define-fun .60 () Bool (= .56 .59))
(define-fun .61 () Bool (not .60))
(define-fun .62 () (_ FP 8 24) (+ .3 .9 .16))
(define-fun .63 () (_ FP 8 24) (+ .3 .24 .62))
(define-fun .64 () (_ FP 8 24) (+ .3 .32 .63))
(define-fun .65 () (_ FP 8 24) (+ .3 .40 .64))
(define-fun .66 () (_ FP 8 24) (+ .3 .48 .65))
(define-fun .67 () Bool (= .59 .66))
(define-fun .68 () Bool (not .67))
(define-fun .69 () (_ FP 8 24) b323)
(define-fun .70 () Bool (= .52 .69))
(define-fun .71 () Bool (not .70))
(define-fun .72 () (_ FP 8 24) b316)
(define-fun .73 () Bool (= .9 .72))
(define-fun .74 () Bool (not .73))
(define-fun .75 () (_ FP 8 24) b65)
(define-fun .76 () Bool (<= .75 .9))
(define-fun .77 () Bool (not .76))
(define-fun .78 () (_ FP 8 24) (- .9))
(define-fun .79 () Bool (= .72 .78))
(define-fun .80 () Bool (and .77 .79))
(define-fun .81 () Bool (and .74 .80))
(define-fun .82 () Bool (<= .75 .52))
(define-fun .83 () Bool (not .82))
(define-fun .84 () Bool (and .81 .83))
(define-fun .85 () (_ FP 8 24) (- .52))
(define-fun .86 () Bool (= .69 .85))
(define-fun .87 () Bool (and .84 .86))
(define-fun .88 () Bool (and .71 .87))
(define-fun .89 () (_ FP 11 53) ((_ asFloat 11 53) .3 .41))
(define-fun .90 () (_ FP 11 53) b95)
(define-fun .91 () Bool (<= .90 .89))
(define-fun .92 () Bool (not .91))
(define-fun .93 () Bool (and .88 .92))
(define-fun .94 () Bool (= .59 .65))
(define-fun .95 () Bool (and .93 .94))
(define-fun .96 () (_ FP 8 24) b72)
(define-fun .97 () Bool (<= .69 .96))
(define-fun .98 () Bool (not .97))
(define-fun .99 () Bool (and .95 .98))
(define-fun .100 () (_ FP 8 24) b222)
(define-fun .101 () Bool (<= .72 .100))
(define-fun .102 () Bool (and .99 .101))
(define-fun .103 () (_ FP 8 24) b219)
(define-fun .104 () Bool (<= .103 .9))
(define-fun .105 () Bool (and .102 .104))
(define-fun .106 () Bool (<= .9 .100))
(define-fun .107 () Bool (and .105 .106))
(define-fun .108 () Bool (and .68 .107))
(define-fun .109 () (_ FP 11 53) ((_ asFloat 11 53) .3 .33))
(define-fun .110 () Bool (<= .90 .109))
(define-fun .111 () Bool (not .110))
(define-fun .112 () Bool (and .108 .111))
(define-fun .113 () Bool (= .56 .64))
(define-fun .114 () Bool (and .112 .113))
(define-fun .115 () Bool (and .61 .114))
(define-fun .116 () (_ FP 11 53) ((_ asFloat 11 53) .3 .25))
(define-fun .117 () Bool (<= .90 .116))
(define-fun .118 () Bool (not .117))
(define-fun .119 () Bool (and .115 .118))
(define-fun .120 () Bool (= .53 .63))
(define-fun .121 () Bool (and .119 .120))
(define-fun .122 () Bool (and .58 .121))
(define-fun .123 () (_ FP 11 53) ((_ asFloat 11 53) .3 .17))
(define-fun .124 () Bool (<= .90 .123))
(define-fun .125 () Bool (not .124))
(define-fun .126 () Bool (and .122 .125))
(define-fun .127 () Bool (= .52 .62))
(define-fun .128 () Bool (and .126 .127))
(define-fun .129 () Bool (and .55 .128))
(define-fun .130 () Bool (<= .75 .48))
(define-fun .131 () Bool (not .130))
(define-fun .132 () Bool (and .129 .131))
(define-fun .133 () (_ FP 8 24) (- .48))
(define-fun .134 () Bool (= .49 .133))
(define-fun .135 () Bool (and .132 .134))
(define-fun .136 () Bool (and .51 .135))
(define-fun .137 () Bool (<= .75 .40))
(define-fun .138 () Bool (not .137))
(define-fun .139 () Bool (and .136 .138))
(define-fun .140 () (_ FP 8 24) (- .40))
(define-fun .141 () Bool (= .41 .140))
(define-fun .142 () Bool (and .139 .141))
(define-fun .143 () Bool (and .43 .142))
(define-fun .144 () Bool (<= .75 .32))
(define-fun .145 () Bool (not .144))
(define-fun .146 () Bool (and .143 .145))
(define-fun .147 () (_ FP 8 24) (- .32))
(define-fun .148 () Bool (= .33 .147))
(define-fun .149 () Bool (and .146 .148))
(define-fun .150 () Bool (and .35 .149))
(define-fun .151 () Bool (<= .75 .24))
(define-fun .152 () Bool (not .151))
(define-fun .153 () Bool (and .150 .152))
(define-fun .154 () (_ FP 8 24) (- .24))
(define-fun .155 () Bool (= .25 .154))
(define-fun .156 () Bool (and .153 .155))
(define-fun .157 () Bool (and .27 .156))
(define-fun .158 () Bool (<= .75 .16))
(define-fun .159 () Bool (not .158))
(define-fun .160 () Bool (and .157 .159))
(define-fun .161 () (_ FP 8 24) (- .16))
(define-fun .162 () Bool (= .17 .161))
(define-fun .163 () Bool (and .160 .162))
(define-fun .164 () (_ FP 11 53) ((_ asFloat 11 53) .3 .49))
(define-fun .165 () Bool (<= .90 .164))
(define-fun .166 () Bool (not .165))
(define-fun .167 () Bool (and .163 .166))
(define-fun .168 () Bool (and .19 .167))
(assert .168)
(check-sat)
