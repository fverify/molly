(set-logic QF_FPABV)
(declare-fun b64 () (_ FP 8 24))
(declare-fun b85 () (_ FP 8 24))
(declare-fun b49 () (_ FP 8 24))
(declare-fun b172 () (_ FP 8 24))
(declare-fun b91 () (_ FP 8 24))
(declare-fun b34 () (_ FP 8 24))
(declare-fun b16 () (_ FP 8 24))
(declare-fun b40 () (_ FP 8 24))
(declare-fun b28 () (_ FP 8 24))
(declare-fun b76 () (_ FP 8 24))
(declare-fun b25 () (_ FP 8 24))
(declare-fun b37 () (_ FP 8 24))
(declare-fun b43 () (_ FP 8 24))
(declare-fun b70 () (_ FP 8 24))
(declare-fun b61 () (_ FP 8 24))
(declare-fun b79 () (_ FP 8 24))
(declare-fun b11 () (_ FP 8 24))
(declare-fun b94 () (_ FP 8 24))
(declare-fun b169 () (_ FP 8 24))
(declare-fun b22 () (_ FP 8 24))
(declare-fun b88 () (_ FP 8 24))
(declare-fun b82 () (_ FP 8 24))
(declare-fun b55 () (_ FP 8 24))
(declare-fun b46 () (_ FP 8 24))
(declare-fun b97 () (_ FP 8 24))
(declare-fun b13 () (_ FP 8 24))
(declare-fun b31 () (_ FP 8 24))
(declare-fun b101 () (_ FP 11 53))
(declare-fun b73 () (_ FP 8 24))
(declare-fun b58 () (_ FP 8 24))
(declare-fun b67 () (_ FP 8 24))
(declare-fun b52 () (_ FP 8 24))
(declare-fun b19 () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) b169)
(define-fun .10 () (_ FP 8 24) b11)
(define-fun .11 () Bool (< .9 .10))
(define-fun .12 () (_ FP 8 24) b13)
(define-fun .13 () (_ FP 8 24) (* .3 .10 .12))
(define-fun .14 () (_ FP 8 24) b16)
(define-fun .15 () (_ FP 8 24) (* .3 .13 .14))
(define-fun .16 () (_ FP 8 24) b19)
(define-fun .17 () (_ FP 8 24) (* .3 .15 .16))
(define-fun .18 () (_ FP 8 24) b22)
(define-fun .19 () (_ FP 8 24) (* .3 .17 .18))
(define-fun .20 () (_ FP 8 24) b25)
(define-fun .21 () (_ FP 8 24) (* .3 .19 .20))
(define-fun .22 () (_ FP 8 24) b28)
(define-fun .23 () (_ FP 8 24) (* .3 .21 .22))
(define-fun .24 () (_ FP 8 24) b31)
(define-fun .25 () (_ FP 8 24) (* .3 .23 .24))
(define-fun .26 () (_ FP 8 24) b34)
(define-fun .27 () (_ FP 8 24) (* .3 .25 .26))
(define-fun .28 () (_ FP 8 24) b37)
(define-fun .29 () (_ FP 8 24) (* .3 .27 .28))
(define-fun .30 () (_ FP 8 24) b40)
(define-fun .31 () (_ FP 8 24) (* .3 .29 .30))
(define-fun .32 () (_ FP 8 24) b43)
(define-fun .33 () (_ FP 8 24) (* .3 .31 .32))
(define-fun .34 () (_ FP 8 24) b46)
(define-fun .35 () (_ FP 8 24) (* .3 .33 .34))
(define-fun .36 () (_ FP 8 24) b49)
(define-fun .37 () (_ FP 8 24) (* .3 .35 .36))
(define-fun .38 () (_ FP 8 24) b52)
(define-fun .39 () (_ FP 8 24) (* .3 .37 .38))
(define-fun .40 () (_ FP 8 24) b55)
(define-fun .41 () (_ FP 8 24) (* .3 .39 .40))
(define-fun .42 () (_ FP 8 24) b58)
(define-fun .43 () (_ FP 8 24) (* .3 .41 .42))
(define-fun .44 () (_ FP 8 24) b61)
(define-fun .45 () (_ FP 8 24) (* .3 .43 .44))
(define-fun .46 () (_ FP 8 24) b64)
(define-fun .47 () (_ FP 8 24) (* .3 .45 .46))
(define-fun .48 () (_ FP 8 24) b67)
(define-fun .49 () (_ FP 8 24) (* .3 .47 .48))
(define-fun .50 () (_ FP 8 24) b70)
(define-fun .51 () (_ FP 8 24) (* .3 .49 .50))
(define-fun .52 () (_ FP 8 24) b73)
(define-fun .53 () (_ FP 8 24) (* .3 .51 .52))
(define-fun .54 () (_ FP 8 24) b76)
(define-fun .55 () (_ FP 8 24) (* .3 .53 .54))
(define-fun .56 () (_ FP 8 24) b79)
(define-fun .57 () (_ FP 8 24) (* .3 .55 .56))
(define-fun .58 () (_ FP 8 24) b82)
(define-fun .59 () (_ FP 8 24) (* .3 .57 .58))
(define-fun .60 () (_ FP 8 24) b85)
(define-fun .61 () (_ FP 8 24) (* .3 .59 .60))
(define-fun .62 () (_ FP 8 24) b88)
(define-fun .63 () (_ FP 8 24) (* .3 .61 .62))
(define-fun .64 () (_ FP 8 24) b91)
(define-fun .65 () (_ FP 8 24) (* .3 .63 .64))
(define-fun .66 () (_ FP 8 24) b94)
(define-fun .67 () (_ FP 8 24) (* .3 .65 .66))
(define-fun .68 () (_ FP 8 24) b97)
(define-fun .69 () (_ FP 8 24) (* .3 .67 .68))
(define-fun .70 () (_ FP 11 53) ((_ asFloat 11 53) .3 .69))
(define-fun .71 () (_ FP 11 53) b101)
(define-fun .72 () Bool (< .71 .70))
(define-fun .73 () Bool (and .11 .72))
(define-fun .74 () (_ FP 8 24) b172)
(define-fun .75 () Bool (< .10 .74))
(define-fun .76 () Bool (and .73 .75))
(define-fun .77 () Bool (< .9 .12))
(define-fun .78 () Bool (and .76 .77))
(define-fun .79 () Bool (< .12 .74))
(define-fun .80 () Bool (and .78 .79))
(define-fun .81 () Bool (< .9 .14))
(define-fun .82 () Bool (and .80 .81))
(define-fun .83 () Bool (< .14 .74))
(define-fun .84 () Bool (and .82 .83))
(define-fun .85 () Bool (< .9 .16))
(define-fun .86 () Bool (and .84 .85))
(define-fun .87 () Bool (< .16 .74))
(define-fun .88 () Bool (and .86 .87))
(define-fun .89 () Bool (< .9 .18))
(define-fun .90 () Bool (and .88 .89))
(define-fun .91 () Bool (< .18 .74))
(define-fun .92 () Bool (and .90 .91))
(define-fun .93 () Bool (< .9 .20))
(define-fun .94 () Bool (and .92 .93))
(define-fun .95 () Bool (< .20 .74))
(define-fun .96 () Bool (and .94 .95))
(define-fun .97 () Bool (< .9 .22))
(define-fun .98 () Bool (and .96 .97))
(define-fun .99 () Bool (< .22 .74))
(define-fun .100 () Bool (and .98 .99))
(define-fun .101 () Bool (< .9 .24))
(define-fun .102 () Bool (and .100 .101))
(define-fun .103 () Bool (< .24 .74))
(define-fun .104 () Bool (and .102 .103))
(define-fun .105 () Bool (< .9 .26))
(define-fun .106 () Bool (and .104 .105))
(define-fun .107 () Bool (< .26 .74))
(define-fun .108 () Bool (and .106 .107))
(define-fun .109 () Bool (< .9 .28))
(define-fun .110 () Bool (and .108 .109))
(define-fun .111 () Bool (< .28 .74))
(define-fun .112 () Bool (and .110 .111))
(define-fun .113 () Bool (< .9 .30))
(define-fun .114 () Bool (and .112 .113))
(define-fun .115 () Bool (< .30 .74))
(define-fun .116 () Bool (and .114 .115))
(define-fun .117 () Bool (< .9 .32))
(define-fun .118 () Bool (and .116 .117))
(define-fun .119 () Bool (< .32 .74))
(define-fun .120 () Bool (and .118 .119))
(define-fun .121 () Bool (< .9 .34))
(define-fun .122 () Bool (and .120 .121))
(define-fun .123 () Bool (< .34 .74))
(define-fun .124 () Bool (and .122 .123))
(define-fun .125 () Bool (< .9 .36))
(define-fun .126 () Bool (and .124 .125))
(define-fun .127 () Bool (< .36 .74))
(define-fun .128 () Bool (and .126 .127))
(define-fun .129 () Bool (< .9 .38))
(define-fun .130 () Bool (and .128 .129))
(define-fun .131 () Bool (< .38 .74))
(define-fun .132 () Bool (and .130 .131))
(define-fun .133 () Bool (< .9 .40))
(define-fun .134 () Bool (and .132 .133))
(define-fun .135 () Bool (< .40 .74))
(define-fun .136 () Bool (and .134 .135))
(define-fun .137 () Bool (< .9 .42))
(define-fun .138 () Bool (and .136 .137))
(define-fun .139 () Bool (< .42 .74))
(define-fun .140 () Bool (and .138 .139))
(define-fun .141 () Bool (< .9 .44))
(define-fun .142 () Bool (and .140 .141))
(define-fun .143 () Bool (< .44 .74))
(define-fun .144 () Bool (and .142 .143))
(define-fun .145 () Bool (< .9 .46))
(define-fun .146 () Bool (and .144 .145))
(define-fun .147 () Bool (< .46 .74))
(define-fun .148 () Bool (and .146 .147))
(define-fun .149 () Bool (< .9 .48))
(define-fun .150 () Bool (and .148 .149))
(define-fun .151 () Bool (< .48 .74))
(define-fun .152 () Bool (and .150 .151))
(define-fun .153 () Bool (< .9 .50))
(define-fun .154 () Bool (and .152 .153))
(define-fun .155 () Bool (< .50 .74))
(define-fun .156 () Bool (and .154 .155))
(define-fun .157 () Bool (< .9 .52))
(define-fun .158 () Bool (and .156 .157))
(define-fun .159 () Bool (< .52 .74))
(define-fun .160 () Bool (and .158 .159))
(define-fun .161 () Bool (< .9 .54))
(define-fun .162 () Bool (and .160 .161))
(define-fun .163 () Bool (< .54 .74))
(define-fun .164 () Bool (and .162 .163))
(define-fun .165 () Bool (< .9 .56))
(define-fun .166 () Bool (and .164 .165))
(define-fun .167 () Bool (< .56 .74))
(define-fun .168 () Bool (and .166 .167))
(define-fun .169 () Bool (< .9 .58))
(define-fun .170 () Bool (and .168 .169))
(define-fun .171 () Bool (< .58 .74))
(define-fun .172 () Bool (and .170 .171))
(define-fun .173 () Bool (< .9 .60))
(define-fun .174 () Bool (and .172 .173))
(define-fun .175 () Bool (< .60 .74))
(define-fun .176 () Bool (and .174 .175))
(define-fun .177 () Bool (< .9 .62))
(define-fun .178 () Bool (and .176 .177))
(define-fun .179 () Bool (< .62 .74))
(define-fun .180 () Bool (and .178 .179))
(define-fun .181 () Bool (< .9 .64))
(define-fun .182 () Bool (and .180 .181))
(define-fun .183 () Bool (< .64 .74))
(define-fun .184 () Bool (and .182 .183))
(define-fun .185 () Bool (< .9 .66))
(define-fun .186 () Bool (and .184 .185))
(define-fun .187 () Bool (< .66 .74))
(define-fun .188 () Bool (and .186 .187))
(define-fun .189 () Bool (< .9 .68))
(define-fun .190 () Bool (and .188 .189))
(define-fun .191 () Bool (< .68 .74))
(define-fun .192 () Bool (and .190 .191))
(assert .192)
(check-sat)
