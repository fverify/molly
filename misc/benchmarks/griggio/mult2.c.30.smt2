(set-logic QF_FPABV)
(declare-fun b17 () (_ FP 8 24))
(declare-fun b44 () (_ FP 8 24))
(declare-fun b92 () (_ FP 8 24))
(declare-fun b101 () (_ FP 8 24))
(declare-fun b98 () (_ FP 8 24))
(declare-fun b86 () (_ FP 8 24))
(declare-fun b50 () (_ FP 8 24))
(declare-fun b10 () (_ FP 8 24))
(declare-fun b71 () (_ FP 8 24))
(declare-fun b47 () (_ FP 8 24))
(declare-fun b23 () (_ FP 8 24))
(declare-fun b77 () (_ FP 8 24))
(declare-fun b11 () (_ FP 8 24))
(declare-fun b53 () (_ FP 8 24))
(declare-fun b29 () (_ FP 8 24))
(declare-fun b35 () (_ FP 8 24))
(declare-fun b59 () (_ FP 8 24))
(declare-fun b169 () (_ FP 8 24))
(declare-fun b20 () (_ FP 8 24))
(declare-fun b74 () (_ FP 8 24))
(declare-fun b89 () (_ FP 8 24))
(declare-fun b80 () (_ FP 8 24))
(declare-fun b95 () (_ FP 8 24))
(declare-fun b62 () (_ FP 8 24))
(declare-fun b14 () (_ FP 8 24))
(declare-fun b38 () (_ FP 8 24))
(declare-fun b65 () (_ FP 8 24))
(declare-fun b56 () (_ FP 8 24))
(declare-fun b26 () (_ FP 8 24))
(declare-fun b172 () (_ FP 8 24))
(declare-fun b32 () (_ FP 8 24))
(declare-fun b68 () (_ FP 8 24))
(declare-fun b41 () (_ FP 8 24))
(declare-fun b83 () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) b169)
(define-fun .10 () (_ FP 8 24) b11)
(define-fun .11 () Bool (< .9 .10))
(define-fun .12 () (_ FP 8 24) b10)
(define-fun .13 () (_ FP 8 24) (* .3 .10 .12))
(define-fun .14 () (_ FP 8 24) b14)
(define-fun .15 () (_ FP 8 24) (* .3 .13 .14))
(define-fun .16 () (_ FP 8 24) b17)
(define-fun .17 () (_ FP 8 24) (* .3 .15 .16))
(define-fun .18 () (_ FP 8 24) b20)
(define-fun .19 () (_ FP 8 24) (* .3 .17 .18))
(define-fun .20 () (_ FP 8 24) b23)
(define-fun .21 () (_ FP 8 24) (* .3 .19 .20))
(define-fun .22 () (_ FP 8 24) b26)
(define-fun .23 () (_ FP 8 24) (* .3 .21 .22))
(define-fun .24 () (_ FP 8 24) b29)
(define-fun .25 () (_ FP 8 24) (* .3 .23 .24))
(define-fun .26 () (_ FP 8 24) b32)
(define-fun .27 () (_ FP 8 24) (* .3 .25 .26))
(define-fun .28 () (_ FP 8 24) b35)
(define-fun .29 () (_ FP 8 24) (* .3 .27 .28))
(define-fun .30 () (_ FP 8 24) b38)
(define-fun .31 () (_ FP 8 24) (* .3 .29 .30))
(define-fun .32 () (_ FP 8 24) b41)
(define-fun .33 () (_ FP 8 24) (* .3 .31 .32))
(define-fun .34 () (_ FP 8 24) b44)
(define-fun .35 () (_ FP 8 24) (* .3 .33 .34))
(define-fun .36 () (_ FP 8 24) b47)
(define-fun .37 () (_ FP 8 24) (* .3 .35 .36))
(define-fun .38 () (_ FP 8 24) b50)
(define-fun .39 () (_ FP 8 24) (* .3 .37 .38))
(define-fun .40 () (_ FP 8 24) b53)
(define-fun .41 () (_ FP 8 24) (* .3 .39 .40))
(define-fun .42 () (_ FP 8 24) b56)
(define-fun .43 () (_ FP 8 24) (* .3 .41 .42))
(define-fun .44 () (_ FP 8 24) b59)
(define-fun .45 () (_ FP 8 24) (* .3 .43 .44))
(define-fun .46 () (_ FP 8 24) b62)
(define-fun .47 () (_ FP 8 24) (* .3 .45 .46))
(define-fun .48 () (_ FP 8 24) b65)
(define-fun .49 () (_ FP 8 24) (* .3 .47 .48))
(define-fun .50 () (_ FP 8 24) b68)
(define-fun .51 () (_ FP 8 24) (* .3 .49 .50))
(define-fun .52 () (_ FP 8 24) b71)
(define-fun .53 () (_ FP 8 24) (* .3 .51 .52))
(define-fun .54 () (_ FP 8 24) b74)
(define-fun .55 () (_ FP 8 24) (* .3 .53 .54))
(define-fun .56 () (_ FP 8 24) b77)
(define-fun .57 () (_ FP 8 24) (* .3 .55 .56))
(define-fun .58 () (_ FP 8 24) b80)
(define-fun .59 () (_ FP 8 24) (* .3 .57 .58))
(define-fun .60 () (_ FP 8 24) b83)
(define-fun .61 () (_ FP 8 24) (* .3 .59 .60))
(define-fun .62 () (_ FP 8 24) b86)
(define-fun .63 () (_ FP 8 24) (* .3 .61 .62))
(define-fun .64 () (_ FP 8 24) b89)
(define-fun .65 () (_ FP 8 24) (* .3 .63 .64))
(define-fun .66 () (_ FP 8 24) b92)
(define-fun .67 () (_ FP 8 24) (* .3 .65 .66))
(define-fun .68 () (_ FP 8 24) b95)
(define-fun .69 () (_ FP 8 24) (* .3 .67 .68))
(define-fun .70 () (_ FP 8 24) b98)
(define-fun .71 () (_ FP 8 24) (* .3 .69 .70))
(define-fun .72 () (_ FP 8 24) b101)
(define-fun .73 () Bool (< .71 .72))
(define-fun .74 () Bool (and .11 .73))
(define-fun .75 () (_ FP 8 24) b172)
(define-fun .76 () Bool (< .10 .75))
(define-fun .77 () Bool (and .74 .76))
(define-fun .78 () Bool (< .9 .14))
(define-fun .79 () Bool (and .77 .78))
(define-fun .80 () Bool (< .14 .75))
(define-fun .81 () Bool (and .79 .80))
(define-fun .82 () Bool (< .9 .16))
(define-fun .83 () Bool (and .81 .82))
(define-fun .84 () Bool (< .16 .75))
(define-fun .85 () Bool (and .83 .84))
(define-fun .86 () Bool (< .9 .18))
(define-fun .87 () Bool (and .85 .86))
(define-fun .88 () Bool (< .18 .75))
(define-fun .89 () Bool (and .87 .88))
(define-fun .90 () Bool (< .9 .20))
(define-fun .91 () Bool (and .89 .90))
(define-fun .92 () Bool (< .20 .75))
(define-fun .93 () Bool (and .91 .92))
(define-fun .94 () Bool (< .9 .22))
(define-fun .95 () Bool (and .93 .94))
(define-fun .96 () Bool (< .22 .75))
(define-fun .97 () Bool (and .95 .96))
(define-fun .98 () Bool (< .9 .24))
(define-fun .99 () Bool (and .97 .98))
(define-fun .100 () Bool (< .24 .75))
(define-fun .101 () Bool (and .99 .100))
(define-fun .102 () Bool (< .9 .26))
(define-fun .103 () Bool (and .101 .102))
(define-fun .104 () Bool (< .26 .75))
(define-fun .105 () Bool (and .103 .104))
(define-fun .106 () Bool (< .9 .28))
(define-fun .107 () Bool (and .105 .106))
(define-fun .108 () Bool (< .28 .75))
(define-fun .109 () Bool (and .107 .108))
(define-fun .110 () Bool (< .9 .30))
(define-fun .111 () Bool (and .109 .110))
(define-fun .112 () Bool (< .30 .75))
(define-fun .113 () Bool (and .111 .112))
(define-fun .114 () Bool (< .9 .32))
(define-fun .115 () Bool (and .113 .114))
(define-fun .116 () Bool (< .32 .75))
(define-fun .117 () Bool (and .115 .116))
(define-fun .118 () Bool (< .9 .34))
(define-fun .119 () Bool (and .117 .118))
(define-fun .120 () Bool (< .34 .75))
(define-fun .121 () Bool (and .119 .120))
(define-fun .122 () Bool (< .9 .36))
(define-fun .123 () Bool (and .121 .122))
(define-fun .124 () Bool (< .36 .75))
(define-fun .125 () Bool (and .123 .124))
(define-fun .126 () Bool (< .9 .38))
(define-fun .127 () Bool (and .125 .126))
(define-fun .128 () Bool (< .38 .75))
(define-fun .129 () Bool (and .127 .128))
(define-fun .130 () Bool (< .9 .40))
(define-fun .131 () Bool (and .129 .130))
(define-fun .132 () Bool (< .40 .75))
(define-fun .133 () Bool (and .131 .132))
(define-fun .134 () Bool (< .9 .42))
(define-fun .135 () Bool (and .133 .134))
(define-fun .136 () Bool (< .42 .75))
(define-fun .137 () Bool (and .135 .136))
(define-fun .138 () Bool (< .9 .44))
(define-fun .139 () Bool (and .137 .138))
(define-fun .140 () Bool (< .44 .75))
(define-fun .141 () Bool (and .139 .140))
(define-fun .142 () Bool (< .9 .46))
(define-fun .143 () Bool (and .141 .142))
(define-fun .144 () Bool (< .46 .75))
(define-fun .145 () Bool (and .143 .144))
(define-fun .146 () Bool (< .9 .48))
(define-fun .147 () Bool (and .145 .146))
(define-fun .148 () Bool (< .48 .75))
(define-fun .149 () Bool (and .147 .148))
(define-fun .150 () Bool (< .9 .50))
(define-fun .151 () Bool (and .149 .150))
(define-fun .152 () Bool (< .50 .75))
(define-fun .153 () Bool (and .151 .152))
(define-fun .154 () Bool (< .9 .52))
(define-fun .155 () Bool (and .153 .154))
(define-fun .156 () Bool (< .52 .75))
(define-fun .157 () Bool (and .155 .156))
(define-fun .158 () Bool (< .9 .54))
(define-fun .159 () Bool (and .157 .158))
(define-fun .160 () Bool (< .54 .75))
(define-fun .161 () Bool (and .159 .160))
(define-fun .162 () Bool (< .9 .56))
(define-fun .163 () Bool (and .161 .162))
(define-fun .164 () Bool (< .56 .75))
(define-fun .165 () Bool (and .163 .164))
(define-fun .166 () Bool (< .9 .58))
(define-fun .167 () Bool (and .165 .166))
(define-fun .168 () Bool (< .58 .75))
(define-fun .169 () Bool (and .167 .168))
(define-fun .170 () Bool (< .9 .60))
(define-fun .171 () Bool (and .169 .170))
(define-fun .172 () Bool (< .60 .75))
(define-fun .173 () Bool (and .171 .172))
(define-fun .174 () Bool (< .9 .62))
(define-fun .175 () Bool (and .173 .174))
(define-fun .176 () Bool (< .62 .75))
(define-fun .177 () Bool (and .175 .176))
(define-fun .178 () Bool (< .9 .64))
(define-fun .179 () Bool (and .177 .178))
(define-fun .180 () Bool (< .64 .75))
(define-fun .181 () Bool (and .179 .180))
(define-fun .182 () Bool (< .9 .66))
(define-fun .183 () Bool (and .181 .182))
(define-fun .184 () Bool (< .66 .75))
(define-fun .185 () Bool (and .183 .184))
(define-fun .186 () Bool (< .9 .68))
(define-fun .187 () Bool (and .185 .186))
(define-fun .188 () Bool (< .68 .75))
(define-fun .189 () Bool (and .187 .188))
(define-fun .190 () Bool (< .9 .70))
(define-fun .191 () Bool (and .189 .190))
(define-fun .192 () Bool (< .70 .75))
(define-fun .193 () Bool (and .191 .192))
(assert .193)
(check-sat)
