(set-logic QF_FPABV)
(declare-fun b104 () (_ FP 8 24))
(declare-fun b80 () (_ FP 8 24))
(declare-fun b92 () (_ FP 8 24))
(declare-fun b56 () (_ FP 8 24))
(declare-fun b10 () (_ FP 8 24))
(declare-fun b125 () (_ FP 8 24))
(declare-fun b41 () (_ FP 8 24))
(declare-fun b32 () (_ FP 8 24))
(declare-fun b113 () (_ FP 8 24))
(declare-fun b23 () (_ FP 8 24))
(declare-fun b62 () (_ FP 8 24))
(declare-fun b77 () (_ FP 8 24))
(declare-fun b26 () (_ FP 8 24))
(declare-fun b110 () (_ FP 8 24))
(declare-fun b20 () (_ FP 8 24))
(declare-fun b89 () (_ FP 8 24))
(declare-fun b74 () (_ FP 8 24))
(declare-fun b116 () (_ FP 8 24))
(declare-fun b95 () (_ FP 8 24))
(declare-fun b59 () (_ FP 8 24))
(declare-fun b98 () (_ FP 8 24))
(declare-fun b222 () (_ FP 8 24))
(declare-fun b29 () (_ FP 8 24))
(declare-fun b47 () (_ FP 8 24))
(declare-fun b68 () (_ FP 8 24))
(declare-fun b14 () (_ FP 8 24))
(declare-fun b44 () (_ FP 8 24))
(declare-fun b101 () (_ FP 8 24))
(declare-fun b219 () (_ FP 8 24))
(declare-fun b122 () (_ FP 8 24))
(declare-fun b50 () (_ FP 8 24))
(declare-fun b128 () (_ FP 8 24))
(declare-fun b35 () (_ FP 8 24))
(declare-fun b17 () (_ FP 8 24))
(declare-fun b71 () (_ FP 8 24))
(declare-fun b107 () (_ FP 8 24))
(declare-fun b86 () (_ FP 8 24))
(declare-fun b119 () (_ FP 8 24))
(declare-fun b11 () (_ FP 8 24))
(declare-fun b83 () (_ FP 8 24))
(declare-fun b65 () (_ FP 8 24))
(declare-fun b38 () (_ FP 8 24))
(declare-fun b131 () (_ FP 8 24))
(declare-fun b53 () (_ FP 8 24))
(define-fun .3 () RoundingMode roundNearestTiesToEven)
(define-fun .9 () (_ FP 8 24) b219)
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
(define-fun .73 () (_ FP 8 24) (* .3 .71 .72))
(define-fun .74 () (_ FP 8 24) b104)
(define-fun .75 () (_ FP 8 24) (* .3 .73 .74))
(define-fun .76 () (_ FP 8 24) b107)
(define-fun .77 () (_ FP 8 24) (* .3 .75 .76))
(define-fun .78 () (_ FP 8 24) b110)
(define-fun .79 () (_ FP 8 24) (* .3 .77 .78))
(define-fun .80 () (_ FP 8 24) b113)
(define-fun .81 () (_ FP 8 24) (* .3 .79 .80))
(define-fun .82 () (_ FP 8 24) b116)
(define-fun .83 () (_ FP 8 24) (* .3 .81 .82))
(define-fun .84 () (_ FP 8 24) b119)
(define-fun .85 () (_ FP 8 24) (* .3 .83 .84))
(define-fun .86 () (_ FP 8 24) b122)
(define-fun .87 () (_ FP 8 24) (* .3 .85 .86))
(define-fun .88 () (_ FP 8 24) b125)
(define-fun .89 () (_ FP 8 24) (* .3 .87 .88))
(define-fun .90 () (_ FP 8 24) b128)
(define-fun .91 () (_ FP 8 24) (* .3 .89 .90))
(define-fun .92 () (_ FP 8 24) b131)
(define-fun .93 () Bool (< .91 .92))
(define-fun .94 () Bool (and .11 .93))
(define-fun .95 () (_ FP 8 24) b222)
(define-fun .96 () Bool (< .10 .95))
(define-fun .97 () Bool (and .94 .96))
(define-fun .98 () Bool (< .9 .14))
(define-fun .99 () Bool (and .97 .98))
(define-fun .100 () Bool (< .14 .95))
(define-fun .101 () Bool (and .99 .100))
(define-fun .102 () Bool (< .9 .16))
(define-fun .103 () Bool (and .101 .102))
(define-fun .104 () Bool (< .16 .95))
(define-fun .105 () Bool (and .103 .104))
(define-fun .106 () Bool (< .9 .18))
(define-fun .107 () Bool (and .105 .106))
(define-fun .108 () Bool (< .18 .95))
(define-fun .109 () Bool (and .107 .108))
(define-fun .110 () Bool (< .9 .20))
(define-fun .111 () Bool (and .109 .110))
(define-fun .112 () Bool (< .20 .95))
(define-fun .113 () Bool (and .111 .112))
(define-fun .114 () Bool (< .9 .22))
(define-fun .115 () Bool (and .113 .114))
(define-fun .116 () Bool (< .22 .95))
(define-fun .117 () Bool (and .115 .116))
(define-fun .118 () Bool (< .9 .24))
(define-fun .119 () Bool (and .117 .118))
(define-fun .120 () Bool (< .24 .95))
(define-fun .121 () Bool (and .119 .120))
(define-fun .122 () Bool (< .9 .26))
(define-fun .123 () Bool (and .121 .122))
(define-fun .124 () Bool (< .26 .95))
(define-fun .125 () Bool (and .123 .124))
(define-fun .126 () Bool (< .9 .28))
(define-fun .127 () Bool (and .125 .126))
(define-fun .128 () Bool (< .28 .95))
(define-fun .129 () Bool (and .127 .128))
(define-fun .130 () Bool (< .9 .30))
(define-fun .131 () Bool (and .129 .130))
(define-fun .132 () Bool (< .30 .95))
(define-fun .133 () Bool (and .131 .132))
(define-fun .134 () Bool (< .9 .32))
(define-fun .135 () Bool (and .133 .134))
(define-fun .136 () Bool (< .32 .95))
(define-fun .137 () Bool (and .135 .136))
(define-fun .138 () Bool (< .9 .34))
(define-fun .139 () Bool (and .137 .138))
(define-fun .140 () Bool (< .34 .95))
(define-fun .141 () Bool (and .139 .140))
(define-fun .142 () Bool (< .9 .36))
(define-fun .143 () Bool (and .141 .142))
(define-fun .144 () Bool (< .36 .95))
(define-fun .145 () Bool (and .143 .144))
(define-fun .146 () Bool (< .9 .38))
(define-fun .147 () Bool (and .145 .146))
(define-fun .148 () Bool (< .38 .95))
(define-fun .149 () Bool (and .147 .148))
(define-fun .150 () Bool (< .9 .40))
(define-fun .151 () Bool (and .149 .150))
(define-fun .152 () Bool (< .40 .95))
(define-fun .153 () Bool (and .151 .152))
(define-fun .154 () Bool (< .9 .42))
(define-fun .155 () Bool (and .153 .154))
(define-fun .156 () Bool (< .42 .95))
(define-fun .157 () Bool (and .155 .156))
(define-fun .158 () Bool (< .9 .44))
(define-fun .159 () Bool (and .157 .158))
(define-fun .160 () Bool (< .44 .95))
(define-fun .161 () Bool (and .159 .160))
(define-fun .162 () Bool (< .9 .46))
(define-fun .163 () Bool (and .161 .162))
(define-fun .164 () Bool (< .46 .95))
(define-fun .165 () Bool (and .163 .164))
(define-fun .166 () Bool (< .9 .48))
(define-fun .167 () Bool (and .165 .166))
(define-fun .168 () Bool (< .48 .95))
(define-fun .169 () Bool (and .167 .168))
(define-fun .170 () Bool (< .9 .50))
(define-fun .171 () Bool (and .169 .170))
(define-fun .172 () Bool (< .50 .95))
(define-fun .173 () Bool (and .171 .172))
(define-fun .174 () Bool (< .9 .52))
(define-fun .175 () Bool (and .173 .174))
(define-fun .176 () Bool (< .52 .95))
(define-fun .177 () Bool (and .175 .176))
(define-fun .178 () Bool (< .9 .54))
(define-fun .179 () Bool (and .177 .178))
(define-fun .180 () Bool (< .54 .95))
(define-fun .181 () Bool (and .179 .180))
(define-fun .182 () Bool (< .9 .56))
(define-fun .183 () Bool (and .181 .182))
(define-fun .184 () Bool (< .56 .95))
(define-fun .185 () Bool (and .183 .184))
(define-fun .186 () Bool (< .9 .58))
(define-fun .187 () Bool (and .185 .186))
(define-fun .188 () Bool (< .58 .95))
(define-fun .189 () Bool (and .187 .188))
(define-fun .190 () Bool (< .9 .60))
(define-fun .191 () Bool (and .189 .190))
(define-fun .192 () Bool (< .60 .95))
(define-fun .193 () Bool (and .191 .192))
(define-fun .194 () Bool (< .9 .62))
(define-fun .195 () Bool (and .193 .194))
(define-fun .196 () Bool (< .62 .95))
(define-fun .197 () Bool (and .195 .196))
(define-fun .198 () Bool (< .9 .64))
(define-fun .199 () Bool (and .197 .198))
(define-fun .200 () Bool (< .64 .95))
(define-fun .201 () Bool (and .199 .200))
(define-fun .202 () Bool (< .9 .66))
(define-fun .203 () Bool (and .201 .202))
(define-fun .204 () Bool (< .66 .95))
(define-fun .205 () Bool (and .203 .204))
(define-fun .206 () Bool (< .9 .68))
(define-fun .207 () Bool (and .205 .206))
(define-fun .208 () Bool (< .68 .95))
(define-fun .209 () Bool (and .207 .208))
(define-fun .210 () Bool (< .9 .70))
(define-fun .211 () Bool (and .209 .210))
(define-fun .212 () Bool (< .70 .95))
(define-fun .213 () Bool (and .211 .212))
(define-fun .214 () Bool (< .9 .72))
(define-fun .215 () Bool (and .213 .214))
(define-fun .216 () Bool (< .72 .95))
(define-fun .217 () Bool (and .215 .216))
(define-fun .218 () Bool (< .9 .74))
(define-fun .219 () Bool (and .217 .218))
(define-fun .220 () Bool (< .74 .95))
(define-fun .221 () Bool (and .219 .220))
(define-fun .222 () Bool (< .9 .76))
(define-fun .223 () Bool (and .221 .222))
(define-fun .224 () Bool (< .76 .95))
(define-fun .225 () Bool (and .223 .224))
(define-fun .226 () Bool (< .9 .78))
(define-fun .227 () Bool (and .225 .226))
(define-fun .228 () Bool (< .78 .95))
(define-fun .229 () Bool (and .227 .228))
(define-fun .230 () Bool (< .9 .80))
(define-fun .231 () Bool (and .229 .230))
(define-fun .232 () Bool (< .80 .95))
(define-fun .233 () Bool (and .231 .232))
(define-fun .234 () Bool (< .9 .82))
(define-fun .235 () Bool (and .233 .234))
(define-fun .236 () Bool (< .82 .95))
(define-fun .237 () Bool (and .235 .236))
(define-fun .238 () Bool (< .9 .84))
(define-fun .239 () Bool (and .237 .238))
(define-fun .240 () Bool (< .84 .95))
(define-fun .241 () Bool (and .239 .240))
(define-fun .242 () Bool (< .9 .86))
(define-fun .243 () Bool (and .241 .242))
(define-fun .244 () Bool (< .86 .95))
(define-fun .245 () Bool (and .243 .244))
(define-fun .246 () Bool (< .9 .88))
(define-fun .247 () Bool (and .245 .246))
(define-fun .248 () Bool (< .88 .95))
(define-fun .249 () Bool (and .247 .248))
(define-fun .250 () Bool (< .9 .90))
(define-fun .251 () Bool (and .249 .250))
(define-fun .252 () Bool (< .90 .95))
(define-fun .253 () Bool (and .251 .252))
(assert .253)
(check-sat)