(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(declare-fun x4 () (_ FloatingPoint 8 24))
(assert (let ((.def_16 (fp.leq x0 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_15 (fp.leq (fp #b1 #b10000010 #b01000000000000000000000) x0)))
(let ((.def_17 (and .def_15 .def_16)))
.def_17))))
(assert (let ((.def_20 (fp.leq x1 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_19 (fp.leq (fp #b1 #b10000010 #b01000000000000000000000) x1)))
(let ((.def_21 (and .def_19 .def_20)))
.def_21))))
(assert (let ((.def_24 (fp.leq x2 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_23 (fp.leq (fp #b1 #b10000010 #b01000000000000000000000) x2)))
(let ((.def_25 (and .def_23 .def_24)))
.def_25))))
(assert (let ((.def_28 (fp.leq x3 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_27 (fp.leq (fp #b1 #b10000010 #b01000000000000000000000) x3)))
(let ((.def_29 (and .def_27 .def_28)))
.def_29))))
(assert (let ((.def_32 (fp.leq x4 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_31 (fp.leq (fp #b1 #b10000010 #b01000000000000000000000) x4)))
(let ((.def_33 (and .def_31 .def_32)))
.def_33))))
(assert (let ((.def_63 (fp.mul RNE x4 (fp #b1 #b01111110 #b11001010001111010111000))))
(let ((.def_58 (fp.mul RNE x3 (fp #b0 #b01111110 #b10010000111001010110000))))
(let ((.def_54 (fp.mul RNE x2 (fp #b1 #b01111101 #b10011111101111100111011))))
(let ((.def_49 (fp.mul RNE x1 (fp #b1 #b01111110 #b00111010010111100011011))))
(let ((.def_44 (fp.mul RNE x0 (fp #b1 #b01111100 #b00111001010110000001000))))
(let ((.def_45 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_44)))
(let ((.def_50 (fp.add RNE .def_45 .def_49)))
(let ((.def_55 (fp.add RNE .def_50 .def_54)))
(let ((.def_59 (fp.add RNE .def_55 .def_58)))
(let ((.def_64 (fp.add RNE .def_59 .def_63)))
(let ((.def_65 (fp.leq .def_64 (fp #b1 #b01111110 #b10111110011101101100100))))
.def_65))))))))))))
(assert (let ((.def_90 (fp.mul RNE x4 (fp #b1 #b01111110 #b10011110001101010100000))))
(let ((.def_85 (fp.mul RNE x3 (fp #b0 #b01111101 #b11101001011110001101010))))
(let ((.def_81 (fp.mul RNE x2 (fp #b0 #b01111000 #b10001001001101110100110))))
(let ((.def_77 (fp.mul RNE x1 (fp #b1 #b01111101 #b01111101111100111011011))))
(let ((.def_72 (fp.mul RNE x0 (fp #b1 #b01111110 #b01110001101010011111110))))
(let ((.def_73 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_72)))
(let ((.def_78 (fp.add RNE .def_73 .def_77)))
(let ((.def_82 (fp.add RNE .def_78 .def_81)))
(let ((.def_86 (fp.add RNE .def_82 .def_85)))
(let ((.def_91 (fp.add RNE .def_86 .def_90)))
(let ((.def_92 (fp.leq (fp #b1 #b01111000 #b11101011100001010001111) .def_91)))
.def_92))))))))))))
(assert (let ((.def_116 (fp.mul RNE x4 (fp #b1 #b01111110 #b10101100100010110100010))))
(let ((.def_111 (fp.mul RNE x3 (fp #b0 #b01111010 #b01100000010000011000101))))
(let ((.def_107 (fp.mul RNE x2 (fp #b1 #b01111101 #b00001100010010011011101))))
(let ((.def_102 (fp.mul RNE x1 (fp #b1 #b01111110 #b11001111110111110011110))))
(let ((.def_97 (fp.mul RNE x0 (fp #b0 #b01111110 #b01110110010001011010001))))
(let ((.def_98 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_97)))
(let ((.def_103 (fp.add RNE .def_98 .def_102)))
(let ((.def_108 (fp.add RNE .def_103 .def_107)))
(let ((.def_112 (fp.add RNE .def_108 .def_111)))
(let ((.def_117 (fp.add RNE .def_112 .def_116)))
(let ((.def_118 (fp.leq (fp #b0 #b01111101 #b10110011001100110011010) .def_117)))
.def_118))))))))))))
(assert (let ((.def_145 (fp.mul RNE x4 (fp #b1 #b01111110 #b10001001101110100101111))))
(let ((.def_140 (fp.mul RNE x3 (fp #b1 #b01111101 #b00000011000100100110111))))
(let ((.def_135 (fp.mul RNE x2 (fp #b1 #b01111110 #b10111010010111100011011))))
(let ((.def_130 (fp.mul RNE x1 (fp #b1 #b01111110 #b10011001000101101000100))))
(let ((.def_125 (fp.mul RNE x0 (fp #b1 #b01111110 #b10100100010110100001110))))
(let ((.def_126 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_125)))
(let ((.def_131 (fp.add RNE .def_126 .def_130)))
(let ((.def_136 (fp.add RNE .def_131 .def_135)))
(let ((.def_141 (fp.add RNE .def_136 .def_140)))
(let ((.def_146 (fp.add RNE .def_141 .def_145)))
(let ((.def_147 (fp.leq (fp #b1 #b01111110 #b00011111101111100111011) .def_146)))
.def_147))))))))))))
(assert (let ((.def_171 (fp.mul RNE x4 (fp #b1 #b01111101 #b00110101001111110111110))))
(let ((.def_166 (fp.mul RNE x3 (fp #b0 #b01111110 #b01010010011011101001100))))
(let ((.def_162 (fp.mul RNE x2 (fp #b0 #b01111110 #b11110001101010011111110))))
(let ((.def_158 (fp.mul RNE x1 (fp #b0 #b01111110 #b10111000010100011110110))))
(let ((.def_154 (fp.mul RNE x0 (fp #b1 #b01111101 #b01101110100101111000111))))
(let ((.def_155 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_154)))
(let ((.def_159 (fp.add RNE .def_155 .def_158)))
(let ((.def_163 (fp.add RNE .def_159 .def_162)))
(let ((.def_167 (fp.add RNE .def_163 .def_166)))
(let ((.def_172 (fp.add RNE .def_167 .def_171)))
(let ((.def_173 (fp.leq (fp #b1 #b01111101 #b10010110100001110010110) .def_172)))
.def_173))))))))))))
(assert (let ((.def_197 (fp.mul RNE x4 (fp #b0 #b01111011 #b10000101000111101011100))))
(let ((.def_193 (fp.mul RNE x3 (fp #b1 #b01111110 #b10000110101001111111000))))
(let ((.def_188 (fp.mul RNE x2 (fp #b1 #b01111101 #b01110100101111000110101))))
(let ((.def_183 (fp.mul RNE x1 (fp #b0 #b01111110 #b10011100001010001111011))))
(let ((.def_179 (fp.mul RNE x0 (fp #b0 #b01111110 #b00000111101011100001010))))
(let ((.def_180 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_179)))
(let ((.def_184 (fp.add RNE .def_180 .def_183)))
(let ((.def_189 (fp.add RNE .def_184 .def_188)))
(let ((.def_194 (fp.add RNE .def_189 .def_193)))
(let ((.def_198 (fp.add RNE .def_194 .def_197)))
(let ((.def_199 (fp.leq (fp #b1 #b01111011 #b10011001100110011001101) .def_198)))
.def_199))))))))))))
(assert (let ((.def_223 (fp.mul RNE x4 (fp #b1 #b01111011 #b00000010000011000100101))))
(let ((.def_218 (fp.mul RNE x3 (fp #b1 #b01111100 #b00101000111101011100001))))
(let ((.def_213 (fp.mul RNE x2 (fp #b1 #b01111100 #b01001101110100101111001))))
(let ((.def_208 (fp.mul RNE x1 (fp #b0 #b01111101 #b00001001001101110100110))))
(let ((.def_204 (fp.mul RNE x0 (fp #b0 #b01111110 #b11100111011011001000110))))
(let ((.def_205 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_204)))
(let ((.def_209 (fp.add RNE .def_205 .def_208)))
(let ((.def_214 (fp.add RNE .def_209 .def_213)))
(let ((.def_219 (fp.add RNE .def_214 .def_218)))
(let ((.def_224 (fp.add RNE .def_219 .def_223)))
(let ((.def_225 (fp.leq (fp #b0 #b01111110 #b11110101001111110111110) .def_224)))
.def_225))))))))))))
(assert (let ((.def_246 (fp.mul RNE x4 (fp #b0 #b01111110 #b00000000000000000000000))))
(let ((.def_242 (fp.mul RNE x3 (fp #b0 #b01111101 #b11110111110011101101101))))
(let ((.def_238 (fp.mul RNE x2 (fp #b1 #b01111110 #b10111101011100001010010))))
(let ((.def_233 (fp.mul RNE x1 (fp #b0 #b01111110 #b10111010010111100011011))))
(let ((.def_231 (fp.mul RNE x0 (fp #b1 #b01111110 #b10110010001011010000111))))
(let ((.def_232 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_231)))
(let ((.def_234 (fp.add RNE .def_232 .def_233)))
(let ((.def_239 (fp.add RNE .def_234 .def_238)))
(let ((.def_243 (fp.add RNE .def_239 .def_242)))
(let ((.def_247 (fp.add RNE .def_243 .def_246)))
(let ((.def_248 (fp.leq .def_247 (fp #b0 #b01111100 #b11000100100110111010011))))
.def_248))))))))))))
(assert (let ((.def_270 (fp.mul RNE x4 (fp #b0 #b01111110 #b00010000011000100100111))))
(let ((.def_266 (fp.mul RNE x3 (fp #b0 #b01111100 #b00000110001001001101111))))
(let ((.def_262 (fp.mul RNE x2 (fp #b0 #b01111101 #b11110000101000111101100))))
(let ((.def_258 (fp.mul RNE x1 (fp #b1 #b01111110 #b01000010100011110101110))))
(let ((.def_253 (fp.mul RNE x0 (fp #b0 #b01111110 #b11010010111100011010101))))
(let ((.def_254 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_253)))
(let ((.def_259 (fp.add RNE .def_254 .def_258)))
(let ((.def_263 (fp.add RNE .def_259 .def_262)))
(let ((.def_267 (fp.add RNE .def_263 .def_266)))
(let ((.def_271 (fp.add RNE .def_267 .def_270)))
(let ((.def_272 (fp.leq (fp #b0 #b01111110 #b00000011000100100110111) .def_271)))
.def_272))))))))))))
(assert (let ((.def_297 (fp.mul RNE x4 (fp #b1 #b01111100 #b01111110111110011101110))))
(let ((.def_292 (fp.mul RNE x3 (fp #b1 #b01111110 #b11011110001101010100000))))
(let ((.def_287 (fp.mul RNE x2 (fp #b1 #b01111101 #b01101111100111011011001))))
(let ((.def_282 (fp.mul RNE x1 (fp #b0 #b01111110 #b10100001110010101100000))))
(let ((.def_278 (fp.mul RNE x0 (fp #b0 #b01111110 #b11010110100001110010110))))
(let ((.def_279 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_278)))
(let ((.def_283 (fp.add RNE .def_279 .def_282)))
(let ((.def_288 (fp.add RNE .def_283 .def_287)))
(let ((.def_293 (fp.add RNE .def_288 .def_292)))
(let ((.def_298 (fp.add RNE .def_293 .def_297)))
(let ((.def_299 (fp.leq .def_298 (fp #b1 #b01111110 #b00000001100010010011100))))
.def_299))))))))))))
(check-sat)
