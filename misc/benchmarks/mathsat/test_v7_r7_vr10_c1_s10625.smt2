(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(declare-fun x4 () (_ FloatingPoint 8 24))
(declare-fun x5 () (_ FloatingPoint 8 24))
(declare-fun x6 () (_ FloatingPoint 8 24))
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
(assert (let ((.def_36 (fp.leq x5 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_35 (fp.leq (fp #b1 #b10000010 #b01000000000000000000000) x5)))
(let ((.def_37 (and .def_35 .def_36)))
.def_37))))
(assert (let ((.def_40 (fp.leq x6 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_39 (fp.leq (fp #b1 #b10000010 #b01000000000000000000000) x6)))
(let ((.def_41 (and .def_39 .def_40)))
.def_41))))
(assert (let ((.def_77 (fp.mul RNE x6 (fp #b0 #b01111110 #b01000111001010110000001))))
(let ((.def_73 (fp.mul RNE x5 (fp #b0 #b01111101 #b11101111100111011011001))))
(let ((.def_69 (fp.mul RNE x4 (fp #b0 #b01111101 #b11001100110011001100110))))
(let ((.def_65 (fp.mul RNE x3 (fp #b1 #b01111100 #b00011010100111111011111))))
(let ((.def_60 (fp.mul RNE x2 (fp #b0 #b01111100 #b01110100101111000110101))))
(let ((.def_56 (fp.mul RNE x1 (fp #b1 #b01111110 #b11111100111011011001001))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111110 #b01101110000101000111101))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_57 (fp.add RNE .def_52 .def_56)))
(let ((.def_61 (fp.add RNE .def_57 .def_60)))
(let ((.def_66 (fp.add RNE .def_61 .def_65)))
(let ((.def_70 (fp.add RNE .def_66 .def_69)))
(let ((.def_74 (fp.add RNE .def_70 .def_73)))
(let ((.def_78 (fp.add RNE .def_74 .def_77)))
(let ((.def_79 (fp.leq .def_78 (fp #b1 #b01111110 #b01101111000110101010000))))
.def_79))))))))))))))))
(assert (let ((.def_114 (fp.mul RNE x6 (fp #b1 #b01111110 #b01011011001000101101000))))
(let ((.def_109 (fp.mul RNE x5 (fp #b1 #b01111110 #b01000110001001001101111))))
(let ((.def_104 (fp.mul RNE x4 (fp #b0 #b01111110 #b11100101111000110101010))))
(let ((.def_100 (fp.mul RNE x3 (fp #b1 #b01111101 #b11110101110000101001000))))
(let ((.def_95 (fp.mul RNE x2 (fp #b1 #b01111100 #b01100000010000011000101))))
(let ((.def_90 (fp.mul RNE x1 (fp #b0 #b01111011 #b00010010011011101001100))))
(let ((.def_86 (fp.mul RNE x0 (fp #b1 #b01111101 #b00111100011010100111111))))
(let ((.def_87 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_86)))
(let ((.def_91 (fp.add RNE .def_87 .def_90)))
(let ((.def_96 (fp.add RNE .def_91 .def_95)))
(let ((.def_101 (fp.add RNE .def_96 .def_100)))
(let ((.def_105 (fp.add RNE .def_101 .def_104)))
(let ((.def_110 (fp.add RNE .def_105 .def_109)))
(let ((.def_115 (fp.add RNE .def_110 .def_114)))
(let ((.def_116 (fp.leq .def_115 (fp #b1 #b01111101 #b00110111010010111100011))))
.def_116))))))))))))))))
(assert (let ((.def_150 (fp.mul RNE x6 (fp #b1 #b01111011 #b11010010111100011010101))))
(let ((.def_145 (fp.mul RNE x5 (fp #b0 #b01111100 #b11100101011000000100001))))
(let ((.def_141 (fp.mul RNE x4 (fp #b1 #b01111011 #b00011110101110000101001))))
(let ((.def_136 (fp.mul RNE x3 (fp #b1 #b01111101 #b01000101101000011100101))))
(let ((.def_131 (fp.mul RNE x2 (fp #b1 #b01111101 #b10100010110100001110011))))
(let ((.def_126 (fp.mul RNE x1 (fp #b0 #b01111110 #b00111110111110011101110))))
(let ((.def_122 (fp.mul RNE x0 (fp #b0 #b01111110 #b00100100110111010011000))))
(let ((.def_123 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_122)))
(let ((.def_127 (fp.add RNE .def_123 .def_126)))
(let ((.def_132 (fp.add RNE .def_127 .def_131)))
(let ((.def_137 (fp.add RNE .def_132 .def_136)))
(let ((.def_142 (fp.add RNE .def_137 .def_141)))
(let ((.def_146 (fp.add RNE .def_142 .def_145)))
(let ((.def_151 (fp.add RNE .def_146 .def_150)))
(let ((.def_152 (fp.leq .def_151 (fp #b1 #b01111101 #b11000101101000011100101))))
.def_152))))))))))))))))
(assert (let ((.def_184 (fp.mul RNE x6 (fp #b0 #b01111110 #b11110100001110010101100))))
(let ((.def_180 (fp.mul RNE x5 (fp #b1 #b01111110 #b10001110110110010001011))))
(let ((.def_175 (fp.mul RNE x4 (fp #b0 #b01111110 #b10000111101011100001010))))
(let ((.def_171 (fp.mul RNE x3 (fp #b1 #b01111110 #b10000100100110111010011))))
(let ((.def_166 (fp.mul RNE x2 (fp #b1 #b01111101 #b01011111001110110110010))))
(let ((.def_161 (fp.mul RNE x1 (fp #b0 #b01111110 #b10111100011010100111111))))
(let ((.def_157 (fp.mul RNE x0 (fp #b0 #b01111110 #b00011111101111100111011))))
(let ((.def_158 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_157)))
(let ((.def_162 (fp.add RNE .def_158 .def_161)))
(let ((.def_167 (fp.add RNE .def_162 .def_166)))
(let ((.def_172 (fp.add RNE .def_167 .def_171)))
(let ((.def_176 (fp.add RNE .def_172 .def_175)))
(let ((.def_181 (fp.add RNE .def_176 .def_180)))
(let ((.def_185 (fp.add RNE .def_181 .def_184)))
(let ((.def_186 (fp.leq (fp #b0 #b01111011 #b00000010000011000100101) .def_185)))
.def_186))))))))))))))))
(assert (let ((.def_222 (fp.mul RNE x6 (fp #b1 #b01111110 #b00001010110000001000010))))
(let ((.def_217 (fp.mul RNE x5 (fp #b1 #b01111101 #b01101110100101111000111))))
(let ((.def_212 (fp.mul RNE x4 (fp #b0 #b01111110 #b01000011100101011000001))))
(let ((.def_208 (fp.mul RNE x3 (fp #b1 #b01111110 #b11110111110011101101101))))
(let ((.def_203 (fp.mul RNE x2 (fp #b1 #b01111101 #b01011110001101010100000))))
(let ((.def_198 (fp.mul RNE x1 (fp #b1 #b01111110 #b00100101111000110101010))))
(let ((.def_193 (fp.mul RNE x0 (fp #b1 #b01111110 #b01110001101010011111110))))
(let ((.def_194 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_193)))
(let ((.def_199 (fp.add RNE .def_194 .def_198)))
(let ((.def_204 (fp.add RNE .def_199 .def_203)))
(let ((.def_209 (fp.add RNE .def_204 .def_208)))
(let ((.def_213 (fp.add RNE .def_209 .def_212)))
(let ((.def_218 (fp.add RNE .def_213 .def_217)))
(let ((.def_223 (fp.add RNE .def_218 .def_222)))
(let ((.def_224 (fp.leq .def_223 (fp #b1 #b01111100 #b01011110001101010100000))))
.def_224))))))))))))))))
(assert (let ((.def_259 (fp.mul RNE x6 (fp #b1 #b01111100 #b00010100011110101110001))))
(let ((.def_254 (fp.mul RNE x5 (fp #b1 #b01111100 #b10000001000001100010010))))
(let ((.def_249 (fp.mul RNE x4 (fp #b1 #b01111110 #b01011100001010001111011))))
(let ((.def_244 (fp.mul RNE x3 (fp #b0 #b01111101 #b10011000100100110111010))))
(let ((.def_240 (fp.mul RNE x2 (fp #b1 #b01111101 #b11001000101101000011101))))
(let ((.def_235 (fp.mul RNE x1 (fp #b1 #b01111011 #b11000110101001111111000))))
(let ((.def_230 (fp.mul RNE x0 (fp #b0 #b01111101 #b01111110111110011101110))))
(let ((.def_231 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_230)))
(let ((.def_236 (fp.add RNE .def_231 .def_235)))
(let ((.def_241 (fp.add RNE .def_236 .def_240)))
(let ((.def_245 (fp.add RNE .def_241 .def_244)))
(let ((.def_250 (fp.add RNE .def_245 .def_249)))
(let ((.def_255 (fp.add RNE .def_250 .def_254)))
(let ((.def_260 (fp.add RNE .def_255 .def_259)))
(let ((.def_261 (fp.leq .def_260 (fp #b1 #b01111101 #b00010111100011010101000))))
.def_261))))))))))))))))
(assert (let ((.def_295 (fp.mul RNE x6 (fp #b1 #b01111101 #b11100010010011011101001))))
(let ((.def_290 (fp.mul RNE x5 (fp #b1 #b01111010 #b01111000110101001111111))))
(let ((.def_285 (fp.mul RNE x4 (fp #b1 #b01111110 #b01101100100010110100010))))
(let ((.def_280 (fp.mul RNE x3 (fp #b0 #b01111110 #b01101011000000100000110))))
(let ((.def_276 (fp.mul RNE x2 (fp #b0 #b01111101 #b10001000001100010010011))))
(let ((.def_272 (fp.mul RNE x1 (fp #b0 #b01111110 #b01111000110101001111111))))
(let ((.def_268 (fp.mul RNE x0 (fp #b1 #b01111100 #b11001110110110010001011))))
(let ((.def_269 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_268)))
(let ((.def_273 (fp.add RNE .def_269 .def_272)))
(let ((.def_277 (fp.add RNE .def_273 .def_276)))
(let ((.def_281 (fp.add RNE .def_277 .def_280)))
(let ((.def_286 (fp.add RNE .def_281 .def_285)))
(let ((.def_291 (fp.add RNE .def_286 .def_290)))
(let ((.def_296 (fp.add RNE .def_291 .def_295)))
(let ((.def_297 (fp.leq (fp #b1 #b01111110 #b00100011010100111111100) .def_296)))
.def_297))))))))))))))))
(check-sat)
