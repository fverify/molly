(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(declare-fun x4 () (_ FloatingPoint 8 24))
(declare-fun x5 () (_ FloatingPoint 8 24))
(declare-fun x6 () (_ FloatingPoint 8 24))
(assert (let ((.def_16 (fp.leq x0 (fp #b0 #b10000001 #b01000000000000000000000))))
(let ((.def_15 (fp.leq (fp #b1 #b10000001 #b01000000000000000000000) x0)))
(let ((.def_17 (and .def_15 .def_16)))
.def_17))))
(assert (let ((.def_20 (fp.leq x1 (fp #b0 #b10000001 #b01000000000000000000000))))
(let ((.def_19 (fp.leq (fp #b1 #b10000001 #b01000000000000000000000) x1)))
(let ((.def_21 (and .def_19 .def_20)))
.def_21))))
(assert (let ((.def_24 (fp.leq x2 (fp #b0 #b10000001 #b01000000000000000000000))))
(let ((.def_23 (fp.leq (fp #b1 #b10000001 #b01000000000000000000000) x2)))
(let ((.def_25 (and .def_23 .def_24)))
.def_25))))
(assert (let ((.def_28 (fp.leq x3 (fp #b0 #b10000001 #b01000000000000000000000))))
(let ((.def_27 (fp.leq (fp #b1 #b10000001 #b01000000000000000000000) x3)))
(let ((.def_29 (and .def_27 .def_28)))
.def_29))))
(assert (let ((.def_32 (fp.leq x4 (fp #b0 #b10000001 #b01000000000000000000000))))
(let ((.def_31 (fp.leq (fp #b1 #b10000001 #b01000000000000000000000) x4)))
(let ((.def_33 (and .def_31 .def_32)))
.def_33))))
(assert (let ((.def_36 (fp.leq x5 (fp #b0 #b10000001 #b01000000000000000000000))))
(let ((.def_35 (fp.leq (fp #b1 #b10000001 #b01000000000000000000000) x5)))
(let ((.def_37 (and .def_35 .def_36)))
.def_37))))
(assert (let ((.def_40 (fp.leq x6 (fp #b0 #b10000001 #b01000000000000000000000))))
(let ((.def_39 (fp.leq (fp #b1 #b10000001 #b01000000000000000000000) x6)))
(let ((.def_41 (and .def_39 .def_40)))
.def_41))))
(assert (let ((.def_77 (fp.mul RNE x6 (fp #b1 #b01111110 #b01100000110001001001110))))
(let ((.def_72 (fp.mul RNE x5 (fp #b0 #b01111100 #b00111111011111001110111))))
(let ((.def_68 (fp.mul RNE x4 (fp #b0 #b01111110 #b00010000111001010110000))))
(let ((.def_64 (fp.mul RNE x3 (fp #b1 #b01111000 #b01101000011100101011000))))
(let ((.def_59 (fp.mul RNE x2 (fp #b1 #b01111110 #b00011100101011000000100))))
(let ((.def_54 (fp.mul RNE x1 (fp #b0 #b01111110 #b11110011001100110011010))))
(let ((.def_50 (fp.mul RNE x0 (fp #b0 #b01111101 #b00000110001001001101111))))
(let ((.def_51 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_50)))
(let ((.def_55 (fp.add RNE .def_51 .def_54)))
(let ((.def_60 (fp.add RNE .def_55 .def_59)))
(let ((.def_65 (fp.add RNE .def_60 .def_64)))
(let ((.def_69 (fp.add RNE .def_65 .def_68)))
(let ((.def_73 (fp.add RNE .def_69 .def_72)))
(let ((.def_78 (fp.add RNE .def_73 .def_77)))
(let ((.def_79 (fp.leq (fp #b0 #b01111110 #b01000000100000110001001) .def_78)))
.def_79))))))))))))))))
(assert (let ((.def_113 (fp.mul RNE x6 (fp #b0 #b01111110 #b00011000100100110111010))))
(let ((.def_109 (fp.mul RNE x5 (fp #b1 #b01111011 #b00010110100001110010110))))
(let ((.def_104 (fp.mul RNE x4 (fp #b1 #b01111110 #b10111011011001000101101))))
(let ((.def_99 (fp.mul RNE x3 (fp #b0 #b01111110 #b00000011100101011000001))))
(let ((.def_95 (fp.mul RNE x2 (fp #b1 #b01111101 #b01111001110110110010001))))
(let ((.def_90 (fp.mul RNE x1 (fp #b0 #b01111011 #b00000110001001001101111))))
(let ((.def_86 (fp.mul RNE x0 (fp #b1 #b01111101 #b11000101101000011100101))))
(let ((.def_87 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_86)))
(let ((.def_91 (fp.add RNE .def_87 .def_90)))
(let ((.def_96 (fp.add RNE .def_91 .def_95)))
(let ((.def_100 (fp.add RNE .def_96 .def_99)))
(let ((.def_105 (fp.add RNE .def_100 .def_104)))
(let ((.def_110 (fp.add RNE .def_105 .def_109)))
(let ((.def_114 (fp.add RNE .def_110 .def_113)))
(let ((.def_115 (fp.leq .def_114 (fp #b1 #b01111110 #b10010101100000010000011))))
.def_115))))))))))))))))
(assert (let ((.def_147 (fp.mul RNE x6 (fp #b1 #b01111101 #b00011101101100100010111))))
(let ((.def_142 (fp.mul RNE x5 (fp #b1 #b01111110 #b00111110111110011101110))))
(let ((.def_137 (fp.mul RNE x4 (fp #b0 #b01111010 #b11000010100011110101110))))
(let ((.def_133 (fp.mul RNE x3 (fp #b0 #b01111101 #b00010001011010000111001))))
(let ((.def_129 (fp.mul RNE x2 (fp #b0 #b01111110 #b00111011111001110110110))))
(let ((.def_125 (fp.mul RNE x1 (fp #b0 #b01111101 #b00001001001101110100110))))
(let ((.def_121 (fp.mul RNE x0 (fp #b1 #b01111110 #b01011111001110110110010))))
(let ((.def_122 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_121)))
(let ((.def_126 (fp.add RNE .def_122 .def_125)))
(let ((.def_130 (fp.add RNE .def_126 .def_129)))
(let ((.def_134 (fp.add RNE .def_130 .def_133)))
(let ((.def_138 (fp.add RNE .def_134 .def_137)))
(let ((.def_143 (fp.add RNE .def_138 .def_142)))
(let ((.def_148 (fp.add RNE .def_143 .def_147)))
(let ((.def_149 (fp.leq .def_148 (fp #b0 #b01111110 #b11000111101011100001010))))
.def_149))))))))))))))))
(assert (let ((.def_178 (fp.mul RNE x6 (fp #b1 #b01111011 #b11010010111100011010101))))
(let ((.def_173 (fp.mul RNE x5 (fp #b0 #b01111101 #b10010000011000100100111))))
(let ((.def_169 (fp.mul RNE x4 (fp #b0 #b01111110 #b01010011011101001011110))))
(let ((.def_165 (fp.mul RNE x3 (fp #b0 #b01111101 #b00100011110101110000101))))
(let ((.def_161 (fp.mul RNE x2 (fp #b0 #b01111100 #b01110010101100000010000))))
(let ((.def_157 (fp.mul RNE x1 (fp #b1 #b01111100 #b10010011011101001011110))))
(let ((.def_152 (fp.mul RNE x0 (fp #b0 #b01111110 #b01011001100110011001101))))
(let ((.def_153 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_152)))
(let ((.def_158 (fp.add RNE .def_153 .def_157)))
(let ((.def_162 (fp.add RNE .def_158 .def_161)))
(let ((.def_166 (fp.add RNE .def_162 .def_165)))
(let ((.def_170 (fp.add RNE .def_166 .def_169)))
(let ((.def_174 (fp.add RNE .def_170 .def_173)))
(let ((.def_179 (fp.add RNE .def_174 .def_178)))
(let ((.def_180 (fp.leq (fp #b0 #b01111110 #b00000011100101011000001) .def_179)))
.def_180))))))))))))))))
(assert (let ((.def_215 (fp.mul RNE x6 (fp #b1 #b01111101 #b00100101111000110101010))))
(let ((.def_210 (fp.mul RNE x5 (fp #b0 #b01111110 #b01010001111010111000011))))
(let ((.def_206 (fp.mul RNE x4 (fp #b1 #b01111100 #b11011111001110110110010))))
(let ((.def_201 (fp.mul RNE x3 (fp #b0 #b01111110 #b00110011001100110011010))))
(let ((.def_197 (fp.mul RNE x2 (fp #b1 #b01111101 #b00011011101001011110010))))
(let ((.def_192 (fp.mul RNE x1 (fp #b1 #b01111101 #b11011110001101010100000))))
(let ((.def_187 (fp.mul RNE x0 (fp #b1 #b01111100 #b01111110111110011101110))))
(let ((.def_188 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_187)))
(let ((.def_193 (fp.add RNE .def_188 .def_192)))
(let ((.def_198 (fp.add RNE .def_193 .def_197)))
(let ((.def_202 (fp.add RNE .def_198 .def_201)))
(let ((.def_207 (fp.add RNE .def_202 .def_206)))
(let ((.def_211 (fp.add RNE .def_207 .def_210)))
(let ((.def_216 (fp.add RNE .def_211 .def_215)))
(let ((.def_217 (fp.leq .def_216 (fp #b1 #b01111011 #b01010011111101111100111))))
.def_217))))))))))))))))
(assert (let ((.def_250 (fp.mul RNE x6 (fp #b1 #b01111110 #b01011101001011110001101))))
(let ((.def_245 (fp.mul RNE x5 (fp #b0 #b01111011 #b00110011001100110011010))))
(let ((.def_241 (fp.mul RNE x4 (fp #b0 #b01111011 #b00011010100111111011111))))
(let ((.def_237 (fp.mul RNE x3 (fp #b0 #b01111110 #b11101011100001010001111))))
(let ((.def_233 (fp.mul RNE x2 (fp #b0 #b01111110 #b11011101001011110001101))))
(let ((.def_229 (fp.mul RNE x1 (fp #b1 #b01111110 #b01100100110111010011000))))
(let ((.def_224 (fp.mul RNE x0 (fp #b1 #b01111110 #b11101100100010110100010))))
(let ((.def_225 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_224)))
(let ((.def_230 (fp.add RNE .def_225 .def_229)))
(let ((.def_234 (fp.add RNE .def_230 .def_233)))
(let ((.def_238 (fp.add RNE .def_234 .def_237)))
(let ((.def_242 (fp.add RNE .def_238 .def_241)))
(let ((.def_246 (fp.add RNE .def_242 .def_245)))
(let ((.def_251 (fp.add RNE .def_246 .def_250)))
(let ((.def_252 (fp.leq .def_251 (fp #b1 #b01111110 #b00100111011011001000110))))
.def_252))))))))))))))))
(assert (let ((.def_286 (fp.mul RNE x6 (fp #b0 #b01111010 #b11101011100001010001111))))
(let ((.def_282 (fp.mul RNE x5 (fp #b0 #b01111110 #b00010001111010111000011))))
(let ((.def_278 (fp.mul RNE x4 (fp #b1 #b01111110 #b01111100011010100111111))))
(let ((.def_273 (fp.mul RNE x3 (fp #b1 #b01111110 #b00101101100100010110100))))
(let ((.def_268 (fp.mul RNE x2 (fp #b1 #b01111110 #b11011001100110011001101))))
(let ((.def_263 (fp.mul RNE x1 (fp #b1 #b01111110 #b00111001010110000001000))))
(let ((.def_258 (fp.mul RNE x0 (fp #b0 #b01111100 #b11111101111100111011011))))
(let ((.def_259 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_258)))
(let ((.def_264 (fp.add RNE .def_259 .def_263)))
(let ((.def_269 (fp.add RNE .def_264 .def_268)))
(let ((.def_274 (fp.add RNE .def_269 .def_273)))
(let ((.def_279 (fp.add RNE .def_274 .def_278)))
(let ((.def_283 (fp.add RNE .def_279 .def_282)))
(let ((.def_287 (fp.add RNE .def_283 .def_286)))
(let ((.def_288 (fp.leq .def_287 (fp #b1 #b01111110 #b00111101111100111011011))))
.def_288))))))))))))))))
(check-sat)