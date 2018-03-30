(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(declare-fun x4 () (_ FloatingPoint 8 24))
(declare-fun x5 () (_ FloatingPoint 8 24))
(declare-fun x6 () (_ FloatingPoint 8 24))
(assert (let ((.def_16 (fp.leq x0 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_15 (fp.leq (fp #b1 #b01111111 #b00000000000000000000000) x0)))
(let ((.def_17 (and .def_15 .def_16)))
.def_17))))
(assert (let ((.def_20 (fp.leq x1 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_19 (fp.leq (fp #b1 #b01111111 #b00000000000000000000000) x1)))
(let ((.def_21 (and .def_19 .def_20)))
.def_21))))
(assert (let ((.def_24 (fp.leq x2 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_23 (fp.leq (fp #b1 #b01111111 #b00000000000000000000000) x2)))
(let ((.def_25 (and .def_23 .def_24)))
.def_25))))
(assert (let ((.def_28 (fp.leq x3 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_27 (fp.leq (fp #b1 #b01111111 #b00000000000000000000000) x3)))
(let ((.def_29 (and .def_27 .def_28)))
.def_29))))
(assert (let ((.def_32 (fp.leq x4 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_31 (fp.leq (fp #b1 #b01111111 #b00000000000000000000000) x4)))
(let ((.def_33 (and .def_31 .def_32)))
.def_33))))
(assert (let ((.def_36 (fp.leq x5 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_35 (fp.leq (fp #b1 #b01111111 #b00000000000000000000000) x5)))
(let ((.def_37 (and .def_35 .def_36)))
.def_37))))
(assert (let ((.def_40 (fp.leq x6 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_39 (fp.leq (fp #b1 #b01111111 #b00000000000000000000000) x6)))
(let ((.def_41 (and .def_39 .def_40)))
.def_41))))
(assert (let ((.def_77 (fp.mul RNE x6 (fp #b0 #b01111110 #b10100001010001111010111))))
(let ((.def_73 (fp.mul RNE x5 (fp #b0 #b01111110 #b10110111010010111100011))))
(let ((.def_69 (fp.mul RNE x4 (fp #b1 #b01111101 #b11010011111101111100111))))
(let ((.def_64 (fp.mul RNE x3 (fp #b0 #b01111110 #b01011010000111001010110))))
(let ((.def_60 (fp.mul RNE x2 (fp #b0 #b01111110 #b10100011010100111111100))))
(let ((.def_56 (fp.mul RNE x1 (fp #b1 #b01111110 #b00101111100111011011001))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111110 #b10010111000010100011111))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_57 (fp.add RNE .def_52 .def_56)))
(let ((.def_61 (fp.add RNE .def_57 .def_60)))
(let ((.def_65 (fp.add RNE .def_61 .def_64)))
(let ((.def_70 (fp.add RNE .def_65 .def_69)))
(let ((.def_74 (fp.add RNE .def_70 .def_73)))
(let ((.def_78 (fp.add RNE .def_74 .def_77)))
(let ((.def_79 (fp.leq (fp #b1 #b01111110 #b10000010000011000100101) .def_78)))
.def_79))))))))))))))))
(assert (let ((.def_112 (fp.mul RNE x6 (fp #b1 #b01111101 #b01111000110101001111111))))
(let ((.def_107 (fp.mul RNE x5 (fp #b1 #b01111101 #b11011110001101010100000))))
(let ((.def_102 (fp.mul RNE x4 (fp #b1 #b01111000 #b01101000011100101011000))))
(let ((.def_97 (fp.mul RNE x3 (fp #b0 #b01111001 #b00010110100001110010110))))
(let ((.def_93 (fp.mul RNE x2 (fp #b1 #b01111000 #b00000110001001001101111))))
(let ((.def_88 (fp.mul RNE x1 (fp #b0 #b01111110 #b10010101100000010000011))))
(let ((.def_84 (fp.mul RNE x0 (fp #b0 #b01111101 #b00110100001110010101100))))
(let ((.def_85 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_84)))
(let ((.def_89 (fp.add RNE .def_85 .def_88)))
(let ((.def_94 (fp.add RNE .def_89 .def_93)))
(let ((.def_98 (fp.add RNE .def_94 .def_97)))
(let ((.def_103 (fp.add RNE .def_98 .def_102)))
(let ((.def_108 (fp.add RNE .def_103 .def_107)))
(let ((.def_113 (fp.add RNE .def_108 .def_112)))
(let ((.def_114 (fp.leq (fp #b0 #b01111101 #b00001111010111000010100) .def_113)))
.def_114))))))))))))))))
(assert (let ((.def_144 (fp.mul RNE x6 (fp #b0 #b01111101 #b11111100111011011001001))))
(let ((.def_140 (fp.mul RNE x5 (fp #b0 #b01111101 #b01001010110000001000010))))
(let ((.def_136 (fp.mul RNE x4 (fp #b0 #b01111110 #b11010001111010111000011))))
(let ((.def_132 (fp.mul RNE x3 (fp #b1 #b01111110 #b10110111010010111100011))))
(let ((.def_129 (fp.mul RNE x2 (fp #b1 #b01111101 #b00101011000000100000110))))
(let ((.def_124 (fp.mul RNE x1 (fp #b0 #b01111110 #b11000100100110111010011))))
(let ((.def_120 (fp.mul RNE x0 (fp #b1 #b01111110 #b10110101110000101001000))))
(let ((.def_121 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_120)))
(let ((.def_125 (fp.add RNE .def_121 .def_124)))
(let ((.def_130 (fp.add RNE .def_125 .def_129)))
(let ((.def_133 (fp.add RNE .def_130 .def_132)))
(let ((.def_137 (fp.add RNE .def_133 .def_136)))
(let ((.def_141 (fp.add RNE .def_137 .def_140)))
(let ((.def_145 (fp.add RNE .def_141 .def_144)))
(let ((.def_146 (fp.leq .def_145 (fp #b0 #b01111101 #b01000100100110111010011))))
.def_146))))))))))))))))
(assert (let ((.def_176 (fp.mul RNE x6 (fp #b0 #b01111101 #b01111100111011011001001))))
(let ((.def_172 (fp.mul RNE x5 (fp #b0 #b01111101 #b10101001111110111110100))))
(let ((.def_168 (fp.mul RNE x4 (fp #b0 #b01111110 #b10101110100101111000111))))
(let ((.def_164 (fp.mul RNE x3 (fp #b0 #b01111110 #b01101000111101011100001))))
(let ((.def_160 (fp.mul RNE x2 (fp #b0 #b01111110 #b10010110000001000001100))))
(let ((.def_156 (fp.mul RNE x1 (fp #b0 #b01111110 #b10001111110111110011110))))
(let ((.def_152 (fp.mul RNE x0 (fp #b0 #b01111101 #b10100001110010101100000))))
(let ((.def_153 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_152)))
(let ((.def_157 (fp.add RNE .def_153 .def_156)))
(let ((.def_161 (fp.add RNE .def_157 .def_160)))
(let ((.def_165 (fp.add RNE .def_161 .def_164)))
(let ((.def_169 (fp.add RNE .def_165 .def_168)))
(let ((.def_173 (fp.add RNE .def_169 .def_172)))
(let ((.def_177 (fp.add RNE .def_173 .def_176)))
(let ((.def_178 (fp.leq .def_177 (fp #b1 #b01111110 #b01110000001000001100010))))
.def_178))))))))))))))))
(assert (let ((.def_210 (fp.mul RNE x6 (fp #b1 #b01110111 #b11001010110000001000010))))
(let ((.def_205 (fp.mul RNE x5 (fp #b0 #b01111101 #b10011111101111100111011))))
(let ((.def_201 (fp.mul RNE x4 (fp #b1 #b01111110 #b10010110000001000001100))))
(let ((.def_198 (fp.mul RNE x3 (fp #b0 #b01111110 #b10001110110110010001011))))
(let ((.def_194 (fp.mul RNE x2 (fp #b1 #b01111100 #b01001001101110100101111))))
(let ((.def_189 (fp.mul RNE x1 (fp #b0 #b01111011 #b11011111001110110110010))))
(let ((.def_185 (fp.mul RNE x0 (fp #b1 #b01111110 #b00010001011010000111001))))
(let ((.def_186 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_185)))
(let ((.def_190 (fp.add RNE .def_186 .def_189)))
(let ((.def_195 (fp.add RNE .def_190 .def_194)))
(let ((.def_199 (fp.add RNE .def_195 .def_198)))
(let ((.def_202 (fp.add RNE .def_199 .def_201)))
(let ((.def_206 (fp.add RNE .def_202 .def_205)))
(let ((.def_211 (fp.add RNE .def_206 .def_210)))
(let ((.def_212 (fp.leq .def_211 (fp #b1 #b01111110 #b01000111001010110000001))))
.def_212))))))))))))))))
(assert (let ((.def_244 (fp.mul RNE x6 (fp #b0 #b01111010 #b01011000000100000110001))))
(let ((.def_240 (fp.mul RNE x5 (fp #b1 #b01111110 #b00000000000000000000000))))
(let ((.def_235 (fp.mul RNE x4 (fp #b0 #b01111100 #b11000110101001111111000))))
(let ((.def_231 (fp.mul RNE x3 (fp #b0 #b01111110 #b10011111001110110110010))))
(let ((.def_227 (fp.mul RNE x2 (fp #b1 #b01111110 #b10010011011101001011110))))
(let ((.def_222 (fp.mul RNE x1 (fp #b1 #b01111101 #b00011010100111111011111))))
(let ((.def_217 (fp.mul RNE x0 (fp #b0 #b01111101 #b10010001011010000111001))))
(let ((.def_218 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_217)))
(let ((.def_223 (fp.add RNE .def_218 .def_222)))
(let ((.def_228 (fp.add RNE .def_223 .def_227)))
(let ((.def_232 (fp.add RNE .def_228 .def_231)))
(let ((.def_236 (fp.add RNE .def_232 .def_235)))
(let ((.def_241 (fp.add RNE .def_236 .def_240)))
(let ((.def_245 (fp.add RNE .def_241 .def_244)))
(let ((.def_246 (fp.leq .def_245 (fp #b0 #b01111011 #b01010011111101111100111))))
.def_246))))))))))))))))
(assert (let ((.def_278 (fp.mul RNE x6 (fp #b1 #b01111101 #b10100110111010010111100))))
(let ((.def_273 (fp.mul RNE x5 (fp #b1 #b01111100 #b01010001111010111000011))))
(let ((.def_268 (fp.mul RNE x4 (fp #b0 #b01111110 #b01110100101111000110101))))
(let ((.def_264 (fp.mul RNE x3 (fp #b0 #b01111110 #b01100101011000000100001))))
(let ((.def_260 (fp.mul RNE x2 (fp #b0 #b01111100 #b01111110111110011101110))))
(let ((.def_256 (fp.mul RNE x1 (fp #b1 #b01111101 #b01011000000100000110001))))
(let ((.def_251 (fp.mul RNE x0 (fp #b0 #b01111101 #b10111010010111100011011))))
(let ((.def_252 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_251)))
(let ((.def_257 (fp.add RNE .def_252 .def_256)))
(let ((.def_261 (fp.add RNE .def_257 .def_260)))
(let ((.def_265 (fp.add RNE .def_261 .def_264)))
(let ((.def_269 (fp.add RNE .def_265 .def_268)))
(let ((.def_274 (fp.add RNE .def_269 .def_273)))
(let ((.def_279 (fp.add RNE .def_274 .def_278)))
(let ((.def_280 (fp.leq .def_279 (fp #b0 #b01111110 #b00100011110101110000101))))
.def_280))))))))))))))))
(check-sat)
