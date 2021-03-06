(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(declare-fun x4 () (_ FloatingPoint 8 24))
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
(assert (let ((.def_61 (fp.mul RNE x4 (fp #b0 #b01111101 #b11010010111100011010101))))
(let ((.def_57 (fp.mul RNE x3 (fp #b1 #b01111100 #b01001111110111110011110))))
(let ((.def_52 (fp.mul RNE x2 (fp #b1 #b01111011 #b00001010001111010111000))))
(let ((.def_47 (fp.mul RNE x1 (fp #b0 #b01111110 #b10100001010001111010111))))
(let ((.def_43 (fp.mul RNE x0 (fp #b0 #b01111001 #b01000111101011100001010))))
(let ((.def_44 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_43)))
(let ((.def_48 (fp.add RNE .def_44 .def_47)))
(let ((.def_53 (fp.add RNE .def_48 .def_52)))
(let ((.def_58 (fp.add RNE .def_53 .def_57)))
(let ((.def_62 (fp.add RNE .def_58 .def_61)))
(let ((.def_63 (fp.leq .def_62 (fp #b1 #b01111100 #b11100101011000000100001))))
.def_63))))))))))))
(assert (let ((.def_86 (fp.mul RNE x4 (fp #b0 #b01111110 #b10000110101001111111000))))
(let ((.def_82 (fp.mul RNE x3 (fp #b0 #b01111110 #b11001111010111000010100))))
(let ((.def_78 (fp.mul RNE x2 (fp #b1 #b01111110 #b10000101101000011100101))))
(let ((.def_73 (fp.mul RNE x1 (fp #b0 #b01111110 #b11110111110011101101101))))
(let ((.def_69 (fp.mul RNE x0 (fp #b0 #b01111110 #b01100101111000110101010))))
(let ((.def_70 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_69)))
(let ((.def_74 (fp.add RNE .def_70 .def_73)))
(let ((.def_79 (fp.add RNE .def_74 .def_78)))
(let ((.def_83 (fp.add RNE .def_79 .def_82)))
(let ((.def_87 (fp.add RNE .def_83 .def_86)))
(let ((.def_88 (fp.leq .def_87 (fp #b1 #b01111100 #b10000101000111101011100))))
.def_88))))))))))))
(assert (let ((.def_111 (fp.mul RNE x4 (fp #b1 #b01111110 #b11001110110110010001011))))
(let ((.def_106 (fp.mul RNE x3 (fp #b0 #b01111110 #b00011110101110000101001))))
(let ((.def_102 (fp.mul RNE x2 (fp #b1 #b01111001 #b01111000110101001111111))))
(let ((.def_97 (fp.mul RNE x1 (fp #b0 #b01111100 #b00011010100111111011111))))
(let ((.def_93 (fp.mul RNE x0 (fp #b0 #b01111110 #b00011000100100110111010))))
(let ((.def_94 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_93)))
(let ((.def_98 (fp.add RNE .def_94 .def_97)))
(let ((.def_103 (fp.add RNE .def_98 .def_102)))
(let ((.def_107 (fp.add RNE .def_103 .def_106)))
(let ((.def_112 (fp.add RNE .def_107 .def_111)))
(let ((.def_113 (fp.leq (fp #b0 #b01111110 #b00101100100010110100010) .def_112)))
.def_113))))))))))))
(assert (let ((.def_137 (fp.mul RNE x4 (fp #b0 #b01111100 #b11110111110011101101101))))
(let ((.def_133 (fp.mul RNE x3 (fp #b1 #b01111110 #b11011001000101101000100))))
(let ((.def_128 (fp.mul RNE x2 (fp #b1 #b01111100 #b10000011000100100110111))))
(let ((.def_123 (fp.mul RNE x1 (fp #b0 #b01111110 #b10101000111101011100001))))
(let ((.def_119 (fp.mul RNE x0 (fp #b1 #b01111100 #b10111000010100011110110))))
(let ((.def_120 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_119)))
(let ((.def_124 (fp.add RNE .def_120 .def_123)))
(let ((.def_129 (fp.add RNE .def_124 .def_128)))
(let ((.def_134 (fp.add RNE .def_129 .def_133)))
(let ((.def_138 (fp.add RNE .def_134 .def_137)))
(let ((.def_139 (fp.leq .def_138 (fp #b0 #b01111100 #b00001100010010011011101))))
.def_139))))))))))))
(assert (let ((.def_163 (fp.mul RNE x4 (fp #b0 #b01111110 #b01100111111011111001111))))
(let ((.def_159 (fp.mul RNE x3 (fp #b0 #b01111001 #b10011001100110011001101))))
(let ((.def_155 (fp.mul RNE x2 (fp #b1 #b01111110 #b00100000010000011000101))))
(let ((.def_150 (fp.mul RNE x1 (fp #b1 #b01111010 #b10011001100110011001101))))
(let ((.def_145 (fp.mul RNE x0 (fp #b1 #b01111100 #b00100000110001001001110))))
(let ((.def_146 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_145)))
(let ((.def_151 (fp.add RNE .def_146 .def_150)))
(let ((.def_156 (fp.add RNE .def_151 .def_155)))
(let ((.def_160 (fp.add RNE .def_156 .def_159)))
(let ((.def_164 (fp.add RNE .def_160 .def_163)))
(let ((.def_165 (fp.leq .def_164 (fp #b0 #b01111110 #b11111110011101101100100))))
.def_165))))))))))))
(assert (let ((.def_188 (fp.mul RNE x4 (fp #b0 #b01111110 #b00011001000101101000100))))
(let ((.def_184 (fp.mul RNE x3 (fp #b1 #b01111110 #b00110010001011010000111))))
(let ((.def_179 (fp.mul RNE x2 (fp #b1 #b01111110 #b00010001011010000111001))))
(let ((.def_174 (fp.mul RNE x1 (fp #b0 #b01111110 #b10001111110111110011110))))
(let ((.def_170 (fp.mul RNE x0 (fp #b0 #b01111011 #b01001111110111110011110))))
(let ((.def_171 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_170)))
(let ((.def_175 (fp.add RNE .def_171 .def_174)))
(let ((.def_180 (fp.add RNE .def_175 .def_179)))
(let ((.def_185 (fp.add RNE .def_180 .def_184)))
(let ((.def_189 (fp.add RNE .def_185 .def_188)))
(let ((.def_190 (fp.leq (fp #b0 #b01111110 #b01101111100111011011001) .def_189)))
.def_190))))))))))))
(assert (let ((.def_211 (fp.mul RNE x4 (fp #b1 #b01111110 #b11100100110111010011000))))
(let ((.def_209 (fp.mul RNE x3 (fp #b1 #b01111110 #b11100100110111010011000))))
(let ((.def_204 (fp.mul RNE x2 (fp #b0 #b01111110 #b10111011111001110110110))))
(let ((.def_200 (fp.mul RNE x1 (fp #b1 #b01111100 #b01101000011100101011000))))
(let ((.def_195 (fp.mul RNE x0 (fp #b0 #b01111101 #b10111101011100001010010))))
(let ((.def_196 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_195)))
(let ((.def_201 (fp.add RNE .def_196 .def_200)))
(let ((.def_205 (fp.add RNE .def_201 .def_204)))
(let ((.def_210 (fp.add RNE .def_205 .def_209)))
(let ((.def_212 (fp.add RNE .def_210 .def_211)))
(let ((.def_213 (fp.leq (fp #b0 #b01111110 #b00111010111000010100100) .def_212)))
.def_213))))))))))))
(assert (let ((.def_238 (fp.mul RNE x4 (fp #b1 #b01111110 #b11100110111010010111100))))
(let ((.def_233 (fp.mul RNE x3 (fp #b0 #b01111101 #b01110010101100000010000))))
(let ((.def_229 (fp.mul RNE x2 (fp #b1 #b01111110 #b00011101101100100010111))))
(let ((.def_224 (fp.mul RNE x1 (fp #b1 #b01111101 #b11010111000010100011111))))
(let ((.def_219 (fp.mul RNE x0 (fp #b1 #b01111110 #b00110111010010111100011))))
(let ((.def_220 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_219)))
(let ((.def_225 (fp.add RNE .def_220 .def_224)))
(let ((.def_230 (fp.add RNE .def_225 .def_229)))
(let ((.def_234 (fp.add RNE .def_230 .def_233)))
(let ((.def_239 (fp.add RNE .def_234 .def_238)))
(let ((.def_240 (fp.leq .def_239 (fp #b0 #b01111110 #b10001110110110010001011))))
.def_240))))))))))))
(assert (let ((.def_266 (fp.mul RNE x4 (fp #b1 #b01111100 #b10110000001000001100010))))
(let ((.def_261 (fp.mul RNE x3 (fp #b1 #b01111100 #b11110011101101100100011))))
(let ((.def_256 (fp.mul RNE x2 (fp #b1 #b01111100 #b11001000101101000011101))))
(let ((.def_251 (fp.mul RNE x1 (fp #b1 #b01111100 #b01111110111110011101110))))
(let ((.def_246 (fp.mul RNE x0 (fp #b0 #b01111110 #b01111011111001110110110))))
(let ((.def_247 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_246)))
(let ((.def_252 (fp.add RNE .def_247 .def_251)))
(let ((.def_257 (fp.add RNE .def_252 .def_256)))
(let ((.def_262 (fp.add RNE .def_257 .def_261)))
(let ((.def_267 (fp.add RNE .def_262 .def_266)))
(let ((.def_268 (fp.leq (fp #b1 #b01111110 #b10110110110010001011010) .def_267)))
.def_268))))))))))))
(assert (let ((.def_289 (fp.mul RNE x4 (fp #b0 #b01111101 #b11101011100001010001111))))
(let ((.def_285 (fp.mul RNE x3 (fp #b0 #b01111101 #b01011101001011110001101))))
(let ((.def_281 (fp.mul RNE x2 (fp #b1 #b01111110 #b11100110111010010111100))))
(let ((.def_279 (fp.mul RNE x1 (fp #b1 #b01111101 #b00001101010011111110000))))
(let ((.def_274 (fp.mul RNE x0 (fp #b0 #b01111101 #b00111010010111100011011))))
(let ((.def_275 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_274)))
(let ((.def_280 (fp.add RNE .def_275 .def_279)))
(let ((.def_282 (fp.add RNE .def_280 .def_281)))
(let ((.def_286 (fp.add RNE .def_282 .def_285)))
(let ((.def_290 (fp.add RNE .def_286 .def_289)))
(let ((.def_291 (fp.leq .def_290 (fp #b1 #b01111110 #b01011000000100000110001))))
.def_291))))))))))))
(assert (let ((.def_313 (fp.mul RNE x4 (fp #b1 #b01111110 #b10110000101000111101100))))
(let ((.def_308 (fp.mul RNE x3 (fp #b1 #b01111110 #b11000111101011100001010))))
(let ((.def_303 (fp.mul RNE x2 (fp #b1 #b01111101 #b01111101111100111011011))))
(let ((.def_298 (fp.mul RNE x1 (fp #b0 #b01111100 #b10000011000100100110111))))
(let ((.def_296 (fp.mul RNE x0 (fp #b0 #b01111100 #b00100110111010010111100))))
(let ((.def_297 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_296)))
(let ((.def_299 (fp.add RNE .def_297 .def_298)))
(let ((.def_304 (fp.add RNE .def_299 .def_303)))
(let ((.def_309 (fp.add RNE .def_304 .def_308)))
(let ((.def_314 (fp.add RNE .def_309 .def_313)))
(let ((.def_315 (fp.leq (fp #b0 #b01111100 #b10110100001110010101100) .def_314)))
.def_315))))))))))))
(assert (let ((.def_335 (fp.mul RNE x4 (fp #b1 #b01111110 #b01000100100110111010011))))
(let ((.def_330 (fp.mul RNE x3 (fp #b1 #b01111110 #b00001101110100101111001))))
(let ((.def_325 (fp.mul RNE x2 (fp #b1 #b01111110 #b11010001011010000111001))))
(let ((.def_320 (fp.mul RNE x1 (fp #b1 #b01111110 #b10110000101000111101100))))
(let ((.def_318 (fp.mul RNE x0 (fp #b0 #b01111100 #b01110010101100000010000))))
(let ((.def_319 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_318)))
(let ((.def_321 (fp.add RNE .def_319 .def_320)))
(let ((.def_326 (fp.add RNE .def_321 .def_325)))
(let ((.def_331 (fp.add RNE .def_326 .def_330)))
(let ((.def_336 (fp.add RNE .def_331 .def_335)))
(let ((.def_337 (fp.leq (fp #b0 #b01111110 #b01101111100111011011001) .def_336)))
.def_337))))))))))))
(assert (let ((.def_360 (fp.mul RNE x4 (fp #b1 #b01111101 #b10101111000110101010000))))
(let ((.def_355 (fp.mul RNE x3 (fp #b0 #b01111101 #b00101111000110101010000))))
(let ((.def_351 (fp.mul RNE x2 (fp #b0 #b01111110 #b01101100000010000011001))))
(let ((.def_347 (fp.mul RNE x1 (fp #b1 #b01111101 #b11001001101110100101111))))
(let ((.def_342 (fp.mul RNE x0 (fp #b0 #b01111101 #b11110111110011101101101))))
(let ((.def_343 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_342)))
(let ((.def_348 (fp.add RNE .def_343 .def_347)))
(let ((.def_352 (fp.add RNE .def_348 .def_351)))
(let ((.def_356 (fp.add RNE .def_352 .def_355)))
(let ((.def_361 (fp.add RNE .def_356 .def_360)))
(let ((.def_362 (fp.leq (fp #b0 #b01111100 #b00110111010010111100011) .def_361)))
.def_362))))))))))))
(assert (let ((.def_383 (fp.mul RNE x4 (fp #b0 #b01111101 #b01010111000010100011111))))
(let ((.def_379 (fp.mul RNE x3 (fp #b0 #b01111101 #b10010001011010000111001))))
(let ((.def_375 (fp.mul RNE x2 (fp #b1 #b01111110 #b00011000100100110111010))))
(let ((.def_372 (fp.mul RNE x1 (fp #b0 #b01111110 #b11001101010011111110000))))
(let ((.def_368 (fp.mul RNE x0 (fp #b0 #b01111110 #b00101011100001010001111))))
(let ((.def_369 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_368)))
(let ((.def_373 (fp.add RNE .def_369 .def_372)))
(let ((.def_376 (fp.add RNE .def_373 .def_375)))
(let ((.def_380 (fp.add RNE .def_376 .def_379)))
(let ((.def_384 (fp.add RNE .def_380 .def_383)))
(let ((.def_385 (fp.leq (fp #b1 #b01111101 #b00100101111000110101010) .def_384)))
.def_385))))))))))))
(assert (let ((.def_406 (fp.mul RNE x4 (fp #b0 #b01111001 #b11001010110000001000010))))
(let ((.def_402 (fp.mul RNE x3 (fp #b1 #b01111101 #b01100010010011011101001))))
(let ((.def_397 (fp.mul RNE x2 (fp #b0 #b01111101 #b11000010100011110101110))))
(let ((.def_393 (fp.mul RNE x1 (fp #b1 #b01111100 #b00110011001100110011010))))
(let ((.def_388 (fp.mul RNE x0 (fp #b0 #b01111100 #b00011010100111111011111))))
(let ((.def_389 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_388)))
(let ((.def_394 (fp.add RNE .def_389 .def_393)))
(let ((.def_398 (fp.add RNE .def_394 .def_397)))
(let ((.def_403 (fp.add RNE .def_398 .def_402)))
(let ((.def_407 (fp.add RNE .def_403 .def_406)))
(let ((.def_408 (fp.leq (fp #b0 #b01111110 #b00101000111101011100001) .def_407)))
.def_408))))))))))))
(check-sat)
