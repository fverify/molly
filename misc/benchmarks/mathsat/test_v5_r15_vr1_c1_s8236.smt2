(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(declare-fun x4 () (_ FloatingPoint 8 24))
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
(assert (let ((.def_63 (fp.mul RNE x4 (fp #b1 #b01111010 #b11110011101101100100011))))
(let ((.def_58 (fp.mul RNE x3 (fp #b1 #b01110111 #b11001010110000001000010))))
(let ((.def_53 (fp.mul RNE x2 (fp #b1 #b01111110 #b01001001001101110100110))))
(let ((.def_48 (fp.mul RNE x1 (fp #b1 #b01111110 #b00001010110000001000010))))
(let ((.def_43 (fp.mul RNE x0 (fp #b1 #b01111110 #b10011111101111100111011))))
(let ((.def_44 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_43)))
(let ((.def_49 (fp.add RNE .def_44 .def_48)))
(let ((.def_54 (fp.add RNE .def_49 .def_53)))
(let ((.def_59 (fp.add RNE .def_54 .def_58)))
(let ((.def_64 (fp.add RNE .def_59 .def_63)))
(let ((.def_65 (fp.leq .def_64 (fp #b0 #b01111110 #b00000011000100100110111))))
.def_65))))))))))))
(assert (let ((.def_89 (fp.mul RNE x4 (fp #b0 #b01111110 #b11100001010001111010111))))
(let ((.def_85 (fp.mul RNE x3 (fp #b1 #b01111110 #b00001100110011001100110))))
(let ((.def_80 (fp.mul RNE x2 (fp #b1 #b01111110 #b00000100100110111010011))))
(let ((.def_75 (fp.mul RNE x1 (fp #b1 #b01111101 #b11000000100000110001001))))
(let ((.def_70 (fp.mul RNE x0 (fp #b0 #b01111110 #b00110110010001011010001))))
(let ((.def_71 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_70)))
(let ((.def_76 (fp.add RNE .def_71 .def_75)))
(let ((.def_81 (fp.add RNE .def_76 .def_80)))
(let ((.def_86 (fp.add RNE .def_81 .def_85)))
(let ((.def_90 (fp.add RNE .def_86 .def_89)))
(let ((.def_91 (fp.leq (fp #b0 #b01111110 #b00001000001100010010011) .def_90)))
.def_91))))))))))))
(assert (let ((.def_114 (fp.mul RNE x4 (fp #b0 #b01111010 #b00000110001001001101111))))
(let ((.def_110 (fp.mul RNE x3 (fp #b0 #b01111011 #b11101011100001010001111))))
(let ((.def_106 (fp.mul RNE x2 (fp #b1 #b01111110 #b00100111111011111001111))))
(let ((.def_101 (fp.mul RNE x1 (fp #b0 #b01111110 #b01110001001001101110101))))
(let ((.def_97 (fp.mul RNE x0 (fp #b1 #b01111101 #b00000110001001001101111))))
(let ((.def_98 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_97)))
(let ((.def_102 (fp.add RNE .def_98 .def_101)))
(let ((.def_107 (fp.add RNE .def_102 .def_106)))
(let ((.def_111 (fp.add RNE .def_107 .def_110)))
(let ((.def_115 (fp.add RNE .def_111 .def_114)))
(let ((.def_116 (fp.leq .def_115 (fp #b0 #b01111110 #b01001111110111110011110))))
.def_116))))))))))))
(assert (let ((.def_140 (fp.mul RNE x4 (fp #b0 #b01111101 #b00000011000100100110111))))
(let ((.def_136 (fp.mul RNE x3 (fp #b0 #b01111101 #b11100010010011011101001))))
(let ((.def_132 (fp.mul RNE x2 (fp #b1 #b01111110 #b01000011000100100110111))))
(let ((.def_127 (fp.mul RNE x1 (fp #b1 #b01111110 #b10000110001001001101111))))
(let ((.def_122 (fp.mul RNE x0 (fp #b1 #b01111110 #b11011110101110000101001))))
(let ((.def_123 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_122)))
(let ((.def_128 (fp.add RNE .def_123 .def_127)))
(let ((.def_133 (fp.add RNE .def_128 .def_132)))
(let ((.def_137 (fp.add RNE .def_133 .def_136)))
(let ((.def_141 (fp.add RNE .def_137 .def_140)))
(let ((.def_142 (fp.leq (fp #b0 #b01111101 #b10000010000011000100101) .def_141)))
.def_142))))))))))))
(assert (let ((.def_164 (fp.mul RNE x4 (fp #b0 #b01111110 #b11110110110010001011010))))
(let ((.def_160 (fp.mul RNE x3 (fp #b0 #b01111110 #b00101110100101111000111))))
(let ((.def_156 (fp.mul RNE x2 (fp #b0 #b01111101 #b10010011011101001011110))))
(let ((.def_152 (fp.mul RNE x1 (fp #b0 #b01111110 #b11001011110001101010100))))
(let ((.def_148 (fp.mul RNE x0 (fp #b0 #b01111101 #b01111110111110011101110))))
(let ((.def_149 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_148)))
(let ((.def_153 (fp.add RNE .def_149 .def_152)))
(let ((.def_157 (fp.add RNE .def_153 .def_156)))
(let ((.def_161 (fp.add RNE .def_157 .def_160)))
(let ((.def_165 (fp.add RNE .def_161 .def_164)))
(let ((.def_166 (fp.leq .def_165 (fp #b1 #b01111100 #b01001001101110100101111))))
.def_166))))))))))))
(assert (let ((.def_190 (fp.mul RNE x4 (fp #b0 #b01111110 #b10100111011011001000110))))
(let ((.def_186 (fp.mul RNE x3 (fp #b1 #b01111101 #b11110101110000101001000))))
(let ((.def_181 (fp.mul RNE x2 (fp #b0 #b01111100 #b10001011010000111001011))))
(let ((.def_177 (fp.mul RNE x1 (fp #b1 #b01111110 #b00110001101010011111110))))
(let ((.def_172 (fp.mul RNE x0 (fp #b1 #b01111101 #b00101111000110101010000))))
(let ((.def_173 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_172)))
(let ((.def_178 (fp.add RNE .def_173 .def_177)))
(let ((.def_182 (fp.add RNE .def_178 .def_181)))
(let ((.def_187 (fp.add RNE .def_182 .def_186)))
(let ((.def_191 (fp.add RNE .def_187 .def_190)))
(let ((.def_192 (fp.leq (fp #b0 #b01111110 #b11010010111100011010101) .def_191)))
.def_192))))))))))))
(assert (let ((.def_217 (fp.mul RNE x4 (fp #b0 #b01111101 #b10010000011000100100111))))
(let ((.def_213 (fp.mul RNE x3 (fp #b0 #b01111101 #b11110111110011101101101))))
(let ((.def_209 (fp.mul RNE x2 (fp #b1 #b01111110 #b11010011011101001011110))))
(let ((.def_204 (fp.mul RNE x1 (fp #b1 #b01111100 #b11011101001011110001101))))
(let ((.def_199 (fp.mul RNE x0 (fp #b1 #b01111110 #b00101100000010000011001))))
(let ((.def_200 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_199)))
(let ((.def_205 (fp.add RNE .def_200 .def_204)))
(let ((.def_210 (fp.add RNE .def_205 .def_209)))
(let ((.def_214 (fp.add RNE .def_210 .def_213)))
(let ((.def_218 (fp.add RNE .def_214 .def_217)))
(let ((.def_219 (fp.leq (fp #b1 #b01111010 #b10001001001101110100110) .def_218)))
.def_219))))))))))))
(assert (let ((.def_240 (fp.mul RNE x4 (fp #b0 #b01111110 #b10101011000000100000110))))
(let ((.def_236 (fp.mul RNE x3 (fp #b0 #b01111110 #b00111101011100001010010))))
(let ((.def_232 (fp.mul RNE x2 (fp #b0 #b01111110 #b11010010111100011010101))))
(let ((.def_230 (fp.mul RNE x1 (fp #b1 #b01111110 #b10111010010111100011011))))
(let ((.def_225 (fp.mul RNE x0 (fp #b0 #b01111011 #b01111000110101001111111))))
(let ((.def_226 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_225)))
(let ((.def_231 (fp.add RNE .def_226 .def_230)))
(let ((.def_233 (fp.add RNE .def_231 .def_232)))
(let ((.def_237 (fp.add RNE .def_233 .def_236)))
(let ((.def_241 (fp.add RNE .def_237 .def_240)))
(let ((.def_242 (fp.leq (fp #b1 #b01111011 #b11001110110110010001011) .def_241)))
.def_242))))))))))))
(assert (let ((.def_265 (fp.mul RNE x4 (fp #b1 #b01111110 #b10011011101001011110010))))
(let ((.def_260 (fp.mul RNE x3 (fp #b0 #b01111110 #b01111110111110011101110))))
(let ((.def_256 (fp.mul RNE x2 (fp #b0 #b01111101 #b01001110110110010001011))))
(let ((.def_252 (fp.mul RNE x1 (fp #b0 #b01111110 #b10011111001110110110010))))
(let ((.def_248 (fp.mul RNE x0 (fp #b0 #b01111110 #b01100100010110100001110))))
(let ((.def_249 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_248)))
(let ((.def_253 (fp.add RNE .def_249 .def_252)))
(let ((.def_257 (fp.add RNE .def_253 .def_256)))
(let ((.def_261 (fp.add RNE .def_257 .def_260)))
(let ((.def_266 (fp.add RNE .def_261 .def_265)))
(let ((.def_267 (fp.leq (fp #b1 #b01111101 #b10011010100111111011111) .def_266)))
.def_267))))))))))))
(assert (let ((.def_290 (fp.mul RNE x4 (fp #b0 #b01111100 #b00101101000011100101011))))
(let ((.def_286 (fp.mul RNE x3 (fp #b0 #b01111011 #b11010010111100011010101))))
(let ((.def_282 (fp.mul RNE x2 (fp #b1 #b01111101 #b00010100011110101110001))))
(let ((.def_277 (fp.mul RNE x1 (fp #b1 #b01111110 #b00110011101101100100011))))
(let ((.def_272 (fp.mul RNE x0 (fp #b0 #b01111101 #b10011001100110011001101))))
(let ((.def_273 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_272)))
(let ((.def_278 (fp.add RNE .def_273 .def_277)))
(let ((.def_283 (fp.add RNE .def_278 .def_282)))
(let ((.def_287 (fp.add RNE .def_283 .def_286)))
(let ((.def_291 (fp.add RNE .def_287 .def_290)))
(let ((.def_292 (fp.leq (fp #b0 #b01111101 #b11111000110101001111111) .def_291)))
.def_292))))))))))))
(assert (let ((.def_317 (fp.mul RNE x4 (fp #b1 #b01110101 #b00000110001001001101111))))
(let ((.def_312 (fp.mul RNE x3 (fp #b0 #b01111101 #b00100000110001001001110))))
(let ((.def_308 (fp.mul RNE x2 (fp #b1 #b01111110 #b00111011111001110110110))))
(let ((.def_303 (fp.mul RNE x1 (fp #b1 #b01111110 #b01110000001000001100010))))
(let ((.def_298 (fp.mul RNE x0 (fp #b0 #b01111110 #b11000110001001001101111))))
(let ((.def_299 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_298)))
(let ((.def_304 (fp.add RNE .def_299 .def_303)))
(let ((.def_309 (fp.add RNE .def_304 .def_308)))
(let ((.def_313 (fp.add RNE .def_309 .def_312)))
(let ((.def_318 (fp.add RNE .def_313 .def_317)))
(let ((.def_319 (fp.leq .def_318 (fp #b1 #b01111110 #b01111010010111100011011))))
.def_319))))))))))))
(assert (let ((.def_341 (fp.mul RNE x4 (fp #b1 #b01111110 #b10010100111111011111010))))
(let ((.def_336 (fp.mul RNE x3 (fp #b1 #b01111000 #b01101000011100101011000))))
(let ((.def_331 (fp.mul RNE x2 (fp #b0 #b01111110 #b01111010010111100011011))))
(let ((.def_329 (fp.mul RNE x1 (fp #b0 #b01111000 #b11101011100001010001111))))
(let ((.def_325 (fp.mul RNE x0 (fp #b0 #b01111101 #b11111100111011011001001))))
(let ((.def_326 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_325)))
(let ((.def_330 (fp.add RNE .def_326 .def_329)))
(let ((.def_332 (fp.add RNE .def_330 .def_331)))
(let ((.def_337 (fp.add RNE .def_332 .def_336)))
(let ((.def_342 (fp.add RNE .def_337 .def_341)))
(let ((.def_343 (fp.leq (fp #b1 #b01111011 #b11001010110000001000010) .def_342)))
.def_343))))))))))))
(assert (let ((.def_364 (fp.mul RNE x4 (fp #b0 #b01111110 #b01001001001101110100110))))
(let ((.def_362 (fp.mul RNE x3 (fp #b0 #b01111101 #b10110101001111110111110))))
(let ((.def_358 (fp.mul RNE x2 (fp #b0 #b01111110 #b01010110100001110010110))))
(let ((.def_354 (fp.mul RNE x1 (fp #b1 #b01111110 #b01000001100010010011100))))
(let ((.def_349 (fp.mul RNE x0 (fp #b1 #b01111101 #b11001001101110100101111))))
(let ((.def_350 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_349)))
(let ((.def_355 (fp.add RNE .def_350 .def_354)))
(let ((.def_359 (fp.add RNE .def_355 .def_358)))
(let ((.def_363 (fp.add RNE .def_359 .def_362)))
(let ((.def_365 (fp.add RNE .def_363 .def_364)))
(let ((.def_366 (fp.leq (fp #b0 #b01111101 #b00000010000011000100101) .def_365)))
.def_366))))))))))))
(assert (let ((.def_388 (fp.mul RNE x4 (fp #b0 #b01111100 #b10010111100011010101000))))
(let ((.def_384 (fp.mul RNE x3 (fp #b0 #b01111101 #b01111000110101001111111))))
(let ((.def_380 (fp.mul RNE x2 (fp #b1 #b01111110 #b01011000000100000110001))))
(let ((.def_375 (fp.mul RNE x1 (fp #b0 #b01111110 #b00111001010110000001000))))
(let ((.def_371 (fp.mul RNE x0 (fp #b0 #b01111110 #b10000101000111101011100))))
(let ((.def_372 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_371)))
(let ((.def_376 (fp.add RNE .def_372 .def_375)))
(let ((.def_381 (fp.add RNE .def_376 .def_380)))
(let ((.def_385 (fp.add RNE .def_381 .def_384)))
(let ((.def_389 (fp.add RNE .def_385 .def_388)))
(let ((.def_390 (fp.leq .def_389 (fp #b0 #b01111110 #b10010110100001110010110))))
.def_390))))))))))))
(assert (let ((.def_413 (fp.mul RNE x4 (fp #b0 #b01111010 #b00111111011111001110111))))
(let ((.def_409 (fp.mul RNE x3 (fp #b1 #b01111100 #b10111010010111100011011))))
(let ((.def_404 (fp.mul RNE x2 (fp #b1 #b01111110 #b01001011010000111001011))))
(let ((.def_399 (fp.mul RNE x1 (fp #b0 #b01111101 #b01111000110101001111111))))
(let ((.def_397 (fp.mul RNE x0 (fp #b1 #b01111101 #b10011011101001011110010))))
(let ((.def_398 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_397)))
(let ((.def_400 (fp.add RNE .def_398 .def_399)))
(let ((.def_405 (fp.add RNE .def_400 .def_404)))
(let ((.def_410 (fp.add RNE .def_405 .def_409)))
(let ((.def_414 (fp.add RNE .def_410 .def_413)))
(let ((.def_415 (fp.leq .def_414 (fp #b1 #b01111101 #b11100001010001111010111))))
.def_415))))))))))))
(check-sat)
