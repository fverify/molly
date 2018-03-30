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
(assert (let ((.def_76 (fp.mul RNE x6 (fp #b0 #b01111010 #b00001110010101100000010))))
(let ((.def_72 (fp.mul RNE x5 (fp #b0 #b01111110 #b10010011011101001011110))))
(let ((.def_68 (fp.mul RNE x4 (fp #b1 #b01111100 #b01110000101000111101100))))
(let ((.def_63 (fp.mul RNE x3 (fp #b0 #b01111101 #b10011001100110011001101))))
(let ((.def_59 (fp.mul RNE x2 (fp #b0 #b01111110 #b00001010001111010111000))))
(let ((.def_55 (fp.mul RNE x1 (fp #b0 #b01111110 #b10010001011010000111001))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111110 #b11001011010000111001011))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_56 (fp.add RNE .def_52 .def_55)))
(let ((.def_60 (fp.add RNE .def_56 .def_59)))
(let ((.def_64 (fp.add RNE .def_60 .def_63)))
(let ((.def_69 (fp.add RNE .def_64 .def_68)))
(let ((.def_73 (fp.add RNE .def_69 .def_72)))
(let ((.def_77 (fp.add RNE .def_73 .def_76)))
(let ((.def_78 (fp.leq .def_77 (fp #b1 #b01111101 #b00101110000101000111101))))
.def_78))))))))))))))))
(assert (let ((.def_111 (fp.mul RNE x6 (fp #b0 #b01111101 #b01111100111011011001001))))
(let ((.def_107 (fp.mul RNE x5 (fp #b0 #b01111011 #b11001010110000001000010))))
(let ((.def_103 (fp.mul RNE x4 (fp #b1 #b01111110 #b11110001001001101110101))))
(let ((.def_98 (fp.mul RNE x3 (fp #b1 #b01111110 #b00110001001001101110101))))
(let ((.def_93 (fp.mul RNE x2 (fp #b0 #b01111101 #b01101011100001010001111))))
(let ((.def_89 (fp.mul RNE x1 (fp #b1 #b01111101 #b10111001010110000001000))))
(let ((.def_84 (fp.mul RNE x0 (fp #b1 #b01111110 #b00001100010010011011101))))
(let ((.def_85 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_84)))
(let ((.def_90 (fp.add RNE .def_85 .def_89)))
(let ((.def_94 (fp.add RNE .def_90 .def_93)))
(let ((.def_99 (fp.add RNE .def_94 .def_98)))
(let ((.def_104 (fp.add RNE .def_99 .def_103)))
(let ((.def_108 (fp.add RNE .def_104 .def_107)))
(let ((.def_112 (fp.add RNE .def_108 .def_111)))
(let ((.def_113 (fp.leq (fp #b0 #b01111101 #b10010101100000010000011) .def_112)))
.def_113))))))))))))))))
(assert (let ((.def_144 (fp.mul RNE x6 (fp #b0 #b01111101 #b01010100111111011111010))))
(let ((.def_140 (fp.mul RNE x5 (fp #b0 #b01111100 #b00001000001100010010011))))
(let ((.def_136 (fp.mul RNE x4 (fp #b1 #b01111110 #b01111010010111100011011))))
(let ((.def_131 (fp.mul RNE x3 (fp #b1 #b01111010 #b00111111011111001110111))))
(let ((.def_126 (fp.mul RNE x2 (fp #b0 #b01111101 #b00000000000000000000000))))
(let ((.def_122 (fp.mul RNE x1 (fp #b0 #b01111100 #b00011010100111111011111))))
(let ((.def_118 (fp.mul RNE x0 (fp #b0 #b01111110 #b00001111110111110011110))))
(let ((.def_119 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_118)))
(let ((.def_123 (fp.add RNE .def_119 .def_122)))
(let ((.def_127 (fp.add RNE .def_123 .def_126)))
(let ((.def_132 (fp.add RNE .def_127 .def_131)))
(let ((.def_137 (fp.add RNE .def_132 .def_136)))
(let ((.def_141 (fp.add RNE .def_137 .def_140)))
(let ((.def_145 (fp.add RNE .def_141 .def_144)))
(let ((.def_146 (fp.leq (fp #b0 #b01111110 #b01101001011110001101010) .def_145)))
.def_146))))))))))))))))
(assert (let ((.def_179 (fp.mul RNE x6 (fp #b1 #b01111101 #b01010010111100011010101))))
(let ((.def_174 (fp.mul RNE x5 (fp #b0 #b01111101 #b10110111010010111100011))))
(let ((.def_170 (fp.mul RNE x4 (fp #b1 #b01111101 #b00110100001110010101100))))
(let ((.def_165 (fp.mul RNE x3 (fp #b1 #b01111010 #b10001001001101110100110))))
(let ((.def_160 (fp.mul RNE x2 (fp #b1 #b01111110 #b10000101101000011100101))))
(let ((.def_155 (fp.mul RNE x1 (fp #b0 #b01111110 #b10100101111000110101010))))
(let ((.def_151 (fp.mul RNE x0 (fp #b0 #b01111101 #b00101100000010000011001))))
(let ((.def_152 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_151)))
(let ((.def_156 (fp.add RNE .def_152 .def_155)))
(let ((.def_161 (fp.add RNE .def_156 .def_160)))
(let ((.def_166 (fp.add RNE .def_161 .def_165)))
(let ((.def_171 (fp.add RNE .def_166 .def_170)))
(let ((.def_175 (fp.add RNE .def_171 .def_174)))
(let ((.def_180 (fp.add RNE .def_175 .def_179)))
(let ((.def_181 (fp.leq (fp #b0 #b01111110 #b10011011101001011110010) .def_180)))
.def_181))))))))))))))))
(assert (let ((.def_213 (fp.mul RNE x6 (fp #b1 #b01111100 #b10110100001110010101100))))
(let ((.def_208 (fp.mul RNE x5 (fp #b0 #b01111101 #b11100000010000011000101))))
(let ((.def_204 (fp.mul RNE x4 (fp #b0 #b01111011 #b00110111010010111100011))))
(let ((.def_200 (fp.mul RNE x3 (fp #b0 #b01111100 #b11100101011000000100001))))
(let ((.def_196 (fp.mul RNE x2 (fp #b0 #b01111110 #b10001010001111010111000))))
(let ((.def_192 (fp.mul RNE x1 (fp #b0 #b01111110 #b01000010000011000100101))))
(let ((.def_188 (fp.mul RNE x0 (fp #b1 #b01111101 #b00001110010101100000010))))
(let ((.def_189 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_188)))
(let ((.def_193 (fp.add RNE .def_189 .def_192)))
(let ((.def_197 (fp.add RNE .def_193 .def_196)))
(let ((.def_201 (fp.add RNE .def_197 .def_200)))
(let ((.def_205 (fp.add RNE .def_201 .def_204)))
(let ((.def_209 (fp.add RNE .def_205 .def_208)))
(let ((.def_214 (fp.add RNE .def_209 .def_213)))
(let ((.def_215 (fp.leq .def_214 (fp #b1 #b01111110 #b10001010110000001000010))))
.def_215))))))))))))))))
(assert (let ((.def_248 (fp.mul RNE x6 (fp #b0 #b01111011 #b11100011010100111111100))))
(let ((.def_244 (fp.mul RNE x5 (fp #b0 #b01110111 #b01000111101011100001010))))
(let ((.def_240 (fp.mul RNE x4 (fp #b0 #b01111110 #b01100011110101110000101))))
(let ((.def_236 (fp.mul RNE x3 (fp #b1 #b01111110 #b11111100111011011001001))))
(let ((.def_231 (fp.mul RNE x2 (fp #b1 #b01111110 #b11011011101001011110010))))
(let ((.def_226 (fp.mul RNE x1 (fp #b0 #b01111110 #b01010100111111011111010))))
(let ((.def_222 (fp.mul RNE x0 (fp #b1 #b01111110 #b11101000111101011100001))))
(let ((.def_223 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_222)))
(let ((.def_227 (fp.add RNE .def_223 .def_226)))
(let ((.def_232 (fp.add RNE .def_227 .def_231)))
(let ((.def_237 (fp.add RNE .def_232 .def_236)))
(let ((.def_241 (fp.add RNE .def_237 .def_240)))
(let ((.def_245 (fp.add RNE .def_241 .def_244)))
(let ((.def_249 (fp.add RNE .def_245 .def_248)))
(let ((.def_250 (fp.leq (fp #b1 #b01111100 #b00101111000110101010000) .def_249)))
.def_250))))))))))))))))
(assert (let ((.def_281 (fp.mul RNE x6 (fp #b1 #b01111101 #b11110011101101100100011))))
(let ((.def_276 (fp.mul RNE x5 (fp #b0 #b01111101 #b01001000101101000011101))))
(let ((.def_272 (fp.mul RNE x4 (fp #b1 #b01111110 #b00010001111010111000011))))
(let ((.def_267 (fp.mul RNE x3 (fp #b0 #b01111110 #b10101001011110001101010))))
(let ((.def_263 (fp.mul RNE x2 (fp #b0 #b01111110 #b01100110011001100110011))))
(let ((.def_259 (fp.mul RNE x1 (fp #b0 #b01111100 #b11111101111100111011011))))
(let ((.def_255 (fp.mul RNE x0 (fp #b0 #b01111100 #b10000101000111101011100))))
(let ((.def_256 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_255)))
(let ((.def_260 (fp.add RNE .def_256 .def_259)))
(let ((.def_264 (fp.add RNE .def_260 .def_263)))
(let ((.def_268 (fp.add RNE .def_264 .def_267)))
(let ((.def_273 (fp.add RNE .def_268 .def_272)))
(let ((.def_277 (fp.add RNE .def_273 .def_276)))
(let ((.def_282 (fp.add RNE .def_277 .def_281)))
(let ((.def_283 (fp.leq .def_282 (fp #b0 #b01111101 #b11110100101111000110101))))
.def_283))))))))))))))))
(assert (let ((.def_316 (fp.mul RNE x6 (fp #b0 #b01111101 #b01100001010001111010111))))
(let ((.def_312 (fp.mul RNE x5 (fp #b1 #b01111110 #b00001011110001101010100))))
(let ((.def_307 (fp.mul RNE x4 (fp #b0 #b01111110 #b11100000010000011000101))))
(let ((.def_303 (fp.mul RNE x3 (fp #b0 #b01111110 #b00110000101000111101100))))
(let ((.def_299 (fp.mul RNE x2 (fp #b0 #b01111110 #b01000010100011110101110))))
(let ((.def_295 (fp.mul RNE x1 (fp #b1 #b01111001 #b01000111101011100001010))))
(let ((.def_290 (fp.mul RNE x0 (fp #b1 #b01111100 #b10011101101100100010111))))
(let ((.def_291 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_290)))
(let ((.def_296 (fp.add RNE .def_291 .def_295)))
(let ((.def_300 (fp.add RNE .def_296 .def_299)))
(let ((.def_304 (fp.add RNE .def_300 .def_303)))
(let ((.def_308 (fp.add RNE .def_304 .def_307)))
(let ((.def_313 (fp.add RNE .def_308 .def_312)))
(let ((.def_317 (fp.add RNE .def_313 .def_316)))
(let ((.def_318 (fp.leq (fp #b1 #b01111011 #b00011110101110000101001) .def_317)))
.def_318))))))))))))))))
(assert (let ((.def_352 (fp.mul RNE x6 (fp #b1 #b01111101 #b00011000100100110111010))))
(let ((.def_347 (fp.mul RNE x5 (fp #b0 #b01111110 #b11001000101101000011101))))
(let ((.def_343 (fp.mul RNE x4 (fp #b1 #b01111110 #b00110111110011101101101))))
(let ((.def_338 (fp.mul RNE x3 (fp #b1 #b01111110 #b11010001011010000111001))))
(let ((.def_333 (fp.mul RNE x2 (fp #b1 #b01111100 #b00110111010010111100011))))
(let ((.def_328 (fp.mul RNE x1 (fp #b1 #b01111101 #b01101111100111011011001))))
(let ((.def_323 (fp.mul RNE x0 (fp #b0 #b01111100 #b01001011110001101010100))))
(let ((.def_324 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_323)))
(let ((.def_329 (fp.add RNE .def_324 .def_328)))
(let ((.def_334 (fp.add RNE .def_329 .def_333)))
(let ((.def_339 (fp.add RNE .def_334 .def_338)))
(let ((.def_344 (fp.add RNE .def_339 .def_343)))
(let ((.def_348 (fp.add RNE .def_344 .def_347)))
(let ((.def_353 (fp.add RNE .def_348 .def_352)))
(let ((.def_354 (fp.leq .def_353 (fp #b0 #b01111101 #b11100001010001111010111))))
.def_354))))))))))))))))
(assert (let ((.def_386 (fp.mul RNE x6 (fp #b0 #b01111110 #b00101100100010110100010))))
(let ((.def_382 (fp.mul RNE x5 (fp #b1 #b01111100 #b00011110101110000101001))))
(let ((.def_377 (fp.mul RNE x4 (fp #b0 #b01111101 #b11111110111110011101110))))
(let ((.def_373 (fp.mul RNE x3 (fp #b1 #b01111110 #b01001110110110010001011))))
(let ((.def_368 (fp.mul RNE x2 (fp #b0 #b01111110 #b10000100000110001001010))))
(let ((.def_364 (fp.mul RNE x1 (fp #b0 #b01111110 #b11001110010101100000010))))
(let ((.def_360 (fp.mul RNE x0 (fp #b0 #b01111101 #b01001001101110100101111))))
(let ((.def_361 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_360)))
(let ((.def_365 (fp.add RNE .def_361 .def_364)))
(let ((.def_369 (fp.add RNE .def_365 .def_368)))
(let ((.def_374 (fp.add RNE .def_369 .def_373)))
(let ((.def_378 (fp.add RNE .def_374 .def_377)))
(let ((.def_383 (fp.add RNE .def_378 .def_382)))
(let ((.def_387 (fp.add RNE .def_383 .def_386)))
(let ((.def_388 (fp.leq .def_387 (fp #b1 #b01111110 #b11000000000000000000000))))
.def_388))))))))))))))))
(assert (let ((.def_420 (fp.mul RNE x6 (fp #b1 #b01111011 #b11001110110110010001011))))
(let ((.def_415 (fp.mul RNE x5 (fp #b0 #b01111101 #b01010010111100011010101))))
(let ((.def_413 (fp.mul RNE x4 (fp #b0 #b01111101 #b10100000110001001001110))))
(let ((.def_409 (fp.mul RNE x3 (fp #b1 #b01111110 #b01100000010000011000101))))
(let ((.def_404 (fp.mul RNE x2 (fp #b1 #b01111110 #b10011000100100110111010))))
(let ((.def_399 (fp.mul RNE x1 (fp #b1 #b01111110 #b01000001000001100010010))))
(let ((.def_394 (fp.mul RNE x0 (fp #b1 #b01111110 #b01100100010110100001110))))
(let ((.def_395 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_394)))
(let ((.def_400 (fp.add RNE .def_395 .def_399)))
(let ((.def_405 (fp.add RNE .def_400 .def_404)))
(let ((.def_410 (fp.add RNE .def_405 .def_409)))
(let ((.def_414 (fp.add RNE .def_410 .def_413)))
(let ((.def_416 (fp.add RNE .def_414 .def_415)))
(let ((.def_421 (fp.add RNE .def_416 .def_420)))
(let ((.def_422 (fp.leq .def_421 (fp #b0 #b01111110 #b11110000101000111101100))))
.def_422))))))))))))))))
(assert (let ((.def_453 (fp.mul RNE x6 (fp #b1 #b01111110 #b00110011101101100100011))))
(let ((.def_448 (fp.mul RNE x5 (fp #b0 #b01111110 #b11010111000010100011111))))
(let ((.def_444 (fp.mul RNE x4 (fp #b1 #b01111011 #b00010110100001110010110))))
(let ((.def_439 (fp.mul RNE x3 (fp #b1 #b01111110 #b00100100110111010011000))))
(let ((.def_434 (fp.mul RNE x2 (fp #b0 #b01111101 #b11100000010000011000101))))
(let ((.def_432 (fp.mul RNE x1 (fp #b0 #b01111101 #b10001001001101110100110))))
(let ((.def_428 (fp.mul RNE x0 (fp #b1 #b01111110 #b10000101000111101011100))))
(let ((.def_429 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_428)))
(let ((.def_433 (fp.add RNE .def_429 .def_432)))
(let ((.def_435 (fp.add RNE .def_433 .def_434)))
(let ((.def_440 (fp.add RNE .def_435 .def_439)))
(let ((.def_445 (fp.add RNE .def_440 .def_444)))
(let ((.def_449 (fp.add RNE .def_445 .def_448)))
(let ((.def_454 (fp.add RNE .def_449 .def_453)))
(let ((.def_455 (fp.leq (fp #b0 #b01111010 #b01011000000100000110001) .def_454)))
.def_455))))))))))))))))
(check-sat)
