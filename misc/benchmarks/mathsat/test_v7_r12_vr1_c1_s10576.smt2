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
(assert (let ((.def_79 (fp.mul RNE x6 (fp #b1 #b01111010 #b11000010100011110101110))))
(let ((.def_74 (fp.mul RNE x5 (fp #b1 #b01111001 #b10111010010111100011011))))
(let ((.def_69 (fp.mul RNE x4 (fp #b1 #b01111110 #b01000000000000000000000))))
(let ((.def_64 (fp.mul RNE x3 (fp #b0 #b01111011 #b01011100001010001111011))))
(let ((.def_60 (fp.mul RNE x2 (fp #b0 #b01111101 #b01101111100111011011001))))
(let ((.def_56 (fp.mul RNE x1 (fp #b1 #b01111110 #b01010100111111011111010))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111101 #b10110111010010111100011))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_57 (fp.add RNE .def_52 .def_56)))
(let ((.def_61 (fp.add RNE .def_57 .def_60)))
(let ((.def_65 (fp.add RNE .def_61 .def_64)))
(let ((.def_70 (fp.add RNE .def_65 .def_69)))
(let ((.def_75 (fp.add RNE .def_70 .def_74)))
(let ((.def_80 (fp.add RNE .def_75 .def_79)))
(let ((.def_81 (fp.leq (fp #b1 #b01111101 #b10101101000011100101011) .def_80)))
.def_81))))))))))))))))
(assert (let ((.def_115 (fp.mul RNE x6 (fp #b1 #b01111010 #b11101011100001010001111))))
(let ((.def_110 (fp.mul RNE x5 (fp #b1 #b01111100 #b10011011101001011110010))))
(let ((.def_105 (fp.mul RNE x4 (fp #b0 #b01111110 #b00100010110100001110011))))
(let ((.def_101 (fp.mul RNE x3 (fp #b1 #b01111101 #b10010001011010000111001))))
(let ((.def_96 (fp.mul RNE x2 (fp #b1 #b01111100 #b00110011001100110011010))))
(let ((.def_91 (fp.mul RNE x1 (fp #b0 #b01111101 #b10001001001101110100110))))
(let ((.def_87 (fp.mul RNE x0 (fp #b1 #b01111110 #b10100111011011001000110))))
(let ((.def_88 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_87)))
(let ((.def_92 (fp.add RNE .def_88 .def_91)))
(let ((.def_97 (fp.add RNE .def_92 .def_96)))
(let ((.def_102 (fp.add RNE .def_97 .def_101)))
(let ((.def_106 (fp.add RNE .def_102 .def_105)))
(let ((.def_111 (fp.add RNE .def_106 .def_110)))
(let ((.def_116 (fp.add RNE .def_111 .def_115)))
(let ((.def_117 (fp.leq .def_116 (fp #b0 #b01111101 #b11100111011011001000110))))
.def_117))))))))))))))))
(assert (let ((.def_150 (fp.mul RNE x6 (fp #b0 #b01111101 #b10111110011101101100100))))
(let ((.def_146 (fp.mul RNE x5 (fp #b1 #b01111101 #b01110011101101100100011))))
(let ((.def_141 (fp.mul RNE x4 (fp #b1 #b01110111 #b00000110001001001101111))))
(let ((.def_136 (fp.mul RNE x3 (fp #b0 #b01111110 #b11001110010101100000010))))
(let ((.def_132 (fp.mul RNE x2 (fp #b1 #b01111101 #b01100111011011001000110))))
(let ((.def_127 (fp.mul RNE x1 (fp #b0 #b01111101 #b01101110100101111000111))))
(let ((.def_123 (fp.mul RNE x0 (fp #b0 #b01111101 #b10111011011001000101101))))
(let ((.def_124 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_123)))
(let ((.def_128 (fp.add RNE .def_124 .def_127)))
(let ((.def_133 (fp.add RNE .def_128 .def_132)))
(let ((.def_137 (fp.add RNE .def_133 .def_136)))
(let ((.def_142 (fp.add RNE .def_137 .def_141)))
(let ((.def_147 (fp.add RNE .def_142 .def_146)))
(let ((.def_151 (fp.add RNE .def_147 .def_150)))
(let ((.def_152 (fp.leq (fp #b1 #b01111110 #b10110011001100110011010) .def_151)))
.def_152))))))))))))))))
(assert (let ((.def_186 (fp.mul RNE x6 (fp #b1 #b01110110 #b00000110001001001101111))))
(let ((.def_181 (fp.mul RNE x5 (fp #b1 #b01111100 #b11000000100000110001001))))
(let ((.def_176 (fp.mul RNE x4 (fp #b1 #b01111110 #b00100010110100001110011))))
(let ((.def_173 (fp.mul RNE x3 (fp #b1 #b01111110 #b11111011111001110110110))))
(let ((.def_168 (fp.mul RNE x2 (fp #b1 #b01111101 #b11000000100000110001001))))
(let ((.def_163 (fp.mul RNE x1 (fp #b0 #b01111101 #b10110001001001101110101))))
(let ((.def_159 (fp.mul RNE x0 (fp #b1 #b01111100 #b11111001110110110010001))))
(let ((.def_160 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_159)))
(let ((.def_164 (fp.add RNE .def_160 .def_163)))
(let ((.def_169 (fp.add RNE .def_164 .def_168)))
(let ((.def_174 (fp.add RNE .def_169 .def_173)))
(let ((.def_177 (fp.add RNE .def_174 .def_176)))
(let ((.def_182 (fp.add RNE .def_177 .def_181)))
(let ((.def_187 (fp.add RNE .def_182 .def_186)))
(let ((.def_188 (fp.leq (fp #b1 #b01111110 #b01011110001101010100000) .def_187)))
.def_188))))))))))))))))
(assert (let ((.def_221 (fp.mul RNE x6 (fp #b0 #b01111101 #b01011111001110110110010))))
(let ((.def_217 (fp.mul RNE x5 (fp #b1 #b01111011 #b01110100101111000110101))))
(let ((.def_212 (fp.mul RNE x4 (fp #b1 #b01111110 #b01100011110101110000101))))
(let ((.def_207 (fp.mul RNE x3 (fp #b1 #b01111110 #b10011001000101101000100))))
(let ((.def_202 (fp.mul RNE x2 (fp #b1 #b01111100 #b01010001111010111000011))))
(let ((.def_197 (fp.mul RNE x1 (fp #b0 #b01111110 #b10000111001010110000001))))
(let ((.def_193 (fp.mul RNE x0 (fp #b0 #b01111011 #b11101011100001010001111))))
(let ((.def_194 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_193)))
(let ((.def_198 (fp.add RNE .def_194 .def_197)))
(let ((.def_203 (fp.add RNE .def_198 .def_202)))
(let ((.def_208 (fp.add RNE .def_203 .def_207)))
(let ((.def_213 (fp.add RNE .def_208 .def_212)))
(let ((.def_218 (fp.add RNE .def_213 .def_217)))
(let ((.def_222 (fp.add RNE .def_218 .def_221)))
(let ((.def_223 (fp.leq .def_222 (fp #b0 #b01111101 #b11000101101000011100101))))
.def_223))))))))))))))))
(assert (let ((.def_254 (fp.mul RNE x6 (fp #b0 #b01111011 #b11001010110000001000010))))
(let ((.def_250 (fp.mul RNE x5 (fp #b1 #b01111110 #b00111100011010100111111))))
(let ((.def_245 (fp.mul RNE x4 (fp #b0 #b01111110 #b01110000101000111101100))))
(let ((.def_241 (fp.mul RNE x3 (fp #b0 #b01111110 #b00001010110000001000010))))
(let ((.def_237 (fp.mul RNE x2 (fp #b0 #b01111101 #b00000000000000000000000))))
(let ((.def_233 (fp.mul RNE x1 (fp #b0 #b01111110 #b01111011011001000101101))))
(let ((.def_229 (fp.mul RNE x0 (fp #b1 #b01111101 #b10100100110111010011000))))
(let ((.def_230 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_229)))
(let ((.def_234 (fp.add RNE .def_230 .def_233)))
(let ((.def_238 (fp.add RNE .def_234 .def_237)))
(let ((.def_242 (fp.add RNE .def_238 .def_241)))
(let ((.def_246 (fp.add RNE .def_242 .def_245)))
(let ((.def_251 (fp.add RNE .def_246 .def_250)))
(let ((.def_255 (fp.add RNE .def_251 .def_254)))
(let ((.def_256 (fp.leq .def_255 (fp #b0 #b01111110 #b01000101101000011100101))))
.def_256))))))))))))))))
(assert (let ((.def_290 (fp.mul RNE x6 (fp #b1 #b01111110 #b01011000000100000110001))))
(let ((.def_285 (fp.mul RNE x5 (fp #b1 #b01111110 #b00000111101011100001010))))
(let ((.def_280 (fp.mul RNE x4 (fp #b0 #b01111110 #b00001101110100101111001))))
(let ((.def_276 (fp.mul RNE x3 (fp #b0 #b01111110 #b00001100110011001100110))))
(let ((.def_272 (fp.mul RNE x2 (fp #b1 #b01111101 #b10011000100100110111010))))
(let ((.def_267 (fp.mul RNE x1 (fp #b1 #b01111101 #b11100000010000011000101))))
(let ((.def_262 (fp.mul RNE x0 (fp #b1 #b01111100 #b01001011110001101010100))))
(let ((.def_263 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_262)))
(let ((.def_268 (fp.add RNE .def_263 .def_267)))
(let ((.def_273 (fp.add RNE .def_268 .def_272)))
(let ((.def_277 (fp.add RNE .def_273 .def_276)))
(let ((.def_281 (fp.add RNE .def_277 .def_280)))
(let ((.def_286 (fp.add RNE .def_281 .def_285)))
(let ((.def_291 (fp.add RNE .def_286 .def_290)))
(let ((.def_292 (fp.leq (fp #b0 #b01111110 #b00000001100010010011100) .def_291)))
.def_292))))))))))))))))
(assert (let ((.def_322 (fp.mul RNE x6 (fp #b0 #b01111101 #b00100010110100001110011))))
(let ((.def_318 (fp.mul RNE x5 (fp #b0 #b01111010 #b10100001110010101100000))))
(let ((.def_314 (fp.mul RNE x4 (fp #b0 #b01111110 #b10000110001001001101111))))
(let ((.def_310 (fp.mul RNE x3 (fp #b0 #b01111001 #b01000111101011100001010))))
(let ((.def_306 (fp.mul RNE x2 (fp #b1 #b01111110 #b10001000101101000011101))))
(let ((.def_301 (fp.mul RNE x1 (fp #b0 #b01111100 #b01000111101011100001010))))
(let ((.def_297 (fp.mul RNE x0 (fp #b0 #b01111110 #b10010111100011010101000))))
(let ((.def_298 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_297)))
(let ((.def_302 (fp.add RNE .def_298 .def_301)))
(let ((.def_307 (fp.add RNE .def_302 .def_306)))
(let ((.def_311 (fp.add RNE .def_307 .def_310)))
(let ((.def_315 (fp.add RNE .def_311 .def_314)))
(let ((.def_319 (fp.add RNE .def_315 .def_318)))
(let ((.def_323 (fp.add RNE .def_319 .def_322)))
(let ((.def_324 (fp.leq (fp #b0 #b01111100 #b00111011011001000101101) .def_323)))
.def_324))))))))))))))))
(assert (let ((.def_359 (fp.mul RNE x6 (fp #b1 #b01111110 #b00010111100011010101000))))
(let ((.def_354 (fp.mul RNE x5 (fp #b1 #b01111101 #b00110011001100110011010))))
(let ((.def_349 (fp.mul RNE x4 (fp #b0 #b01111100 #b01011000000100000110001))))
(let ((.def_345 (fp.mul RNE x3 (fp #b1 #b01111101 #b10111111011111001110111))))
(let ((.def_340 (fp.mul RNE x2 (fp #b1 #b01111110 #b11101000011100101011000))))
(let ((.def_335 (fp.mul RNE x1 (fp #b1 #b01111001 #b11001010110000001000010))))
(let ((.def_330 (fp.mul RNE x0 (fp #b0 #b01111110 #b00100110011001100110011))))
(let ((.def_331 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_330)))
(let ((.def_336 (fp.add RNE .def_331 .def_335)))
(let ((.def_341 (fp.add RNE .def_336 .def_340)))
(let ((.def_346 (fp.add RNE .def_341 .def_345)))
(let ((.def_350 (fp.add RNE .def_346 .def_349)))
(let ((.def_355 (fp.add RNE .def_350 .def_354)))
(let ((.def_360 (fp.add RNE .def_355 .def_359)))
(let ((.def_361 (fp.leq .def_360 (fp #b1 #b01111110 #b00101000011100101011000))))
.def_361))))))))))))))))
(assert (let ((.def_395 (fp.mul RNE x6 (fp #b0 #b01111110 #b00111110011101101100100))))
(let ((.def_391 (fp.mul RNE x5 (fp #b1 #b01111100 #b11010111000010100011111))))
(let ((.def_386 (fp.mul RNE x4 (fp #b1 #b01111110 #b00110011101101100100011))))
(let ((.def_381 (fp.mul RNE x3 (fp #b0 #b01111100 #b10000001000001100010010))))
(let ((.def_377 (fp.mul RNE x2 (fp #b1 #b01111101 #b00010000011000100100111))))
(let ((.def_372 (fp.mul RNE x1 (fp #b1 #b01111101 #b10101111000110101010000))))
(let ((.def_367 (fp.mul RNE x0 (fp #b1 #b01111101 #b00101110000101000111101))))
(let ((.def_368 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_367)))
(let ((.def_373 (fp.add RNE .def_368 .def_372)))
(let ((.def_378 (fp.add RNE .def_373 .def_377)))
(let ((.def_382 (fp.add RNE .def_378 .def_381)))
(let ((.def_387 (fp.add RNE .def_382 .def_386)))
(let ((.def_392 (fp.add RNE .def_387 .def_391)))
(let ((.def_396 (fp.add RNE .def_392 .def_395)))
(let ((.def_397 (fp.leq (fp #b0 #b01111110 #b01010111100011010101000) .def_396)))
.def_397))))))))))))))))
(assert (let ((.def_424 (fp.mul RNE x6 (fp #b1 #b01111110 #b01010100011110101110001))))
(let ((.def_419 (fp.mul RNE x5 (fp #b0 #b01111101 #b11011110001101010100000))))
(let ((.def_414 (fp.mul RNE x3 (fp #b0 #b01111110 #b01101001011110001101010))))
(let ((.def_410 (fp.mul RNE x2 (fp #b0 #b01111101 #b01100000010000011000101))))
(let ((.def_406 (fp.mul RNE x1 (fp #b1 #b01111110 #b01100001110010101100000))))
(let ((.def_401 (fp.mul RNE x0 (fp #b1 #b01111110 #b11101010011111101111101))))
(let ((.def_402 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_401)))
(let ((.def_407 (fp.add RNE .def_402 .def_406)))
(let ((.def_411 (fp.add RNE .def_407 .def_410)))
(let ((.def_415 (fp.add RNE .def_411 .def_414)))
(let ((.def_349 (fp.mul RNE x4 (fp #b0 #b01111100 #b01011000000100000110001))))
(let ((.def_416 (fp.add RNE .def_349 .def_415)))
(let ((.def_420 (fp.add RNE .def_416 .def_419)))
(let ((.def_425 (fp.add RNE .def_420 .def_424)))
(let ((.def_426 (fp.leq (fp #b0 #b01111110 #b01000000000000000000000) .def_425)))
.def_426))))))))))))))))
(assert (let ((.def_455 (fp.mul RNE x6 (fp #b0 #b01111110 #b01111000010100011110110))))
(let ((.def_451 (fp.mul RNE x5 (fp #b0 #b01111101 #b00000001000001100010010))))
(let ((.def_449 (fp.mul RNE x4 (fp #b1 #b01111011 #b00011010100111111011111))))
(let ((.def_444 (fp.mul RNE x3 (fp #b1 #b01111101 #b00000001000001100010010))))
(let ((.def_439 (fp.mul RNE x2 (fp #b0 #b01111100 #b00001110010101100000010))))
(let ((.def_435 (fp.mul RNE x1 (fp #b0 #b01111110 #b01100100110111010011000))))
(let ((.def_431 (fp.mul RNE x0 (fp #b0 #b01111101 #b11111101111100111011011))))
(let ((.def_432 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_431)))
(let ((.def_436 (fp.add RNE .def_432 .def_435)))
(let ((.def_440 (fp.add RNE .def_436 .def_439)))
(let ((.def_445 (fp.add RNE .def_440 .def_444)))
(let ((.def_450 (fp.add RNE .def_445 .def_449)))
(let ((.def_452 (fp.add RNE .def_450 .def_451)))
(let ((.def_456 (fp.add RNE .def_452 .def_455)))
(let ((.def_457 (fp.leq (fp #b0 #b01111110 #b10101110100101111000111) .def_456)))
.def_457))))))))))))))))
(check-sat)