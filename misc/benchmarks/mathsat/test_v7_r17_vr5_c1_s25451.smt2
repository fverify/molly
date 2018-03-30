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
(assert (let ((.def_77 (fp.mul RNE x6 (fp #b1 #b01111110 #b00011100001010001111011))))
(let ((.def_72 (fp.mul RNE x5 (fp #b1 #b01111100 #b00100100110111010011000))))
(let ((.def_67 (fp.mul RNE x4 (fp #b0 #b01111101 #b01110010101100000010000))))
(let ((.def_63 (fp.mul RNE x3 (fp #b0 #b01111100 #b11110101110000101001000))))
(let ((.def_59 (fp.mul RNE x2 (fp #b0 #b01111100 #b11101101100100010110100))))
(let ((.def_55 (fp.mul RNE x1 (fp #b0 #b01111110 #b00111100011010100111111))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111100 #b00000010000011000100101))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_56 (fp.add RNE .def_52 .def_55)))
(let ((.def_60 (fp.add RNE .def_56 .def_59)))
(let ((.def_64 (fp.add RNE .def_60 .def_63)))
(let ((.def_68 (fp.add RNE .def_64 .def_67)))
(let ((.def_73 (fp.add RNE .def_68 .def_72)))
(let ((.def_78 (fp.add RNE .def_73 .def_77)))
(let ((.def_79 (fp.leq (fp #b1 #b01111100 #b11011001000101101000100) .def_78)))
.def_79))))))))))))))))
(assert (let ((.def_109 (fp.mul RNE (fp #b0 #b00000000 #b00000000000000000000000) x6)))
(let ((.def_107 (fp.mul RNE x5 (fp #b1 #b01111100 #b11100001010001111010111))))
(let ((.def_102 (fp.mul RNE x4 (fp #b0 #b01111101 #b01111010111000010100100))))
(let ((.def_98 (fp.mul RNE x3 (fp #b0 #b01111011 #b10111010010111100011011))))
(let ((.def_94 (fp.mul RNE x2 (fp #b1 #b01111101 #b10000101000111101011100))))
(let ((.def_89 (fp.mul RNE x1 (fp #b1 #b01111110 #b01011001100110011001101))))
(let ((.def_84 (fp.mul RNE x0 (fp #b0 #b01111110 #b10001010110000001000010))))
(let ((.def_85 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_84)))
(let ((.def_90 (fp.add RNE .def_85 .def_89)))
(let ((.def_95 (fp.add RNE .def_90 .def_94)))
(let ((.def_99 (fp.add RNE .def_95 .def_98)))
(let ((.def_103 (fp.add RNE .def_99 .def_102)))
(let ((.def_108 (fp.add RNE .def_103 .def_107)))
(let ((.def_110 (fp.add RNE .def_108 .def_109)))
(let ((.def_111 (fp.leq .def_110 (fp #b0 #b01111101 #b01001101110100101111001))))
.def_111))))))))))))))))
(assert (let ((.def_140 (fp.mul RNE x6 (fp #b0 #b01111100 #b11100001010001111010111))))
(let ((.def_138 (fp.mul RNE x5 (fp #b0 #b01111010 #b10100001110010101100000))))
(let ((.def_134 (fp.mul RNE x4 (fp #b0 #b01111101 #b11001101110100101111001))))
(let ((.def_130 (fp.mul RNE x3 (fp #b1 #b01111101 #b00100000110001001001110))))
(let ((.def_125 (fp.mul RNE x2 (fp #b0 #b01111100 #b00111111011111001110111))))
(let ((.def_121 (fp.mul RNE x1 (fp #b0 #b01111110 #b00000110001001001101111))))
(let ((.def_117 (fp.mul RNE x0 (fp #b0 #b01111110 #b10010000011000100100111))))
(let ((.def_118 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_117)))
(let ((.def_122 (fp.add RNE .def_118 .def_121)))
(let ((.def_126 (fp.add RNE .def_122 .def_125)))
(let ((.def_131 (fp.add RNE .def_126 .def_130)))
(let ((.def_135 (fp.add RNE .def_131 .def_134)))
(let ((.def_139 (fp.add RNE .def_135 .def_138)))
(let ((.def_141 (fp.add RNE .def_139 .def_140)))
(let ((.def_142 (fp.leq (fp #b1 #b01111110 #b00100001110010101100000) .def_141)))
.def_142))))))))))))))))
(assert (let ((.def_173 (fp.mul RNE x6 (fp #b0 #b01111110 #b10000000100000110001001))))
(let ((.def_169 (fp.mul RNE x5 (fp #b1 #b01111101 #b01111011111001110110110))))
(let ((.def_164 (fp.mul RNE x4 (fp #b0 #b01111101 #b11011001000101101000100))))
(let ((.def_160 (fp.mul RNE x3 (fp #b0 #b01111010 #b11001010110000001000010))))
(let ((.def_158 (fp.mul RNE x2 (fp #b0 #b01111011 #b01101000011100101011000))))
(let ((.def_154 (fp.mul RNE x1 (fp #b1 #b01111101 #b11001011110001101010100))))
(let ((.def_149 (fp.mul RNE x0 (fp #b1 #b01111101 #b10010111100011010101000))))
(let ((.def_150 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_149)))
(let ((.def_155 (fp.add RNE .def_150 .def_154)))
(let ((.def_159 (fp.add RNE .def_155 .def_158)))
(let ((.def_161 (fp.add RNE .def_159 .def_160)))
(let ((.def_165 (fp.add RNE .def_161 .def_164)))
(let ((.def_170 (fp.add RNE .def_165 .def_169)))
(let ((.def_174 (fp.add RNE .def_170 .def_173)))
(let ((.def_175 (fp.leq (fp #b1 #b01111010 #b11001010110000001000010) .def_174)))
.def_175))))))))))))))))
(assert (let ((.def_208 (fp.mul RNE x6 (fp #b1 #b01111010 #b11101011100001010001111))))
(let ((.def_203 (fp.mul RNE x5 (fp #b1 #b01111110 #b11000000100000110001001))))
(let ((.def_198 (fp.mul RNE x4 (fp #b1 #b01111110 #b01110000101000111101100))))
(let ((.def_193 (fp.mul RNE x3 (fp #b1 #b01111110 #b10100101111000110101010))))
(let ((.def_188 (fp.mul RNE x2 (fp #b0 #b01111101 #b10010111100011010101000))))
(let ((.def_186 (fp.mul RNE x1 (fp #b1 #b01111101 #b01010111000010100011111))))
(let ((.def_181 (fp.mul RNE x0 (fp #b1 #b01111110 #b11101100000010000011001))))
(let ((.def_182 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_181)))
(let ((.def_187 (fp.add RNE .def_182 .def_186)))
(let ((.def_189 (fp.add RNE .def_187 .def_188)))
(let ((.def_194 (fp.add RNE .def_189 .def_193)))
(let ((.def_199 (fp.add RNE .def_194 .def_198)))
(let ((.def_204 (fp.add RNE .def_199 .def_203)))
(let ((.def_209 (fp.add RNE .def_204 .def_208)))
(let ((.def_210 (fp.leq .def_209 (fp #b0 #b01111110 #b10100100010110100001110))))
.def_210))))))))))))))))
(assert (let ((.def_240 (fp.mul RNE x6 (fp #b1 #b01111110 #b10100000110001001001110))))
(let ((.def_235 (fp.mul RNE x5 (fp #b1 #b01111011 #b10011001100110011001101))))
(let ((.def_230 (fp.mul RNE x4 (fp #b1 #b01111101 #b01111011111001110110110))))
(let ((.def_228 (fp.mul RNE x3 (fp #b1 #b01111100 #b11111011111001110110110))))
(let ((.def_225 (fp.mul RNE x2 (fp #b0 #b01111010 #b01111000110101001111111))))
(let ((.def_221 (fp.mul RNE x1 (fp #b1 #b01111110 #b11001111010111000010100))))
(let ((.def_216 (fp.mul RNE x0 (fp #b0 #b01111100 #b11111011111001110110110))))
(let ((.def_217 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_216)))
(let ((.def_222 (fp.add RNE .def_217 .def_221)))
(let ((.def_226 (fp.add RNE .def_222 .def_225)))
(let ((.def_229 (fp.add RNE .def_226 .def_228)))
(let ((.def_231 (fp.add RNE .def_229 .def_230)))
(let ((.def_236 (fp.add RNE .def_231 .def_235)))
(let ((.def_241 (fp.add RNE .def_236 .def_240)))
(let ((.def_242 (fp.leq .def_241 (fp #b1 #b01111101 #b11110101110000101001000))))
.def_242))))))))))))))))
(assert (let ((.def_275 (fp.mul RNE x6 (fp #b1 #b01111110 #b11000101101000011100101))))
(let ((.def_270 (fp.mul RNE x5 (fp #b0 #b01111011 #b01111100111011011001001))))
(let ((.def_266 (fp.mul RNE x4 (fp #b0 #b01111110 #b10111100011010100111111))))
(let ((.def_262 (fp.mul RNE x3 (fp #b1 #b01111110 #b00010011111101111100111))))
(let ((.def_257 (fp.mul RNE x2 (fp #b0 #b01111110 #b11100101111000110101010))))
(let ((.def_253 (fp.mul RNE x1 (fp #b1 #b01111101 #b01010110000001000001100))))
(let ((.def_248 (fp.mul RNE x0 (fp #b0 #b01111100 #b01100110011001100110011))))
(let ((.def_249 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_248)))
(let ((.def_254 (fp.add RNE .def_249 .def_253)))
(let ((.def_258 (fp.add RNE .def_254 .def_257)))
(let ((.def_263 (fp.add RNE .def_258 .def_262)))
(let ((.def_267 (fp.add RNE .def_263 .def_266)))
(let ((.def_271 (fp.add RNE .def_267 .def_270)))
(let ((.def_276 (fp.add RNE .def_271 .def_275)))
(let ((.def_277 (fp.leq .def_276 (fp #b1 #b01111101 #b10111010010111100011011))))
.def_277))))))))))))))))
(assert (let ((.def_309 (fp.mul RNE x6 (fp #b0 #b01111110 #b00101010011111101111101))))
(let ((.def_305 (fp.mul RNE x5 (fp #b0 #b01111101 #b00110001001001101110101))))
(let ((.def_301 (fp.mul RNE x4 (fp #b0 #b01111100 #b10100011110101110000101))))
(let ((.def_297 (fp.mul RNE x3 (fp #b1 #b01111110 #b01100010110100001110011))))
(let ((.def_292 (fp.mul RNE x2 (fp #b1 #b01111100 #b11110011101101100100011))))
(let ((.def_287 (fp.mul RNE x1 (fp #b0 #b01111101 #b11100110011001100110011))))
(let ((.def_283 (fp.mul RNE x0 (fp #b0 #b01111110 #b11101111000110101010000))))
(let ((.def_284 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_283)))
(let ((.def_288 (fp.add RNE .def_284 .def_287)))
(let ((.def_293 (fp.add RNE .def_288 .def_292)))
(let ((.def_298 (fp.add RNE .def_293 .def_297)))
(let ((.def_302 (fp.add RNE .def_298 .def_301)))
(let ((.def_306 (fp.add RNE .def_302 .def_305)))
(let ((.def_310 (fp.add RNE .def_306 .def_309)))
(let ((.def_311 (fp.leq (fp #b1 #b01111110 #b01110001101010011111110) .def_310)))
.def_311))))))))))))))))
(assert (let ((.def_338 (fp.mul RNE x6 (fp #b1 #b01111011 #b10101001111110111110100))))
(let ((.def_333 (fp.mul RNE x5 (fp #b1 #b01111110 #b11000011000100100110111))))
(let ((.def_328 (fp.mul RNE x4 (fp #b0 #b01111110 #b01110000101000111101100))))
(let ((.def_326 (fp.mul RNE x3 (fp #b1 #b01111101 #b11100110011001100110011))))
(let ((.def_323 (fp.mul RNE x2 (fp #b1 #b01111100 #b11100001010001111010111))))
(let ((.def_321 (fp.mul RNE x1 (fp #b0 #b01111101 #b10001011010000111001011))))
(let ((.def_317 (fp.mul RNE x0 (fp #b1 #b01111110 #b11101010011111101111101))))
(let ((.def_318 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_317)))
(let ((.def_322 (fp.add RNE .def_318 .def_321)))
(let ((.def_324 (fp.add RNE .def_322 .def_323)))
(let ((.def_327 (fp.add RNE .def_324 .def_326)))
(let ((.def_329 (fp.add RNE .def_327 .def_328)))
(let ((.def_334 (fp.add RNE .def_329 .def_333)))
(let ((.def_339 (fp.add RNE .def_334 .def_338)))
(let ((.def_340 (fp.leq (fp #b0 #b01111110 #b10001110110110010001011) .def_339)))
.def_340))))))))))))))))
(assert (let ((.def_370 (fp.mul RNE x6 (fp #b0 #b01111110 #b01000100000110001001010))))
(let ((.def_366 (fp.mul RNE x5 (fp #b0 #b01111110 #b00001111010111000010100))))
(let ((.def_362 (fp.mul RNE x4 (fp #b0 #b01111100 #b11011001000101101000100))))
(let ((.def_360 (fp.mul RNE x3 (fp #b0 #b01111101 #b10000110001001001101111))))
(let ((.def_356 (fp.mul RNE x2 (fp #b1 #b01111110 #b10001100010010011011101))))
(let ((.def_351 (fp.mul RNE x1 (fp #b1 #b01111110 #b01101011100001010001111))))
(let ((.def_346 (fp.mul RNE x0 (fp #b0 #b01111110 #b10010111000010100011111))))
(let ((.def_347 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_346)))
(let ((.def_352 (fp.add RNE .def_347 .def_351)))
(let ((.def_357 (fp.add RNE .def_352 .def_356)))
(let ((.def_361 (fp.add RNE .def_357 .def_360)))
(let ((.def_363 (fp.add RNE .def_361 .def_362)))
(let ((.def_367 (fp.add RNE .def_363 .def_366)))
(let ((.def_371 (fp.add RNE .def_367 .def_370)))
(let ((.def_372 (fp.leq (fp #b1 #b01111100 #b11011111001110110110010) .def_371)))
.def_372))))))))))))))))
(assert (let ((.def_406 (fp.mul RNE x6 (fp #b1 #b01111110 #b00010000011000100100111))))
(let ((.def_401 (fp.mul RNE x5 (fp #b1 #b01111110 #b11100011110101110000101))))
(let ((.def_396 (fp.mul RNE x4 (fp #b1 #b01111110 #b11111010111000010100100))))
(let ((.def_391 (fp.mul RNE x3 (fp #b0 #b01111001 #b11011011001000101101000))))
(let ((.def_387 (fp.mul RNE x2 (fp #b0 #b01111100 #b00000110001001001101111))))
(let ((.def_383 (fp.mul RNE x1 (fp #b1 #b01111110 #b11111001010110000001000))))
(let ((.def_378 (fp.mul RNE x0 (fp #b0 #b01111110 #b10001110010101100000010))))
(let ((.def_379 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_378)))
(let ((.def_384 (fp.add RNE .def_379 .def_383)))
(let ((.def_388 (fp.add RNE .def_384 .def_387)))
(let ((.def_392 (fp.add RNE .def_388 .def_391)))
(let ((.def_397 (fp.add RNE .def_392 .def_396)))
(let ((.def_402 (fp.add RNE .def_397 .def_401)))
(let ((.def_407 (fp.add RNE .def_402 .def_406)))
(let ((.def_408 (fp.leq (fp #b1 #b01111110 #b00110010101100000010000) .def_407)))
.def_408))))))))))))))))
(assert (let ((.def_437 (fp.mul RNE x6 (fp #b0 #b01111110 #b10001100010010011011101))))
(let ((.def_435 (fp.mul RNE x5 (fp #b1 #b01111110 #b11100010110100001110011))))
(let ((.def_430 (fp.mul RNE x4 (fp #b1 #b01111010 #b00111111011111001110111))))
(let ((.def_425 (fp.mul RNE x3 (fp #b0 #b01111110 #b10011000000100000110001))))
(let ((.def_421 (fp.mul RNE x2 (fp #b1 #b01111110 #b01110001101010011111110))))
(let ((.def_419 (fp.mul RNE x1 (fp #b0 #b01111101 #b00101000111101011100001))))
(let ((.def_415 (fp.mul RNE x0 (fp #b1 #b01111110 #b00110100001110010101100))))
(let ((.def_416 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_415)))
(let ((.def_420 (fp.add RNE .def_416 .def_419)))
(let ((.def_422 (fp.add RNE .def_420 .def_421)))
(let ((.def_426 (fp.add RNE .def_422 .def_425)))
(let ((.def_431 (fp.add RNE .def_426 .def_430)))
(let ((.def_436 (fp.add RNE .def_431 .def_435)))
(let ((.def_438 (fp.add RNE .def_436 .def_437)))
(let ((.def_439 (fp.leq .def_438 (fp #b1 #b01111110 #b10110011001100110011010))))
.def_439))))))))))))))))
(assert (let ((.def_467 (fp.mul RNE x6 (fp #b0 #b01111101 #b11100001010001111010111))))
(let ((.def_463 (fp.mul RNE x5 (fp #b1 #b01111110 #b00011101101100100010111))))
(let ((.def_457 (fp.mul RNE x3 (fp #b0 #b01111110 #b10111000110101001111111))))
(let ((.def_453 (fp.mul RNE x2 (fp #b1 #b01111110 #b11101000111101011100001))))
(let ((.def_448 (fp.mul RNE x1 (fp #b1 #b01111101 #b01111010111000010100100))))
(let ((.def_445 (fp.mul RNE x0 (fp #b1 #b01111101 #b01100110011001100110011))))
(let ((.def_446 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_445)))
(let ((.def_449 (fp.add RNE .def_446 .def_448)))
(let ((.def_454 (fp.add RNE .def_449 .def_453)))
(let ((.def_458 (fp.add RNE .def_454 .def_457)))
(let ((.def_328 (fp.mul RNE x4 (fp #b0 #b01111110 #b01110000101000111101100))))
(let ((.def_459 (fp.add RNE .def_328 .def_458)))
(let ((.def_464 (fp.add RNE .def_459 .def_463)))
(let ((.def_468 (fp.add RNE .def_464 .def_467)))
(let ((.def_469 (fp.leq .def_468 (fp #b0 #b01111110 #b10001111010111000010100))))
.def_469))))))))))))))))
(assert (let ((.def_501 (fp.mul RNE x6 (fp #b1 #b01111000 #b10001001001101110100110))))
(let ((.def_496 (fp.mul RNE x5 (fp #b0 #b01111101 #b10011000100100110111010))))
(let ((.def_492 (fp.mul RNE x4 (fp #b0 #b01111110 #b01000101101000011100101))))
(let ((.def_488 (fp.mul RNE x3 (fp #b1 #b01111101 #b00001010001111010111000))))
(let ((.def_483 (fp.mul RNE x2 (fp #b1 #b01110111 #b11001010110000001000010))))
(let ((.def_478 (fp.mul RNE x1 (fp #b0 #b01111100 #b10010101100000010000011))))
(let ((.def_474 (fp.mul RNE x0 (fp #b0 #b01111110 #b01110110010001011010001))))
(let ((.def_475 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_474)))
(let ((.def_479 (fp.add RNE .def_475 .def_478)))
(let ((.def_484 (fp.add RNE .def_479 .def_483)))
(let ((.def_489 (fp.add RNE .def_484 .def_488)))
(let ((.def_493 (fp.add RNE .def_489 .def_492)))
(let ((.def_497 (fp.add RNE .def_493 .def_496)))
(let ((.def_502 (fp.add RNE .def_497 .def_501)))
(let ((.def_503 (fp.leq (fp #b0 #b01111100 #b00011110101110000101001) .def_502)))
.def_503))))))))))))))))
(assert (let ((.def_533 (fp.mul RNE x6 (fp #b1 #b01111110 #b01100001010001111010111))))
(let ((.def_528 (fp.mul RNE x5 (fp #b0 #b01111101 #b00110100001110010101100))))
(let ((.def_524 (fp.mul RNE x4 (fp #b0 #b01111101 #b11111010111000010100100))))
(let ((.def_520 (fp.mul RNE x3 (fp #b0 #b01111110 #b00111101111100111011011))))
(let ((.def_516 (fp.mul RNE x2 (fp #b1 #b01111101 #b00001111010111000010100))))
(let ((.def_511 (fp.mul RNE x1 (fp #b1 #b01111101 #b00100000110001001001110))))
(let ((.def_509 (fp.mul RNE x0 (fp #b1 #b01111110 #b11110111110011101101101))))
(let ((.def_510 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_509)))
(let ((.def_512 (fp.add RNE .def_510 .def_511)))
(let ((.def_517 (fp.add RNE .def_512 .def_516)))
(let ((.def_521 (fp.add RNE .def_517 .def_520)))
(let ((.def_525 (fp.add RNE .def_521 .def_524)))
(let ((.def_529 (fp.add RNE .def_525 .def_528)))
(let ((.def_534 (fp.add RNE .def_529 .def_533)))
(let ((.def_535 (fp.leq (fp #b0 #b01111110 #b11011010100111111011111) .def_534)))
.def_535))))))))))))))))
(assert (let ((.def_567 (fp.mul RNE x6 (fp #b1 #b01111100 #b11111001110110110010001))))
(let ((.def_562 (fp.mul RNE x5 (fp #b0 #b01111100 #b10110000001000001100010))))
(let ((.def_558 (fp.mul RNE x4 (fp #b1 #b01111101 #b00101100000010000011001))))
(let ((.def_553 (fp.mul RNE x3 (fp #b1 #b01111110 #b10001011110001101010100))))
(let ((.def_548 (fp.mul RNE x2 (fp #b1 #b01111110 #b00011000100100110111010))))
(let ((.def_543 (fp.mul RNE x1 (fp #b1 #b01111110 #b00110001001001101110101))))
(let ((.def_538 (fp.mul RNE x0 (fp #b0 #b01111100 #b00100100110111010011000))))
(let ((.def_539 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_538)))
(let ((.def_544 (fp.add RNE .def_539 .def_543)))
(let ((.def_549 (fp.add RNE .def_544 .def_548)))
(let ((.def_554 (fp.add RNE .def_549 .def_553)))
(let ((.def_559 (fp.add RNE .def_554 .def_558)))
(let ((.def_563 (fp.add RNE .def_559 .def_562)))
(let ((.def_568 (fp.add RNE .def_563 .def_567)))
(let ((.def_569 (fp.leq (fp #b0 #b01111110 #b00101100100010110100010) .def_568)))
.def_569))))))))))))))))
(assert (let ((.def_602 (fp.mul RNE x6 (fp #b1 #b01111101 #b10001000001100010010011))))
(let ((.def_597 (fp.mul RNE x5 (fp #b1 #b01111101 #b00101011000000100000110))))
(let ((.def_592 (fp.mul RNE x4 (fp #b0 #b01111110 #b00010001011010000111001))))
(let ((.def_588 (fp.mul RNE x3 (fp #b1 #b01111100 #b00100110111010010111100))))
(let ((.def_583 (fp.mul RNE x2 (fp #b0 #b01111110 #b10100110111010010111100))))
(let ((.def_579 (fp.mul RNE x1 (fp #b0 #b01111110 #b10000110001001001101111))))
(let ((.def_575 (fp.mul RNE x0 (fp #b0 #b01111110 #b10010001111010111000011))))
(let ((.def_576 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_575)))
(let ((.def_580 (fp.add RNE .def_576 .def_579)))
(let ((.def_584 (fp.add RNE .def_580 .def_583)))
(let ((.def_589 (fp.add RNE .def_584 .def_588)))
(let ((.def_593 (fp.add RNE .def_589 .def_592)))
(let ((.def_598 (fp.add RNE .def_593 .def_597)))
(let ((.def_603 (fp.add RNE .def_598 .def_602)))
(let ((.def_604 (fp.leq (fp #b1 #b01111110 #b11011011101001011110010) .def_603)))
.def_604))))))))))))))))
(check-sat)
