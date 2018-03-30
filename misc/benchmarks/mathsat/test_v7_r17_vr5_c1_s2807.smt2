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
(assert (let ((.def_78 (fp.mul RNE x6 (fp #b1 #b01111100 #b10100101111000110101010))))
(let ((.def_73 (fp.mul RNE x5 (fp #b1 #b01111110 #b11110110110010001011010))))
(let ((.def_68 (fp.mul RNE x4 (fp #b0 #b01111011 #b11110011101101100100011))))
(let ((.def_64 (fp.mul RNE x3 (fp #b1 #b01111101 #b11000010100011110101110))))
(let ((.def_59 (fp.mul RNE x2 (fp #b1 #b01111110 #b11001110110110010001011))))
(let ((.def_54 (fp.mul RNE x1 (fp #b0 #b01111100 #b01101110100101111000111))))
(let ((.def_50 (fp.mul RNE x0 (fp #b0 #b01111101 #b10010111100011010101000))))
(let ((.def_51 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_50)))
(let ((.def_55 (fp.add RNE .def_51 .def_54)))
(let ((.def_60 (fp.add RNE .def_55 .def_59)))
(let ((.def_65 (fp.add RNE .def_60 .def_64)))
(let ((.def_69 (fp.add RNE .def_65 .def_68)))
(let ((.def_74 (fp.add RNE .def_69 .def_73)))
(let ((.def_79 (fp.add RNE .def_74 .def_78)))
(let ((.def_80 (fp.leq .def_79 (fp #b0 #b01111011 #b10110010001011010000111))))
.def_80))))))))))))))))
(assert (let ((.def_113 (fp.mul RNE x6 (fp #b1 #b01111101 #b11100001010001111010111))))
(let ((.def_108 (fp.mul RNE x5 (fp #b0 #b01111110 #b01101111000110101010000))))
(let ((.def_104 (fp.mul RNE x4 (fp #b0 #b01111101 #b11011111001110110110010))))
(let ((.def_100 (fp.mul RNE x3 (fp #b1 #b01111110 #b10000101101000011100101))))
(let ((.def_95 (fp.mul RNE x2 (fp #b0 #b01111101 #b11000001100010010011100))))
(let ((.def_91 (fp.mul RNE x1 (fp #b1 #b01111011 #b00001010001111010111000))))
(let ((.def_86 (fp.mul RNE x0 (fp #b0 #b01111110 #b10101010011111101111101))))
(let ((.def_87 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_86)))
(let ((.def_92 (fp.add RNE .def_87 .def_91)))
(let ((.def_96 (fp.add RNE .def_92 .def_95)))
(let ((.def_101 (fp.add RNE .def_96 .def_100)))
(let ((.def_105 (fp.add RNE .def_101 .def_104)))
(let ((.def_109 (fp.add RNE .def_105 .def_108)))
(let ((.def_114 (fp.add RNE .def_109 .def_113)))
(let ((.def_115 (fp.leq (fp #b1 #b01111101 #b11110110110010001011010) .def_114)))
.def_115))))))))))))))))
(assert (let ((.def_145 (fp.mul RNE x6 (fp #b0 #b01111100 #b10010001011010000111001))))
(let ((.def_141 (fp.mul RNE x5 (fp #b0 #b01111101 #b01001000101101000011101))))
(let ((.def_137 (fp.mul RNE x4 (fp #b0 #b01111110 #b10100100010110100001110))))
(let ((.def_133 (fp.mul RNE x3 (fp #b0 #b01111101 #b01010010111100011010101))))
(let ((.def_129 (fp.mul RNE x2 (fp #b1 #b01111110 #b01101110000101000111101))))
(let ((.def_124 (fp.mul RNE x1 (fp #b0 #b01111010 #b11001010110000001000010))))
(let ((.def_120 (fp.mul RNE x0 (fp #b0 #b01111011 #b10011001100110011001101))))
(let ((.def_121 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_120)))
(let ((.def_125 (fp.add RNE .def_121 .def_124)))
(let ((.def_130 (fp.add RNE .def_125 .def_129)))
(let ((.def_134 (fp.add RNE .def_130 .def_133)))
(let ((.def_138 (fp.add RNE .def_134 .def_137)))
(let ((.def_142 (fp.add RNE .def_138 .def_141)))
(let ((.def_146 (fp.add RNE .def_142 .def_145)))
(let ((.def_147 (fp.leq .def_146 (fp #b0 #b01111100 #b11111011111001110110110))))
.def_147))))))))))))))))
(assert (let ((.def_182 (fp.mul RNE x6 (fp #b1 #b01111110 #b00000110001001001101111))))
(let ((.def_177 (fp.mul RNE x5 (fp #b0 #b01111011 #b11001110110110010001011))))
(let ((.def_173 (fp.mul RNE x4 (fp #b1 #b01111101 #b01011011001000101101000))))
(let ((.def_168 (fp.mul RNE x3 (fp #b0 #b01111110 #b10100010010011011101001))))
(let ((.def_164 (fp.mul RNE x2 (fp #b1 #b01111110 #b11111010111000010100100))))
(let ((.def_159 (fp.mul RNE x1 (fp #b1 #b01111110 #b11011101101100100010111))))
(let ((.def_154 (fp.mul RNE x0 (fp #b1 #b01111101 #b10111010010111100011011))))
(let ((.def_155 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_154)))
(let ((.def_160 (fp.add RNE .def_155 .def_159)))
(let ((.def_165 (fp.add RNE .def_160 .def_164)))
(let ((.def_169 (fp.add RNE .def_165 .def_168)))
(let ((.def_174 (fp.add RNE .def_169 .def_173)))
(let ((.def_178 (fp.add RNE .def_174 .def_177)))
(let ((.def_183 (fp.add RNE .def_178 .def_182)))
(let ((.def_184 (fp.leq (fp #b1 #b01111110 #b11110110010001011010001) .def_183)))
.def_184))))))))))))))))
(assert (let ((.def_214 (fp.mul RNE x6 (fp #b0 #b01111110 #b10110000101000111101100))))
(let ((.def_210 (fp.mul RNE x5 (fp #b0 #b01111100 #b10101100000010000011001))))
(let ((.def_206 (fp.mul RNE x4 (fp #b1 #b01111110 #b10111001010110000001000))))
(let ((.def_201 (fp.mul RNE x3 (fp #b0 #b01111101 #b10001000001100010010011))))
(let ((.def_197 (fp.mul RNE x2 (fp #b1 #b01111110 #b01110110110010001011010))))
(let ((.def_192 (fp.mul RNE x1 (fp #b0 #b01111110 #b00000110001001001101111))))
(let ((.def_190 (fp.mul RNE x0 (fp #b1 #b01111011 #b11111011111001110110110))))
(let ((.def_191 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_190)))
(let ((.def_193 (fp.add RNE .def_191 .def_192)))
(let ((.def_198 (fp.add RNE .def_193 .def_197)))
(let ((.def_202 (fp.add RNE .def_198 .def_201)))
(let ((.def_207 (fp.add RNE .def_202 .def_206)))
(let ((.def_211 (fp.add RNE .def_207 .def_210)))
(let ((.def_215 (fp.add RNE .def_211 .def_214)))
(let ((.def_216 (fp.leq (fp #b0 #b01111100 #b11000100100110111010011) .def_215)))
.def_216))))))))))))))))
(assert (let ((.def_251 (fp.mul RNE x6 (fp #b1 #b01111110 #b00000111101011100001010))))
(let ((.def_246 (fp.mul RNE x5 (fp #b1 #b01111110 #b11101111100111011011001))))
(let ((.def_241 (fp.mul RNE x4 (fp #b1 #b01111110 #b01101101100100010110100))))
(let ((.def_236 (fp.mul RNE x3 (fp #b0 #b01111110 #b00011000100100110111010))))
(let ((.def_232 (fp.mul RNE x2 (fp #b0 #b01111110 #b01111000010100011110110))))
(let ((.def_228 (fp.mul RNE x1 (fp #b1 #b01111110 #b01010111100011010101000))))
(let ((.def_223 (fp.mul RNE x0 (fp #b1 #b01111110 #b10011110101110000101001))))
(let ((.def_224 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_223)))
(let ((.def_229 (fp.add RNE .def_224 .def_228)))
(let ((.def_233 (fp.add RNE .def_229 .def_232)))
(let ((.def_237 (fp.add RNE .def_233 .def_236)))
(let ((.def_242 (fp.add RNE .def_237 .def_241)))
(let ((.def_247 (fp.add RNE .def_242 .def_246)))
(let ((.def_252 (fp.add RNE .def_247 .def_251)))
(let ((.def_253 (fp.leq .def_252 (fp #b1 #b01111111 #b00000000000000000000000))))
.def_253))))))))))))))))
(assert (let ((.def_281 (fp.mul RNE x6 (fp #b0 #b01111101 #b01010010111100011010101))))
(let ((.def_279 (fp.mul RNE x5 (fp #b1 #b01111101 #b01011001000101101000100))))
(let ((.def_274 (fp.mul RNE x4 (fp #b0 #b01111110 #b00110100101111000110101))))
(let ((.def_270 (fp.mul RNE x3 (fp #b0 #b01111110 #b00100000010000011000101))))
(let ((.def_266 (fp.mul RNE x2 (fp #b1 #b01111110 #b00110011001100110011010))))
(let ((.def_261 (fp.mul RNE x1 (fp #b0 #b01111101 #b01001010110000001000010))))
(let ((.def_257 (fp.mul RNE (fp #b0 #b00000000 #b00000000000000000000000) x0)))
(let ((.def_258 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_257)))
(let ((.def_262 (fp.add RNE .def_258 .def_261)))
(let ((.def_267 (fp.add RNE .def_262 .def_266)))
(let ((.def_271 (fp.add RNE .def_267 .def_270)))
(let ((.def_275 (fp.add RNE .def_271 .def_274)))
(let ((.def_280 (fp.add RNE .def_275 .def_279)))
(let ((.def_282 (fp.add RNE .def_280 .def_281)))
(let ((.def_283 (fp.leq (fp #b1 #b01111110 #b00111011011001000101101) .def_282)))
.def_283))))))))))))))))
(assert (let ((.def_317 (fp.mul RNE x6 (fp #b0 #b01111010 #b10111010010111100011011))))
(let ((.def_313 (fp.mul RNE x5 (fp #b1 #b01111110 #b11100011110101110000101))))
(let ((.def_308 (fp.mul RNE x4 (fp #b0 #b01111010 #b00000110001001001101111))))
(let ((.def_304 (fp.mul RNE x3 (fp #b0 #b01111110 #b11011100101011000000100))))
(let ((.def_300 (fp.mul RNE x2 (fp #b1 #b01111101 #b00110110010001011010001))))
(let ((.def_295 (fp.mul RNE x1 (fp #b1 #b01111100 #b00010110100001110010110))))
(let ((.def_290 (fp.mul RNE x0 (fp #b1 #b01111110 #b11001101010011111110000))))
(let ((.def_291 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_290)))
(let ((.def_296 (fp.add RNE .def_291 .def_295)))
(let ((.def_301 (fp.add RNE .def_296 .def_300)))
(let ((.def_305 (fp.add RNE .def_301 .def_304)))
(let ((.def_309 (fp.add RNE .def_305 .def_308)))
(let ((.def_314 (fp.add RNE .def_309 .def_313)))
(let ((.def_318 (fp.add RNE .def_314 .def_317)))
(let ((.def_319 (fp.leq .def_318 (fp #b1 #b01111110 #b10000110001001001101111))))
.def_319))))))))))))))))
(assert (let ((.def_344 (fp.mul RNE x5 (fp #b0 #b01111101 #b11011111001110110110010))))
(let ((.def_342 (fp.mul RNE x4 (fp #b0 #b01111101 #b01011101001011110001101))))
(let ((.def_338 (fp.mul RNE x3 (fp #b0 #b01111110 #b11001100010010011011101))))
(let ((.def_334 (fp.mul RNE x2 (fp #b0 #b01111110 #b00111111011111001110111))))
(let ((.def_330 (fp.mul RNE x1 (fp #b1 #b01111110 #b11101111000110101010000))))
(let ((.def_325 (fp.mul RNE x0 (fp #b0 #b01111101 #b10001100010010011011101))))
(let ((.def_326 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_325)))
(let ((.def_331 (fp.add RNE .def_326 .def_330)))
(let ((.def_335 (fp.add RNE .def_331 .def_334)))
(let ((.def_339 (fp.add RNE .def_335 .def_338)))
(let ((.def_343 (fp.add RNE .def_339 .def_342)))
(let ((.def_345 (fp.add RNE .def_343 .def_344)))
(let ((.def_182 (fp.mul RNE x6 (fp #b1 #b01111110 #b00000110001001001101111))))
(let ((.def_346 (fp.add RNE .def_182 .def_345)))
(let ((.def_347 (fp.leq (fp #b1 #b01111101 #b10101100000010000011001) .def_346)))
.def_347))))))))))))))))
(assert (let ((.def_380 (fp.mul RNE x6 (fp #b1 #b01111100 #b01010011111101111100111))))
(let ((.def_375 (fp.mul RNE x5 (fp #b0 #b01111100 #b10110110010001011010001))))
(let ((.def_371 (fp.mul RNE x4 (fp #b0 #b01111000 #b10101001111110111110100))))
(let ((.def_367 (fp.mul RNE x3 (fp #b1 #b01111110 #b10001000001100010010011))))
(let ((.def_362 (fp.mul RNE x2 (fp #b1 #b01111101 #b00110100001110010101100))))
(let ((.def_357 (fp.mul RNE x1 (fp #b0 #b01111110 #b10111111011111001110111))))
(let ((.def_353 (fp.mul RNE x0 (fp #b0 #b01111110 #b11000100000110001001010))))
(let ((.def_354 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_353)))
(let ((.def_358 (fp.add RNE .def_354 .def_357)))
(let ((.def_363 (fp.add RNE .def_358 .def_362)))
(let ((.def_368 (fp.add RNE .def_363 .def_367)))
(let ((.def_372 (fp.add RNE .def_368 .def_371)))
(let ((.def_376 (fp.add RNE .def_372 .def_375)))
(let ((.def_381 (fp.add RNE .def_376 .def_380)))
(let ((.def_382 (fp.leq (fp #b1 #b01111110 #b11100010110100001110011) .def_381)))
.def_382))))))))))))))))
(assert (let ((.def_411 (fp.mul RNE x6 (fp #b0 #b01111101 #b11100001010001111010111))))
(let ((.def_409 (fp.mul RNE x5 (fp #b0 #b01111110 #b10011100001010001111011))))
(let ((.def_405 (fp.mul RNE x4 (fp #b0 #b01111110 #b10010110100001110010110))))
(let ((.def_401 (fp.mul RNE x3 (fp #b1 #b01111110 #b10011001000101101000100))))
(let ((.def_396 (fp.mul RNE x2 (fp #b1 #b01111110 #b10100110011001100110011))))
(let ((.def_391 (fp.mul RNE x1 (fp #b1 #b01111110 #b00101010011111101111101))))
(let ((.def_386 (fp.mul RNE x0 (fp #b1 #b01111101 #b11011010000111001010110))))
(let ((.def_387 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_386)))
(let ((.def_392 (fp.add RNE .def_387 .def_391)))
(let ((.def_397 (fp.add RNE .def_392 .def_396)))
(let ((.def_402 (fp.add RNE .def_397 .def_401)))
(let ((.def_406 (fp.add RNE .def_402 .def_405)))
(let ((.def_410 (fp.add RNE .def_406 .def_409)))
(let ((.def_412 (fp.add RNE .def_410 .def_411)))
(let ((.def_413 (fp.leq .def_412 (fp #b0 #b01111100 #b10010001011010000111001))))
.def_413))))))))))))))))
(assert (let ((.def_442 (fp.mul RNE x6 (fp #b0 #b01111101 #b01110010101100000010000))))
(let ((.def_438 (fp.mul RNE x5 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_436 (fp.mul RNE x4 (fp #b0 #b01111110 #b01010011011101001011110))))
(let ((.def_432 (fp.mul RNE x3 (fp #b1 #b01111110 #b00001011110001101010100))))
(let ((.def_427 (fp.mul RNE x2 (fp #b0 #b01111110 #b11001110010101100000010))))
(let ((.def_423 (fp.mul RNE x1 (fp #b1 #b01111110 #b01100111111011111001111))))
(let ((.def_418 (fp.mul RNE x0 (fp #b0 #b01111101 #b11001011110001101010100))))
(let ((.def_419 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_418)))
(let ((.def_424 (fp.add RNE .def_419 .def_423)))
(let ((.def_428 (fp.add RNE .def_424 .def_427)))
(let ((.def_433 (fp.add RNE .def_428 .def_432)))
(let ((.def_437 (fp.add RNE .def_433 .def_436)))
(let ((.def_439 (fp.add RNE .def_437 .def_438)))
(let ((.def_443 (fp.add RNE .def_439 .def_442)))
(let ((.def_444 (fp.leq .def_443 (fp #b0 #b01111101 #b01000011100101011000001))))
.def_444))))))))))))))))
(assert (let ((.def_470 (fp.mul RNE x6 (fp #b1 #b01111110 #b00000110101001111111000))))
(let ((.def_465 (fp.mul RNE x5 (fp #b0 #b01111110 #b00110100001110010101100))))
(let ((.def_461 (fp.mul RNE x4 (fp #b1 #b01111011 #b11111011111001110110110))))
(let ((.def_459 (fp.mul RNE x3 (fp #b0 #b01111100 #b01000101101000011100101))))
(let ((.def_455 (fp.mul RNE x2 (fp #b0 #b01111101 #b00000011000100100110111))))
(let ((.def_450 (fp.mul RNE x0 (fp #b1 #b01111101 #b10100010110100001110011))))
(let ((.def_451 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_450)))
(let ((.def_159 (fp.mul RNE x1 (fp #b1 #b01111110 #b11011101101100100010111))))
(let ((.def_452 (fp.add RNE .def_159 .def_451)))
(let ((.def_456 (fp.add RNE .def_452 .def_455)))
(let ((.def_460 (fp.add RNE .def_456 .def_459)))
(let ((.def_462 (fp.add RNE .def_460 .def_461)))
(let ((.def_466 (fp.add RNE .def_462 .def_465)))
(let ((.def_471 (fp.add RNE .def_466 .def_470)))
(let ((.def_472 (fp.leq (fp #b0 #b01111101 #b10001111010111000010100) .def_471)))
.def_472))))))))))))))))
(assert (let ((.def_499 (fp.mul RNE x6 (fp #b0 #b01111110 #b01010100011110101110001))))
(let ((.def_495 (fp.mul RNE x5 (fp #b1 #b01111110 #b00111010111000010100100))))
(let ((.def_490 (fp.mul RNE x4 (fp #b0 #b01111110 #b10001000001100010010011))))
(let ((.def_488 (fp.mul RNE x3 (fp #b1 #b01111110 #b11001111010111000010100))))
(let ((.def_483 (fp.mul RNE x2 (fp #b0 #b01111101 #b10110001001001101110101))))
(let ((.def_479 (fp.mul RNE x1 (fp #b0 #b01111010 #b11010010111100011010101))))
(let ((.def_475 (fp.mul RNE x0 (fp #b0 #b01111100 #b00010110100001110010110))))
(let ((.def_476 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_475)))
(let ((.def_480 (fp.add RNE .def_476 .def_479)))
(let ((.def_484 (fp.add RNE .def_480 .def_483)))
(let ((.def_489 (fp.add RNE .def_484 .def_488)))
(let ((.def_491 (fp.add RNE .def_489 .def_490)))
(let ((.def_496 (fp.add RNE .def_491 .def_495)))
(let ((.def_500 (fp.add RNE .def_496 .def_499)))
(let ((.def_501 (fp.leq (fp #b0 #b01111110 #b01011001000101101000100) .def_500)))
.def_501))))))))))))))))
(assert (let ((.def_530 (fp.mul RNE x6 (fp #b1 #b01111101 #b10111101011100001010010))))
(let ((.def_525 (fp.mul RNE x5 (fp #b0 #b01111010 #b11010010111100011010101))))
(let ((.def_523 (fp.mul RNE x4 (fp #b0 #b01111110 #b10010100011110101110001))))
(let ((.def_519 (fp.mul RNE x3 (fp #b1 #b01111101 #b11001011110001101010100))))
(let ((.def_516 (fp.mul RNE x2 (fp #b1 #b01111110 #b00011010000111001010110))))
(let ((.def_511 (fp.mul RNE x1 (fp #b1 #b01111010 #b00101111000110101010000))))
(let ((.def_506 (fp.mul RNE x0 (fp #b0 #b01111010 #b11101011100001010001111))))
(let ((.def_507 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_506)))
(let ((.def_512 (fp.add RNE .def_507 .def_511)))
(let ((.def_517 (fp.add RNE .def_512 .def_516)))
(let ((.def_520 (fp.add RNE .def_517 .def_519)))
(let ((.def_524 (fp.add RNE .def_520 .def_523)))
(let ((.def_526 (fp.add RNE .def_524 .def_525)))
(let ((.def_531 (fp.add RNE .def_526 .def_530)))
(let ((.def_532 (fp.leq (fp #b0 #b01111101 #b01101111100111011011001) .def_531)))
.def_532))))))))))))))))
(assert (let ((.def_563 (fp.mul RNE x6 (fp #b1 #b01111110 #b01100100110111010011000))))
(let ((.def_558 (fp.mul RNE x5 (fp #b1 #b01111110 #b10100111111011111001111))))
(let ((.def_553 (fp.mul RNE x4 (fp #b0 #b01111110 #b01001111010111000010100))))
(let ((.def_549 (fp.mul RNE x3 (fp #b0 #b01111101 #b00010001011010000111001))))
(let ((.def_545 (fp.mul RNE x2 (fp #b0 #b01111110 #b11101000011100101011000))))
(let ((.def_541 (fp.mul RNE x1 (fp #b0 #b01111010 #b10100001110010101100000))))
(let ((.def_537 (fp.mul RNE x0 (fp #b0 #b01111101 #b00100010110100001110011))))
(let ((.def_538 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_537)))
(let ((.def_542 (fp.add RNE .def_538 .def_541)))
(let ((.def_546 (fp.add RNE .def_542 .def_545)))
(let ((.def_550 (fp.add RNE .def_546 .def_549)))
(let ((.def_554 (fp.add RNE .def_550 .def_553)))
(let ((.def_559 (fp.add RNE .def_554 .def_558)))
(let ((.def_564 (fp.add RNE .def_559 .def_563)))
(let ((.def_565 (fp.leq .def_564 (fp #b0 #b01111101 #b00110000001000001100010))))
.def_565))))))))))))))))
(assert (let ((.def_601 (fp.mul RNE x6 (fp #b1 #b01111100 #b11000000100000110001001))))
(let ((.def_596 (fp.mul RNE x5 (fp #b1 #b01111101 #b10101011000000100000110))))
(let ((.def_591 (fp.mul RNE x4 (fp #b1 #b01111100 #b10100111111011111001111))))
(let ((.def_586 (fp.mul RNE x3 (fp #b1 #b01111101 #b10100100110111010011000))))
(let ((.def_581 (fp.mul RNE x2 (fp #b1 #b01111110 #b11011010100111111011111))))
(let ((.def_576 (fp.mul RNE x1 (fp #b1 #b01111110 #b10000101000111101011100))))
(let ((.def_571 (fp.mul RNE x0 (fp #b1 #b01111110 #b00010010011011101001100))))
(let ((.def_572 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_571)))
(let ((.def_577 (fp.add RNE .def_572 .def_576)))
(let ((.def_582 (fp.add RNE .def_577 .def_581)))
(let ((.def_587 (fp.add RNE .def_582 .def_586)))
(let ((.def_592 (fp.add RNE .def_587 .def_591)))
(let ((.def_597 (fp.add RNE .def_592 .def_596)))
(let ((.def_602 (fp.add RNE .def_597 .def_601)))
(let ((.def_603 (fp.leq .def_602 (fp #b0 #b01111101 #b11110001101010011111110))))
.def_603))))))))))))))))
(check-sat)