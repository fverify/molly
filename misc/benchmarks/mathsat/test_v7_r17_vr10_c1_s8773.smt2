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
(assert (let ((.def_79 (fp.mul RNE x6 (fp #b1 #b01111101 #b10000011000100100110111))))
(let ((.def_74 (fp.mul RNE x5 (fp #b1 #b01111101 #b00101111000110101010000))))
(let ((.def_69 (fp.mul RNE x4 (fp #b1 #b01111011 #b11100011010100111111100))))
(let ((.def_64 (fp.mul RNE x3 (fp #b0 #b01111110 #b01000011100101011000001))))
(let ((.def_60 (fp.mul RNE x2 (fp #b0 #b01111110 #b10101011000000100000110))))
(let ((.def_56 (fp.mul RNE x1 (fp #b0 #b01111011 #b11111011111001110110110))))
(let ((.def_52 (fp.mul RNE x0 (fp #b1 #b01111110 #b10010100111111011111010))))
(let ((.def_53 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_52)))
(let ((.def_57 (fp.add RNE .def_53 .def_56)))
(let ((.def_61 (fp.add RNE .def_57 .def_60)))
(let ((.def_65 (fp.add RNE .def_61 .def_64)))
(let ((.def_70 (fp.add RNE .def_65 .def_69)))
(let ((.def_75 (fp.add RNE .def_70 .def_74)))
(let ((.def_80 (fp.add RNE .def_75 .def_79)))
(let ((.def_81 (fp.leq (fp #b1 #b01111110 #b10100001010001111010111) .def_80)))
.def_81))))))))))))))))
(assert (let ((.def_113 (fp.mul RNE x6 (fp #b1 #b01111101 #b01111000110101001111111))))
(let ((.def_108 (fp.mul RNE x5 (fp #b0 #b01111110 #b00101000111101011100001))))
(let ((.def_104 (fp.mul RNE x4 (fp #b1 #b01111110 #b01111001110110110010001))))
(let ((.def_99 (fp.mul RNE x3 (fp #b0 #b01111011 #b10011101101100100010111))))
(let ((.def_95 (fp.mul RNE x2 (fp #b0 #b01111110 #b11010011011101001011110))))
(let ((.def_91 (fp.mul RNE x1 (fp #b0 #b01111100 #b11111011111001110110110))))
(let ((.def_87 (fp.mul RNE x0 (fp #b1 #b01111110 #b00001011010000111001011))))
(let ((.def_88 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_87)))
(let ((.def_92 (fp.add RNE .def_88 .def_91)))
(let ((.def_96 (fp.add RNE .def_92 .def_95)))
(let ((.def_100 (fp.add RNE .def_96 .def_99)))
(let ((.def_105 (fp.add RNE .def_100 .def_104)))
(let ((.def_109 (fp.add RNE .def_105 .def_108)))
(let ((.def_114 (fp.add RNE .def_109 .def_113)))
(let ((.def_115 (fp.leq .def_114 (fp #b0 #b01111110 #b10001101110100101111001))))
.def_115))))))))))))))))
(assert (let ((.def_143 (fp.mul RNE x6 (fp #b0 #b01111101 #b01010100111111011111010))))
(let ((.def_139 (fp.mul RNE x5 (fp #b0 #b01111101 #b11001101110100101111001))))
(let ((.def_135 (fp.mul RNE x4 (fp #b1 #b01111110 #b10100010010011011101001))))
(let ((.def_130 (fp.mul RNE x3 (fp #b0 #b01111110 #b01110011101101100100011))))
(let ((.def_126 (fp.mul RNE x2 (fp #b0 #b01111011 #b11011011001000101101000))))
(let ((.def_122 (fp.mul RNE x1 (fp #b0 #b01111110 #b11011000100100110111010))))
(let ((.def_118 (fp.mul RNE x0 (fp #b0 #b01111001 #b01000111101011100001010))))
(let ((.def_119 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_118)))
(let ((.def_123 (fp.add RNE .def_119 .def_122)))
(let ((.def_127 (fp.add RNE .def_123 .def_126)))
(let ((.def_131 (fp.add RNE .def_127 .def_130)))
(let ((.def_136 (fp.add RNE .def_131 .def_135)))
(let ((.def_140 (fp.add RNE .def_136 .def_139)))
(let ((.def_144 (fp.add RNE .def_140 .def_143)))
(let ((.def_145 (fp.leq (fp #b0 #b01111110 #b01000011100101011000001) .def_144)))
.def_145))))))))))))))))
(assert (let ((.def_179 (fp.mul RNE x6 (fp #b1 #b01111101 #b00001000001100010010011))))
(let ((.def_174 (fp.mul RNE x5 (fp #b0 #b01111110 #b01111100011010100111111))))
(let ((.def_170 (fp.mul RNE x4 (fp #b1 #b01111110 #b11101101100100010110100))))
(let ((.def_165 (fp.mul RNE x3 (fp #b1 #b01111100 #b10110000001000001100010))))
(let ((.def_160 (fp.mul RNE x2 (fp #b0 #b01111101 #b01000110101001111111000))))
(let ((.def_156 (fp.mul RNE x1 (fp #b0 #b01111110 #b00100101111000110101010))))
(let ((.def_152 (fp.mul RNE x0 (fp #b1 #b01111110 #b10110101110000101001000))))
(let ((.def_153 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_152)))
(let ((.def_157 (fp.add RNE .def_153 .def_156)))
(let ((.def_161 (fp.add RNE .def_157 .def_160)))
(let ((.def_166 (fp.add RNE .def_161 .def_165)))
(let ((.def_171 (fp.add RNE .def_166 .def_170)))
(let ((.def_175 (fp.add RNE .def_171 .def_174)))
(let ((.def_180 (fp.add RNE .def_175 .def_179)))
(let ((.def_181 (fp.leq (fp #b1 #b01111110 #b01011100001010001111011) .def_180)))
.def_181))))))))))))))))
(assert (let ((.def_215 (fp.mul RNE x6 (fp #b0 #b01111110 #b01100111111011111001111))))
(let ((.def_211 (fp.mul RNE x5 (fp #b0 #b01111110 #b00111011111001110110110))))
(let ((.def_207 (fp.mul RNE x4 (fp #b1 #b01111100 #b00000100000110001001010))))
(let ((.def_202 (fp.mul RNE x3 (fp #b1 #b01111110 #b10111111011111001110111))))
(let ((.def_197 (fp.mul RNE x2 (fp #b1 #b01111110 #b11011011101001011110010))))
(let ((.def_192 (fp.mul RNE x1 (fp #b1 #b01111101 #b11111010111000010100100))))
(let ((.def_187 (fp.mul RNE x0 (fp #b1 #b01111101 #b00100110111010010111100))))
(let ((.def_188 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_187)))
(let ((.def_193 (fp.add RNE .def_188 .def_192)))
(let ((.def_198 (fp.add RNE .def_193 .def_197)))
(let ((.def_203 (fp.add RNE .def_198 .def_202)))
(let ((.def_208 (fp.add RNE .def_203 .def_207)))
(let ((.def_212 (fp.add RNE .def_208 .def_211)))
(let ((.def_216 (fp.add RNE .def_212 .def_215)))
(let ((.def_217 (fp.leq (fp #b0 #b01111110 #b01010100011110101110001) .def_216)))
.def_217))))))))))))))))
(assert (let ((.def_250 (fp.mul RNE x6 (fp #b0 #b01111011 #b10101001111110111110100))))
(let ((.def_246 (fp.mul RNE x5 (fp #b0 #b01111110 #b01111001010110000001000))))
(let ((.def_242 (fp.mul RNE x4 (fp #b1 #b01111010 #b00110111010010111100011))))
(let ((.def_237 (fp.mul RNE x3 (fp #b1 #b01111110 #b00111001110110110010001))))
(let ((.def_232 (fp.mul RNE x2 (fp #b1 #b01111101 #b11110110110010001011010))))
(let ((.def_227 (fp.mul RNE x1 (fp #b1 #b01111110 #b11011010100111111011111))))
(let ((.def_222 (fp.mul RNE x0 (fp #b0 #b01111100 #b01101000011100101011000))))
(let ((.def_223 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_222)))
(let ((.def_228 (fp.add RNE .def_223 .def_227)))
(let ((.def_233 (fp.add RNE .def_228 .def_232)))
(let ((.def_238 (fp.add RNE .def_233 .def_237)))
(let ((.def_243 (fp.add RNE .def_238 .def_242)))
(let ((.def_247 (fp.add RNE .def_243 .def_246)))
(let ((.def_251 (fp.add RNE .def_247 .def_250)))
(let ((.def_252 (fp.leq (fp #b0 #b01111101 #b10100111111011111001111) .def_251)))
.def_252))))))))))))))))
(assert (let ((.def_284 (fp.mul RNE x6 (fp #b1 #b01110111 #b00000110001001001101111))))
(let ((.def_279 (fp.mul RNE x5 (fp #b1 #b01111001 #b10011001100110011001101))))
(let ((.def_274 (fp.mul RNE x4 (fp #b1 #b01111101 #b00111011011001000101101))))
(let ((.def_269 (fp.mul RNE x3 (fp #b1 #b01111110 #b00000011100101011000001))))
(let ((.def_264 (fp.mul RNE x2 (fp #b0 #b01111100 #b01000001100010010011100))))
(let ((.def_260 (fp.mul RNE x1 (fp #b1 #b01111110 #b10010110100001110010110))))
(let ((.def_255 (fp.mul RNE x0 (fp #b1 #b01111101 #b01000110101001111111000))))
(let ((.def_256 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_255)))
(let ((.def_261 (fp.add RNE .def_256 .def_260)))
(let ((.def_265 (fp.add RNE .def_261 .def_264)))
(let ((.def_270 (fp.add RNE .def_265 .def_269)))
(let ((.def_275 (fp.add RNE .def_270 .def_274)))
(let ((.def_280 (fp.add RNE .def_275 .def_279)))
(let ((.def_285 (fp.add RNE .def_280 .def_284)))
(let ((.def_286 (fp.leq .def_285 (fp #b1 #b01111110 #b01111100011010100111111))))
.def_286))))))))))))))))
(assert (let ((.def_313 (fp.mul RNE x6 (fp #b0 #b01111101 #b00000001000001100010010))))
(let ((.def_309 (fp.mul RNE x5 (fp #b1 #b01111101 #b10010100011110101110001))))
(let ((.def_304 (fp.mul RNE x4 (fp #b0 #b01111101 #b10101011000000100000110))))
(let ((.def_300 (fp.mul RNE x3 (fp #b0 #b01111110 #b10010000011000100100111))))
(let ((.def_296 (fp.mul RNE x2 (fp #b0 #b01111101 #b10100111111011111001111))))
(let ((.def_294 (fp.mul RNE x1 (fp #b0 #b01111110 #b10111111011111001110111))))
(let ((.def_292 (fp.mul RNE x0 (fp #b0 #b01111110 #b10110100001110010101100))))
(let ((.def_293 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_292)))
(let ((.def_295 (fp.add RNE .def_293 .def_294)))
(let ((.def_297 (fp.add RNE .def_295 .def_296)))
(let ((.def_301 (fp.add RNE .def_297 .def_300)))
(let ((.def_305 (fp.add RNE .def_301 .def_304)))
(let ((.def_310 (fp.add RNE .def_305 .def_309)))
(let ((.def_314 (fp.add RNE .def_310 .def_313)))
(let ((.def_315 (fp.leq .def_314 (fp #b1 #b01111110 #b10001001001101110100110))))
.def_315))))))))))))))))
(assert (let ((.def_348 (fp.mul RNE x6 (fp #b0 #b01111110 #b01111111011111001110111))))
(let ((.def_344 (fp.mul RNE x5 (fp #b1 #b01111110 #b00111011011001000101101))))
(let ((.def_339 (fp.mul RNE x4 (fp #b0 #b01111101 #b10100001110010101100000))))
(let ((.def_335 (fp.mul RNE x3 (fp #b1 #b01111110 #b11110100101111000110101))))
(let ((.def_330 (fp.mul RNE x2 (fp #b0 #b01111110 #b00010100011110101110001))))
(let ((.def_326 (fp.mul RNE x1 (fp #b1 #b01111110 #b11110111110011101101101))))
(let ((.def_321 (fp.mul RNE x0 (fp #b0 #b01111101 #b10001010001111010111000))))
(let ((.def_322 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_321)))
(let ((.def_327 (fp.add RNE .def_322 .def_326)))
(let ((.def_331 (fp.add RNE .def_327 .def_330)))
(let ((.def_336 (fp.add RNE .def_331 .def_335)))
(let ((.def_340 (fp.add RNE .def_336 .def_339)))
(let ((.def_345 (fp.add RNE .def_340 .def_344)))
(let ((.def_349 (fp.add RNE .def_345 .def_348)))
(let ((.def_350 (fp.leq (fp #b1 #b01110110 #b00000110001001001101111) .def_349)))
.def_350))))))))))))))))
(assert (let ((.def_383 (fp.mul RNE x6 (fp #b0 #b01111101 #b11000001100010010011100))))
(let ((.def_379 (fp.mul RNE x5 (fp #b1 #b01111011 #b01011000000100000110001))))
(let ((.def_374 (fp.mul RNE x4 (fp #b0 #b01111110 #b11101010011111101111101))))
(let ((.def_370 (fp.mul RNE x3 (fp #b1 #b01111101 #b01011011001000101101000))))
(let ((.def_365 (fp.mul RNE x2 (fp #b1 #b01111110 #b11010010111100011010101))))
(let ((.def_360 (fp.mul RNE x1 (fp #b0 #b01111101 #b01010010111100011010101))))
(let ((.def_356 (fp.mul RNE x0 (fp #b1 #b01111010 #b01111000110101001111111))))
(let ((.def_357 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_356)))
(let ((.def_361 (fp.add RNE .def_357 .def_360)))
(let ((.def_366 (fp.add RNE .def_361 .def_365)))
(let ((.def_371 (fp.add RNE .def_366 .def_370)))
(let ((.def_375 (fp.add RNE .def_371 .def_374)))
(let ((.def_380 (fp.add RNE .def_375 .def_379)))
(let ((.def_384 (fp.add RNE .def_380 .def_383)))
(let ((.def_385 (fp.leq (fp #b0 #b01111100 #b10001101010011111110000) .def_384)))
.def_385))))))))))))))))
(assert (let ((.def_417 (fp.mul RNE x6 (fp #b1 #b01111011 #b01101100100010110100010))))
(let ((.def_412 (fp.mul RNE x5 (fp #b0 #b01111110 #b10110101001111110111110))))
(let ((.def_408 (fp.mul RNE x4 (fp #b1 #b01111101 #b10011100101011000000100))))
(let ((.def_403 (fp.mul RNE x3 (fp #b1 #b01111110 #b01001001101110100101111))))
(let ((.def_398 (fp.mul RNE x2 (fp #b0 #b01111101 #b01110000101000111101100))))
(let ((.def_394 (fp.mul RNE x1 (fp #b0 #b01111110 #b01011110001101010100000))))
(let ((.def_390 (fp.mul RNE x0 (fp #b0 #b01111100 #b01011110001101010100000))))
(let ((.def_391 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_390)))
(let ((.def_395 (fp.add RNE .def_391 .def_394)))
(let ((.def_399 (fp.add RNE .def_395 .def_398)))
(let ((.def_404 (fp.add RNE .def_399 .def_403)))
(let ((.def_409 (fp.add RNE .def_404 .def_408)))
(let ((.def_413 (fp.add RNE .def_409 .def_412)))
(let ((.def_418 (fp.add RNE .def_413 .def_417)))
(let ((.def_419 (fp.leq .def_418 (fp #b0 #b01111110 #b00101111100111011011001))))
.def_419))))))))))))))))
(assert (let ((.def_450 (fp.mul RNE x6 (fp #b0 #b01111110 #b00111110011101101100100))))
(let ((.def_446 (fp.mul RNE x5 (fp #b1 #b01111101 #b10111010010111100011011))))
(let ((.def_441 (fp.mul RNE x4 (fp #b1 #b01111101 #b11111011111001110110110))))
(let ((.def_436 (fp.mul RNE x3 (fp #b1 #b01111110 #b01001101010011111110000))))
(let ((.def_431 (fp.mul RNE x2 (fp #b1 #b01111110 #b10100001010001111010111))))
(let ((.def_429 (fp.mul RNE x1 (fp #b0 #b01111110 #b00011010000111001010110))))
(let ((.def_425 (fp.mul RNE x0 (fp #b0 #b01111110 #b00000111001010110000001))))
(let ((.def_426 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_425)))
(let ((.def_430 (fp.add RNE .def_426 .def_429)))
(let ((.def_432 (fp.add RNE .def_430 .def_431)))
(let ((.def_437 (fp.add RNE .def_432 .def_436)))
(let ((.def_442 (fp.add RNE .def_437 .def_441)))
(let ((.def_447 (fp.add RNE .def_442 .def_446)))
(let ((.def_451 (fp.add RNE .def_447 .def_450)))
(let ((.def_452 (fp.leq .def_451 (fp #b1 #b01111110 #b01110110010001011010001))))
.def_452))))))))))))))))
(assert (let ((.def_485 (fp.mul RNE x6 (fp #b0 #b01111110 #b10111100011010100111111))))
(let ((.def_481 (fp.mul RNE x5 (fp #b1 #b01111101 #b00110110010001011010001))))
(let ((.def_476 (fp.mul RNE x4 (fp #b0 #b01111110 #b11011111101111100111011))))
(let ((.def_472 (fp.mul RNE x3 (fp #b1 #b01111101 #b01011000000100000110001))))
(let ((.def_467 (fp.mul RNE x2 (fp #b0 #b01111110 #b00111101111100111011011))))
(let ((.def_463 (fp.mul RNE x1 (fp #b0 #b01111000 #b10001001001101110100110))))
(let ((.def_459 (fp.mul RNE x0 (fp #b1 #b01111101 #b00011011101001011110010))))
(let ((.def_460 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_459)))
(let ((.def_464 (fp.add RNE .def_460 .def_463)))
(let ((.def_468 (fp.add RNE .def_464 .def_467)))
(let ((.def_473 (fp.add RNE .def_468 .def_472)))
(let ((.def_477 (fp.add RNE .def_473 .def_476)))
(let ((.def_482 (fp.add RNE .def_477 .def_481)))
(let ((.def_486 (fp.add RNE .def_482 .def_485)))
(let ((.def_487 (fp.leq (fp #b1 #b01111110 #b01100000110001001001110) .def_486)))
.def_487))))))))))))))))
(assert (let ((.def_520 (fp.mul RNE x6 (fp #b0 #b01111110 #b00000100000110001001010))))
(let ((.def_516 (fp.mul RNE x5 (fp #b0 #b01111100 #b11100011010100111111100))))
(let ((.def_512 (fp.mul RNE x4 (fp #b1 #b01111100 #b00000010000011000100101))))
(let ((.def_507 (fp.mul RNE x3 (fp #b1 #b01111110 #b10011001100110011001101))))
(let ((.def_502 (fp.mul RNE x2 (fp #b0 #b01111101 #b00111110011101101100100))))
(let ((.def_498 (fp.mul RNE x1 (fp #b1 #b01111100 #b00101011000000100000110))))
(let ((.def_493 (fp.mul RNE x0 (fp #b0 #b01111110 #b10000101101000011100101))))
(let ((.def_494 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_493)))
(let ((.def_499 (fp.add RNE .def_494 .def_498)))
(let ((.def_503 (fp.add RNE .def_499 .def_502)))
(let ((.def_508 (fp.add RNE .def_503 .def_507)))
(let ((.def_513 (fp.add RNE .def_508 .def_512)))
(let ((.def_517 (fp.add RNE .def_513 .def_516)))
(let ((.def_521 (fp.add RNE .def_517 .def_520)))
(let ((.def_522 (fp.leq (fp #b1 #b01111101 #b00100011110101110000101) .def_521)))
.def_522))))))))))))))))
(assert (let ((.def_556 (fp.mul RNE x6 (fp #b1 #b01111101 #b00010011011101001011110))))
(let ((.def_551 (fp.mul RNE x5 (fp #b0 #b01111101 #b01110110110010001011010))))
(let ((.def_547 (fp.mul RNE x4 (fp #b1 #b01111110 #b01111101111100111011011))))
(let ((.def_542 (fp.mul RNE x3 (fp #b0 #b01111110 #b00001110110110010001011))))
(let ((.def_538 (fp.mul RNE x2 (fp #b1 #b01111100 #b11010000111001010110000))))
(let ((.def_533 (fp.mul RNE x1 (fp #b1 #b01111101 #b00000101000111101011100))))
(let ((.def_528 (fp.mul RNE x0 (fp #b1 #b01111110 #b11100011110101110000101))))
(let ((.def_529 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_528)))
(let ((.def_534 (fp.add RNE .def_529 .def_533)))
(let ((.def_539 (fp.add RNE .def_534 .def_538)))
(let ((.def_543 (fp.add RNE .def_539 .def_542)))
(let ((.def_548 (fp.add RNE .def_543 .def_547)))
(let ((.def_552 (fp.add RNE .def_548 .def_551)))
(let ((.def_557 (fp.add RNE .def_552 .def_556)))
(let ((.def_558 (fp.leq .def_557 (fp #b0 #b01111110 #b00100011010100111111100))))
.def_558))))))))))))))))
(assert (let ((.def_586 (fp.mul RNE x6 (fp #b1 #b01111011 #b10100101111000110101010))))
(let ((.def_581 (fp.mul RNE x5 (fp #b0 #b01111101 #b10110110010001011010001))))
(let ((.def_577 (fp.mul RNE x4 (fp #b0 #b01111110 #b11110000101000111101100))))
(let ((.def_573 (fp.mul RNE x3 (fp #b1 #b01111110 #b10110110010001011010001))))
(let ((.def_568 (fp.mul RNE x2 (fp #b0 #b01111010 #b01100000010000011000101))))
(let ((.def_563 (fp.mul RNE x0 (fp #b0 #b01111110 #b10101111000110101010000))))
(let ((.def_564 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_563)))
(let ((.def_122 (fp.mul RNE x1 (fp #b0 #b01111110 #b11011000100100110111010))))
(let ((.def_565 (fp.add RNE .def_122 .def_564)))
(let ((.def_569 (fp.add RNE .def_565 .def_568)))
(let ((.def_574 (fp.add RNE .def_569 .def_573)))
(let ((.def_578 (fp.add RNE .def_574 .def_577)))
(let ((.def_582 (fp.add RNE .def_578 .def_581)))
(let ((.def_587 (fp.add RNE .def_582 .def_586)))
(let ((.def_588 (fp.leq (fp #b0 #b01111101 #b10111011011001000101101) .def_587)))
.def_588))))))))))))))))
(assert (let ((.def_621 (fp.mul RNE x6 (fp #b1 #b01111101 #b01001101110100101111001))))
(let ((.def_616 (fp.mul RNE x5 (fp #b0 #b01111110 #b00101011100001010001111))))
(let ((.def_612 (fp.mul RNE x4 (fp #b0 #b01111101 #b10101100000010000011001))))
(let ((.def_608 (fp.mul RNE x3 (fp #b1 #b01111011 #b00001010001111010111000))))
(let ((.def_603 (fp.mul RNE x2 (fp #b0 #b01111100 #b10010001011010000111001))))
(let ((.def_599 (fp.mul RNE x1 (fp #b1 #b01111110 #b01011011101001011110010))))
(let ((.def_594 (fp.mul RNE x0 (fp #b0 #b01111011 #b10010101100000010000011))))
(let ((.def_595 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_594)))
(let ((.def_600 (fp.add RNE .def_595 .def_599)))
(let ((.def_604 (fp.add RNE .def_600 .def_603)))
(let ((.def_609 (fp.add RNE .def_604 .def_608)))
(let ((.def_613 (fp.add RNE .def_609 .def_612)))
(let ((.def_617 (fp.add RNE .def_613 .def_616)))
(let ((.def_622 (fp.add RNE .def_617 .def_621)))
(let ((.def_623 (fp.leq .def_622 (fp #b1 #b01111100 #b00111001010110000001000))))
.def_623))))))))))))))))
(check-sat)
