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
(assert (let ((.def_77 (fp.mul RNE x6 (fp #b0 #b01111010 #b10110010001011010000111))))
(let ((.def_73 (fp.mul RNE x5 (fp #b0 #b01111110 #b01111110011101101100100))))
(let ((.def_69 (fp.mul RNE x4 (fp #b0 #b01111110 #b00110001001001101110101))))
(let ((.def_65 (fp.mul RNE x3 (fp #b0 #b01111101 #b11100111011011001000110))))
(let ((.def_61 (fp.mul RNE x2 (fp #b1 #b01111101 #b10001101010011111110000))))
(let ((.def_56 (fp.mul RNE x1 (fp #b1 #b01111110 #b00100100010110100001110))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111110 #b00100001010001111010111))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_57 (fp.add RNE .def_52 .def_56)))
(let ((.def_62 (fp.add RNE .def_57 .def_61)))
(let ((.def_66 (fp.add RNE .def_62 .def_65)))
(let ((.def_70 (fp.add RNE .def_66 .def_69)))
(let ((.def_74 (fp.add RNE .def_70 .def_73)))
(let ((.def_78 (fp.add RNE .def_74 .def_77)))
(let ((.def_79 (fp.leq (fp #b1 #b01111110 #b11011011001000101101000) .def_78)))
.def_79))))))))))))))))
(assert (let ((.def_112 (fp.mul RNE x6 (fp #b1 #b01111101 #b10110110010001011010001))))
(let ((.def_107 (fp.mul RNE x5 (fp #b0 #b01111100 #b00010100011110101110001))))
(let ((.def_103 (fp.mul RNE x4 (fp #b1 #b01111110 #b01000111001010110000001))))
(let ((.def_98 (fp.mul RNE x3 (fp #b0 #b01111101 #b11100001010001111010111))))
(let ((.def_94 (fp.mul RNE x2 (fp #b0 #b01111110 #b01010111000010100011111))))
(let ((.def_90 (fp.mul RNE x1 (fp #b1 #b01111100 #b00111111011111001110111))))
(let ((.def_85 (fp.mul RNE x0 (fp #b1 #b01111110 #b01111101011100001010010))))
(let ((.def_86 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_85)))
(let ((.def_91 (fp.add RNE .def_86 .def_90)))
(let ((.def_95 (fp.add RNE .def_91 .def_94)))
(let ((.def_99 (fp.add RNE .def_95 .def_98)))
(let ((.def_104 (fp.add RNE .def_99 .def_103)))
(let ((.def_108 (fp.add RNE .def_104 .def_107)))
(let ((.def_113 (fp.add RNE .def_108 .def_112)))
(let ((.def_114 (fp.leq .def_113 (fp #b0 #b01111101 #b00111111011111001110111))))
.def_114))))))))))))))))
(assert (let ((.def_147 (fp.mul RNE x6 (fp #b0 #b01111110 #b11001110010101100000010))))
(let ((.def_143 (fp.mul RNE x5 (fp #b1 #b01111010 #b11110011101101100100011))))
(let ((.def_138 (fp.mul RNE x4 (fp #b0 #b01111010 #b01111000110101001111111))))
(let ((.def_134 (fp.mul RNE x3 (fp #b1 #b01111110 #b11111011011001000101101))))
(let ((.def_129 (fp.mul RNE x2 (fp #b1 #b01111110 #b00101000011100101011000))))
(let ((.def_124 (fp.mul RNE x1 (fp #b0 #b01111110 #b00010001011010000111001))))
(let ((.def_120 (fp.mul RNE x0 (fp #b1 #b01111010 #b10010001011010000111001))))
(let ((.def_121 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_120)))
(let ((.def_125 (fp.add RNE .def_121 .def_124)))
(let ((.def_130 (fp.add RNE .def_125 .def_129)))
(let ((.def_135 (fp.add RNE .def_130 .def_134)))
(let ((.def_139 (fp.add RNE .def_135 .def_138)))
(let ((.def_144 (fp.add RNE .def_139 .def_143)))
(let ((.def_148 (fp.add RNE .def_144 .def_147)))
(let ((.def_149 (fp.leq (fp #b0 #b01111101 #b00111110011101101100100) .def_148)))
.def_149))))))))))))))))
(assert (let ((.def_182 (fp.mul RNE x6 (fp #b1 #b01111011 #b01111100111011011001001))))
(let ((.def_177 (fp.mul RNE x5 (fp #b0 #b01111110 #b11110001001001101110101))))
(let ((.def_173 (fp.mul RNE x4 (fp #b0 #b01111110 #b00101111000110101010000))))
(let ((.def_169 (fp.mul RNE x3 (fp #b0 #b01111101 #b01110101110000101001000))))
(let ((.def_165 (fp.mul RNE x2 (fp #b1 #b01111110 #b11010111100011010101000))))
(let ((.def_160 (fp.mul RNE x1 (fp #b1 #b01111110 #b11010001011010000111001))))
(let ((.def_155 (fp.mul RNE x0 (fp #b1 #b01111101 #b10010101100000010000011))))
(let ((.def_156 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_155)))
(let ((.def_161 (fp.add RNE .def_156 .def_160)))
(let ((.def_166 (fp.add RNE .def_161 .def_165)))
(let ((.def_170 (fp.add RNE .def_166 .def_169)))
(let ((.def_174 (fp.add RNE .def_170 .def_173)))
(let ((.def_178 (fp.add RNE .def_174 .def_177)))
(let ((.def_183 (fp.add RNE .def_178 .def_182)))
(let ((.def_184 (fp.leq (fp #b0 #b01111110 #b11010011011101001011110) .def_183)))
.def_184))))))))))))))))
(assert (let ((.def_215 (fp.mul RNE x6 (fp #b0 #b01111110 #b11001111110111110011110))))
(let ((.def_211 (fp.mul RNE x5 (fp #b0 #b01111110 #b11100011110101110000101))))
(let ((.def_207 (fp.mul RNE x4 (fp #b0 #b01111001 #b11111011111001110110110))))
(let ((.def_203 (fp.mul RNE x3 (fp #b1 #b01111110 #b11101111000110101010000))))
(let ((.def_198 (fp.mul RNE x2 (fp #b0 #b01111110 #b10100101011000000100001))))
(let ((.def_194 (fp.mul RNE x1 (fp #b0 #b01111011 #b10010101100000010000011))))
(let ((.def_190 (fp.mul RNE x0 (fp #b0 #b01111110 #b01010000011000100100111))))
(let ((.def_191 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_190)))
(let ((.def_195 (fp.add RNE .def_191 .def_194)))
(let ((.def_199 (fp.add RNE .def_195 .def_198)))
(let ((.def_204 (fp.add RNE .def_199 .def_203)))
(let ((.def_208 (fp.add RNE .def_204 .def_207)))
(let ((.def_212 (fp.add RNE .def_208 .def_211)))
(let ((.def_216 (fp.add RNE .def_212 .def_215)))
(let ((.def_217 (fp.leq .def_216 (fp #b1 #b01111110 #b11010010011011101001100))))
.def_217))))))))))))))))
(assert (let ((.def_250 (fp.mul RNE x6 (fp #b1 #b01111011 #b10000101000111101011100))))
(let ((.def_245 (fp.mul RNE x5 (fp #b0 #b01111101 #b10111001010110000001000))))
(let ((.def_241 (fp.mul RNE x4 (fp #b0 #b01111110 #b00000110001001001101111))))
(let ((.def_237 (fp.mul RNE x3 (fp #b1 #b01111101 #b01111001110110110010001))))
(let ((.def_232 (fp.mul RNE x2 (fp #b1 #b01111110 #b01011011101001011110010))))
(let ((.def_227 (fp.mul RNE x1 (fp #b0 #b01111110 #b11111111011111001110111))))
(let ((.def_223 (fp.mul RNE x0 (fp #b0 #b01111101 #b00001110010101100000010))))
(let ((.def_224 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_223)))
(let ((.def_228 (fp.add RNE .def_224 .def_227)))
(let ((.def_233 (fp.add RNE .def_228 .def_232)))
(let ((.def_238 (fp.add RNE .def_233 .def_237)))
(let ((.def_242 (fp.add RNE .def_238 .def_241)))
(let ((.def_246 (fp.add RNE .def_242 .def_245)))
(let ((.def_251 (fp.add RNE .def_246 .def_250)))
(let ((.def_252 (fp.leq .def_251 (fp #b1 #b01111101 #b00101101000011100101011))))
.def_252))))))))))))))))
(assert (let ((.def_286 (fp.mul RNE x6 (fp #b1 #b01111100 #b01100110011001100110011))))
(let ((.def_281 (fp.mul RNE x5 (fp #b1 #b01111110 #b01111101111100111011011))))
(let ((.def_276 (fp.mul RNE x4 (fp #b1 #b01111110 #b10000101000111101011100))))
(let ((.def_271 (fp.mul RNE x3 (fp #b0 #b01111110 #b01000111101011100001010))))
(let ((.def_267 (fp.mul RNE x2 (fp #b1 #b01111101 #b01000110101001111111000))))
(let ((.def_262 (fp.mul RNE x1 (fp #b1 #b01111110 #b11111011111001110110110))))
(let ((.def_257 (fp.mul RNE x0 (fp #b0 #b01111110 #b11000000000000000000000))))
(let ((.def_258 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_257)))
(let ((.def_263 (fp.add RNE .def_258 .def_262)))
(let ((.def_268 (fp.add RNE .def_263 .def_267)))
(let ((.def_272 (fp.add RNE .def_268 .def_271)))
(let ((.def_277 (fp.add RNE .def_272 .def_276)))
(let ((.def_282 (fp.add RNE .def_277 .def_281)))
(let ((.def_287 (fp.add RNE .def_282 .def_286)))
(let ((.def_288 (fp.leq (fp #b0 #b01111010 #b00010110100001110010110) .def_287)))
.def_288))))))))))))))))
(assert (let ((.def_322 (fp.mul RNE x6 (fp #b1 #b01111101 #b01011011001000101101000))))
(let ((.def_317 (fp.mul RNE x5 (fp #b0 #b01111100 #b01011010000111001010110))))
(let ((.def_313 (fp.mul RNE x4 (fp #b0 #b01111101 #b11111110111110011101110))))
(let ((.def_309 (fp.mul RNE x3 (fp #b1 #b01111101 #b10100000110001001001110))))
(let ((.def_304 (fp.mul RNE x2 (fp #b1 #b01111101 #b10011111101111100111011))))
(let ((.def_299 (fp.mul RNE x1 (fp #b1 #b01111110 #b00101001011110001101010))))
(let ((.def_294 (fp.mul RNE x0 (fp #b1 #b01111110 #b01011101101100100010111))))
(let ((.def_295 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_294)))
(let ((.def_300 (fp.add RNE .def_295 .def_299)))
(let ((.def_305 (fp.add RNE .def_300 .def_304)))
(let ((.def_310 (fp.add RNE .def_305 .def_309)))
(let ((.def_314 (fp.add RNE .def_310 .def_313)))
(let ((.def_318 (fp.add RNE .def_314 .def_317)))
(let ((.def_323 (fp.add RNE .def_318 .def_322)))
(let ((.def_324 (fp.leq .def_323 (fp #b0 #b01111110 #b00011100001010001111011))))
.def_324))))))))))))))))
(assert (let ((.def_357 (fp.mul RNE x6 (fp #b0 #b01111011 #b11100011010100111111100))))
(let ((.def_353 (fp.mul RNE x5 (fp #b0 #b01111110 #b00110000101000111101100))))
(let ((.def_349 (fp.mul RNE x4 (fp #b1 #b01111110 #b01001011110001101010100))))
(let ((.def_344 (fp.mul RNE x3 (fp #b0 #b01111100 #b00101011000000100000110))))
(let ((.def_340 (fp.mul RNE x2 (fp #b1 #b01111011 #b10101001111110111110100))))
(let ((.def_335 (fp.mul RNE x1 (fp #b1 #b01110111 #b10001001001101110100110))))
(let ((.def_330 (fp.mul RNE x0 (fp #b0 #b01111110 #b10101011100001010001111))))
(let ((.def_331 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_330)))
(let ((.def_336 (fp.add RNE .def_331 .def_335)))
(let ((.def_341 (fp.add RNE .def_336 .def_340)))
(let ((.def_345 (fp.add RNE .def_341 .def_344)))
(let ((.def_350 (fp.add RNE .def_345 .def_349)))
(let ((.def_354 (fp.add RNE .def_350 .def_353)))
(let ((.def_358 (fp.add RNE .def_354 .def_357)))
(let ((.def_359 (fp.leq (fp #b1 #b01111110 #b10100011110101110000101) .def_358)))
.def_359))))))))))))))))
(assert (let ((.def_392 (fp.mul RNE x6 (fp #b0 #b01111100 #b10000111001010110000001))))
(let ((.def_388 (fp.mul RNE x5 (fp #b1 #b01111100 #b10101001111110111110100))))
(let ((.def_383 (fp.mul RNE x4 (fp #b1 #b01111110 #b10110000001000001100010))))
(let ((.def_378 (fp.mul RNE x3 (fp #b0 #b01111110 #b10010011111101111100111))))
(let ((.def_374 (fp.mul RNE x2 (fp #b0 #b01111110 #b10100101111000110101010))))
(let ((.def_370 (fp.mul RNE x1 (fp #b1 #b01111110 #b01001101010011111110000))))
(let ((.def_365 (fp.mul RNE x0 (fp #b0 #b01111100 #b00010010011011101001100))))
(let ((.def_366 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_365)))
(let ((.def_371 (fp.add RNE .def_366 .def_370)))
(let ((.def_375 (fp.add RNE .def_371 .def_374)))
(let ((.def_379 (fp.add RNE .def_375 .def_378)))
(let ((.def_384 (fp.add RNE .def_379 .def_383)))
(let ((.def_389 (fp.add RNE .def_384 .def_388)))
(let ((.def_393 (fp.add RNE .def_389 .def_392)))
(let ((.def_394 (fp.leq (fp #b1 #b01111110 #b00100000110001001001110) .def_393)))
.def_394))))))))))))))))
(assert (let ((.def_427 (fp.mul RNE x6 (fp #b0 #b01111110 #b10110001101010011111110))))
(let ((.def_423 (fp.mul RNE x5 (fp #b1 #b01111110 #b00111010111000010100100))))
(let ((.def_418 (fp.mul RNE x4 (fp #b1 #b01111101 #b11000010100011110101110))))
(let ((.def_413 (fp.mul RNE x3 (fp #b0 #b01111101 #b11101110100101111000111))))
(let ((.def_409 (fp.mul RNE x2 (fp #b1 #b01111110 #b00010110100001110010110))))
(let ((.def_404 (fp.mul RNE x1 (fp #b1 #b01111101 #b11010000111001010110000))))
(let ((.def_399 (fp.mul RNE x0 (fp #b0 #b01111100 #b11111001110110110010001))))
(let ((.def_400 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_399)))
(let ((.def_405 (fp.add RNE .def_400 .def_404)))
(let ((.def_410 (fp.add RNE .def_405 .def_409)))
(let ((.def_414 (fp.add RNE .def_410 .def_413)))
(let ((.def_419 (fp.add RNE .def_414 .def_418)))
(let ((.def_424 (fp.add RNE .def_419 .def_423)))
(let ((.def_428 (fp.add RNE .def_424 .def_427)))
(let ((.def_429 (fp.leq .def_428 (fp #b0 #b01111101 #b10100011110101110000101))))
.def_429))))))))))))))))
(assert (let ((.def_461 (fp.mul RNE x6 (fp #b0 #b01111100 #b11010000111001010110000))))
(let ((.def_457 (fp.mul RNE x5 (fp #b1 #b01111110 #b11111101011100001010010))))
(let ((.def_452 (fp.mul RNE x4 (fp #b1 #b01111110 #b01011000100100110111010))))
(let ((.def_447 (fp.mul RNE x3 (fp #b1 #b01111110 #b01110001101010011111110))))
(let ((.def_442 (fp.mul RNE x2 (fp #b0 #b01111110 #b01111101011100001010010))))
(let ((.def_440 (fp.mul RNE x1 (fp #b0 #b01111110 #b01001001001101110100110))))
(let ((.def_436 (fp.mul RNE x0 (fp #b1 #b01111110 #b00100110111010010111100))))
(let ((.def_437 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_436)))
(let ((.def_441 (fp.add RNE .def_437 .def_440)))
(let ((.def_443 (fp.add RNE .def_441 .def_442)))
(let ((.def_448 (fp.add RNE .def_443 .def_447)))
(let ((.def_453 (fp.add RNE .def_448 .def_452)))
(let ((.def_458 (fp.add RNE .def_453 .def_457)))
(let ((.def_462 (fp.add RNE .def_458 .def_461)))
(let ((.def_463 (fp.leq .def_462 (fp #b1 #b01111100 #b10111100011010100111111))))
.def_463))))))))))))))))
(check-sat)
