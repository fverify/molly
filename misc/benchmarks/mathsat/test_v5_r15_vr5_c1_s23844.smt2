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
(assert (let ((.def_60 (fp.mul RNE x4 (fp #b1 #b01111110 #b00001100110011001100110))))
(let ((.def_55 (fp.mul RNE x3 (fp #b0 #b01111001 #b00100110111010010111100))))
(let ((.def_51 (fp.mul RNE x2 (fp #b0 #b01111110 #b11110111110011101101101))))
(let ((.def_47 (fp.mul RNE x1 (fp #b0 #b01111110 #b01011011101001011110010))))
(let ((.def_43 (fp.mul RNE x0 (fp #b1 #b01111100 #b11101011100001010001111))))
(let ((.def_44 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_43)))
(let ((.def_48 (fp.add RNE .def_44 .def_47)))
(let ((.def_52 (fp.add RNE .def_48 .def_51)))
(let ((.def_56 (fp.add RNE .def_52 .def_55)))
(let ((.def_61 (fp.add RNE .def_56 .def_60)))
(let ((.def_62 (fp.leq .def_61 (fp #b0 #b01111110 #b11100001010001111010111))))
.def_62))))))))))))
(assert (let ((.def_86 (fp.mul RNE x4 (fp #b0 #b01111001 #b01111000110101001111111))))
(let ((.def_82 (fp.mul RNE x3 (fp #b1 #b01111100 #b10000011000100100110111))))
(let ((.def_77 (fp.mul RNE x2 (fp #b1 #b01111110 #b11000101101000011100101))))
(let ((.def_72 (fp.mul RNE x1 (fp #b0 #b01111101 #b10111100011010100111111))))
(let ((.def_68 (fp.mul RNE x0 (fp #b0 #b01111101 #b00100101111000110101010))))
(let ((.def_69 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_68)))
(let ((.def_73 (fp.add RNE .def_69 .def_72)))
(let ((.def_78 (fp.add RNE .def_73 .def_77)))
(let ((.def_83 (fp.add RNE .def_78 .def_82)))
(let ((.def_87 (fp.add RNE .def_83 .def_86)))
(let ((.def_88 (fp.leq (fp #b1 #b01111110 #b10111010010111100011011) .def_87)))
.def_88))))))))))))
(assert (let ((.def_113 (fp.mul RNE x4 (fp #b0 #b01111011 #b11101111100111011011001))))
(let ((.def_109 (fp.mul RNE x3 (fp #b1 #b01111101 #b00011010100111111011111))))
(let ((.def_104 (fp.mul RNE x2 (fp #b1 #b01111101 #b10101111000110101010000))))
(let ((.def_99 (fp.mul RNE x1 (fp #b1 #b01111110 #b11110000001000001100010))))
(let ((.def_94 (fp.mul RNE x0 (fp #b0 #b01111000 #b10001001001101110100110))))
(let ((.def_95 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_94)))
(let ((.def_100 (fp.add RNE .def_95 .def_99)))
(let ((.def_105 (fp.add RNE .def_100 .def_104)))
(let ((.def_110 (fp.add RNE .def_105 .def_109)))
(let ((.def_114 (fp.add RNE .def_110 .def_113)))
(let ((.def_115 (fp.leq (fp #b1 #b01111100 #b10000101000111101011100) .def_114)))
.def_115))))))))))))
(assert (let ((.def_139 (fp.mul RNE x4 (fp #b1 #b01111101 #b01001011110001101010100))))
(let ((.def_134 (fp.mul RNE x3 (fp #b1 #b01111110 #b01110110110010001011010))))
(let ((.def_129 (fp.mul RNE x2 (fp #b0 #b01111101 #b10000001000001100010010))))
(let ((.def_125 (fp.mul RNE x1 (fp #b1 #b01111101 #b01111101111100111011011))))
(let ((.def_120 (fp.mul RNE x0 (fp #b0 #b01111110 #b00101110100101111000111))))
(let ((.def_121 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_120)))
(let ((.def_126 (fp.add RNE .def_121 .def_125)))
(let ((.def_130 (fp.add RNE .def_126 .def_129)))
(let ((.def_135 (fp.add RNE .def_130 .def_134)))
(let ((.def_140 (fp.add RNE .def_135 .def_139)))
(let ((.def_141 (fp.leq .def_140 (fp #b0 #b01111101 #b10101011000000100000110))))
.def_141))))))))))))
(assert (let ((.def_164 (fp.mul RNE x4 (fp #b1 #b01111110 #b11111001010110000001000))))
(let ((.def_159 (fp.mul RNE x3 (fp #b1 #b01111010 #b00000110001001001101111))))
(let ((.def_154 (fp.mul RNE x2 (fp #b0 #b01111110 #b11101100000010000011001))))
(let ((.def_150 (fp.mul RNE x1 (fp #b0 #b01111110 #b00100111011011001000110))))
(let ((.def_146 (fp.mul RNE x0 (fp #b0 #b01111000 #b01101000011100101011000))))
(let ((.def_147 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_146)))
(let ((.def_151 (fp.add RNE .def_147 .def_150)))
(let ((.def_155 (fp.add RNE .def_151 .def_154)))
(let ((.def_160 (fp.add RNE .def_155 .def_159)))
(let ((.def_165 (fp.add RNE .def_160 .def_164)))
(let ((.def_166 (fp.leq .def_165 (fp #b0 #b01111101 #b11110011101101100100011))))
.def_166))))))))))))
(assert (let ((.def_191 (fp.mul RNE x4 (fp #b0 #b01111101 #b11011110001101010100000))))
(let ((.def_187 (fp.mul RNE x3 (fp #b1 #b01111110 #b11110011001100110011010))))
(let ((.def_182 (fp.mul RNE x2 (fp #b0 #b01111110 #b10011010100111111011111))))
(let ((.def_178 (fp.mul RNE x1 (fp #b1 #b01111110 #b00001011010000111001011))))
(let ((.def_173 (fp.mul RNE x0 (fp #b1 #b01111110 #b11101101000011100101011))))
(let ((.def_174 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_173)))
(let ((.def_179 (fp.add RNE .def_174 .def_178)))
(let ((.def_183 (fp.add RNE .def_179 .def_182)))
(let ((.def_188 (fp.add RNE .def_183 .def_187)))
(let ((.def_192 (fp.add RNE .def_188 .def_191)))
(let ((.def_193 (fp.leq .def_192 (fp #b1 #b01111110 #b11011001100110011001101))))
.def_193))))))))))))
(assert (let ((.def_217 (fp.mul RNE x4 (fp #b0 #b01111110 #b11111100011010100111111))))
(let ((.def_213 (fp.mul RNE x3 (fp #b1 #b01111110 #b00000100000110001001010))))
(let ((.def_208 (fp.mul RNE x2 (fp #b0 #b01111101 #b01001000101101000011101))))
(let ((.def_204 (fp.mul RNE x1 (fp #b1 #b01111110 #b00111110011101101100100))))
(let ((.def_199 (fp.mul RNE x0 (fp #b0 #b01111110 #b11110100101111000110101))))
(let ((.def_200 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_199)))
(let ((.def_205 (fp.add RNE .def_200 .def_204)))
(let ((.def_209 (fp.add RNE .def_205 .def_208)))
(let ((.def_214 (fp.add RNE .def_209 .def_213)))
(let ((.def_218 (fp.add RNE .def_214 .def_217)))
(let ((.def_219 (fp.leq .def_218 (fp #b1 #b01111011 #b00010010011011101001100))))
.def_219))))))))))))
(assert (let ((.def_242 (fp.mul RNE x4 (fp #b1 #b01111000 #b11101011100001010001111))))
(let ((.def_237 (fp.mul RNE x3 (fp #b1 #b01111100 #b11111001110110110010001))))
(let ((.def_232 (fp.mul RNE x2 (fp #b0 #b01111101 #b01111100111011011001001))))
(let ((.def_228 (fp.mul RNE x1 (fp #b0 #b01111110 #b11001111010111000010100))))
(let ((.def_224 (fp.mul RNE x0 (fp #b0 #b01111110 #b00110011001100110011010))))
(let ((.def_225 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_224)))
(let ((.def_229 (fp.add RNE .def_225 .def_228)))
(let ((.def_233 (fp.add RNE .def_229 .def_232)))
(let ((.def_238 (fp.add RNE .def_233 .def_237)))
(let ((.def_243 (fp.add RNE .def_238 .def_242)))
(let ((.def_244 (fp.leq .def_243 (fp #b0 #b01111110 #b00111110111110011101110))))
.def_244))))))))))))
(assert (let ((.def_269 (fp.mul RNE x4 (fp #b1 #b01111110 #b10111001010110000001000))))
(let ((.def_264 (fp.mul RNE x3 (fp #b1 #b01111100 #b10110110010001011010001))))
(let ((.def_259 (fp.mul RNE x2 (fp #b1 #b01111110 #b11100011110101110000101))))
(let ((.def_254 (fp.mul RNE x1 (fp #b1 #b01111101 #b01000101101000011100101))))
(let ((.def_249 (fp.mul RNE x0 (fp #b0 #b01111101 #b10110101001111110111110))))
(let ((.def_250 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_249)))
(let ((.def_255 (fp.add RNE .def_250 .def_254)))
(let ((.def_260 (fp.add RNE .def_255 .def_259)))
(let ((.def_265 (fp.add RNE .def_260 .def_264)))
(let ((.def_270 (fp.add RNE .def_265 .def_269)))
(let ((.def_271 (fp.leq (fp #b0 #b01111110 #b11111011111001110110110) .def_270)))
.def_271))))))))))))
(assert (let ((.def_294 (fp.mul RNE x4 (fp #b0 #b01111100 #b00010000011000100100111))))
(let ((.def_290 (fp.mul RNE x3 (fp #b1 #b01111110 #b11000000100000110001001))))
(let ((.def_285 (fp.mul RNE x2 (fp #b1 #b01111100 #b01011110001101010100000))))
(let ((.def_280 (fp.mul RNE x1 (fp #b0 #b01111110 #b01100101011000000100001))))
(let ((.def_276 (fp.mul RNE x0 (fp #b0 #b01111110 #b11000110001001001101111))))
(let ((.def_277 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_276)))
(let ((.def_281 (fp.add RNE .def_277 .def_280)))
(let ((.def_286 (fp.add RNE .def_281 .def_285)))
(let ((.def_291 (fp.add RNE .def_286 .def_290)))
(let ((.def_295 (fp.add RNE .def_291 .def_294)))
(let ((.def_296 (fp.leq .def_295 (fp #b0 #b01111101 #b01111000110101001111111))))
.def_296))))))))))))
(assert (let ((.def_322 (fp.mul RNE x4 (fp #b1 #b01111100 #b00111101011100001010010))))
(let ((.def_317 (fp.mul RNE x3 (fp #b1 #b01111110 #b10100110111010010111100))))
(let ((.def_312 (fp.mul RNE x2 (fp #b0 #b01111100 #b11000000100000110001001))))
(let ((.def_308 (fp.mul RNE x1 (fp #b1 #b01111101 #b10000010000011000100101))))
(let ((.def_303 (fp.mul RNE x0 (fp #b1 #b01111110 #b10000001000001100010010))))
(let ((.def_304 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_303)))
(let ((.def_309 (fp.add RNE .def_304 .def_308)))
(let ((.def_313 (fp.add RNE .def_309 .def_312)))
(let ((.def_318 (fp.add RNE .def_313 .def_317)))
(let ((.def_323 (fp.add RNE .def_318 .def_322)))
(let ((.def_324 (fp.leq .def_323 (fp #b1 #b01111101 #b11001010110000001000010))))
.def_324))))))))))))
(assert (let ((.def_345 (fp.mul RNE x4 (fp #b0 #b01111101 #b01111100111011011001001))))
(let ((.def_343 (fp.mul RNE x3 (fp #b1 #b01111101 #b01011001000101101000100))))
(let ((.def_338 (fp.mul RNE x2 (fp #b0 #b01110111 #b11001010110000001000010))))
(let ((.def_334 (fp.mul RNE x1 (fp #b0 #b01111101 #b00001010001111010111000))))
(let ((.def_330 (fp.mul RNE x0 (fp #b0 #b01111110 #b11001000101101000011101))))
(let ((.def_331 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_330)))
(let ((.def_335 (fp.add RNE .def_331 .def_334)))
(let ((.def_339 (fp.add RNE .def_335 .def_338)))
(let ((.def_344 (fp.add RNE .def_339 .def_343)))
(let ((.def_346 (fp.add RNE .def_344 .def_345)))
(let ((.def_347 (fp.leq (fp #b1 #b01111110 #b11001110110110010001011) .def_346)))
.def_347))))))))))))
(assert (let ((.def_370 (fp.mul RNE x4 (fp #b0 #b01111101 #b11000111101011100001010))))
(let ((.def_366 (fp.mul RNE x3 (fp #b1 #b01111101 #b01010110000001000001100))))
(let ((.def_361 (fp.mul RNE x2 (fp #b0 #b01111110 #b01010011011101001011110))))
(let ((.def_357 (fp.mul RNE x1 (fp #b1 #b01111101 #b01000111101011100001010))))
(let ((.def_352 (fp.mul RNE x0 (fp #b0 #b01111101 #b00011111101111100111011))))
(let ((.def_353 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_352)))
(let ((.def_358 (fp.add RNE .def_353 .def_357)))
(let ((.def_362 (fp.add RNE .def_358 .def_361)))
(let ((.def_367 (fp.add RNE .def_362 .def_366)))
(let ((.def_371 (fp.add RNE .def_367 .def_370)))
(let ((.def_372 (fp.leq .def_371 (fp #b0 #b01111110 #b00100110111010010111100))))
.def_372))))))))))))
(assert (let ((.def_394 (fp.mul RNE x4 (fp #b0 #b01111101 #b01110111110011101101101))))
(let ((.def_390 (fp.mul RNE x3 (fp #b0 #b01111101 #b01111110111110011101110))))
(let ((.def_386 (fp.mul RNE x2 (fp #b0 #b01111110 #b10001101010011111110000))))
(let ((.def_382 (fp.mul RNE x1 (fp #b0 #b01111110 #b01011011001000101101000))))
(let ((.def_378 (fp.mul RNE x0 (fp #b1 #b01111110 #b01111100011010100111111))))
(let ((.def_379 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_378)))
(let ((.def_383 (fp.add RNE .def_379 .def_382)))
(let ((.def_387 (fp.add RNE .def_383 .def_386)))
(let ((.def_391 (fp.add RNE .def_387 .def_390)))
(let ((.def_395 (fp.add RNE .def_391 .def_394)))
(let ((.def_396 (fp.leq (fp #b0 #b01111100 #b11110001101010011111110) .def_395)))
.def_396))))))))))))
(assert (let ((.def_416 (fp.mul RNE x4 (fp #b0 #b01111100 #b01100010010011011101001))))
(let ((.def_412 (fp.mul RNE x3 (fp #b0 #b01111000 #b01000111101011100001010))))
(let ((.def_408 (fp.mul RNE x2 (fp #b0 #b01111110 #b00101110100101111000111))))
(let ((.def_406 (fp.mul RNE x1 (fp #b1 #b01111110 #b10010000011000100100111))))
(let ((.def_401 (fp.mul RNE x0 (fp #b1 #b01111110 #b00100110111010010111100))))
(let ((.def_402 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_401)))
(let ((.def_407 (fp.add RNE .def_402 .def_406)))
(let ((.def_409 (fp.add RNE .def_407 .def_408)))
(let ((.def_413 (fp.add RNE .def_409 .def_412)))
(let ((.def_417 (fp.add RNE .def_413 .def_416)))
(let ((.def_418 (fp.leq (fp #b1 #b01111010 #b10010001011010000111001) .def_417)))
.def_418))))))))))))
(check-sat)