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
(assert (let ((.def_78 (fp.mul RNE x6 (fp #b0 #b01111110 #b01101110100101111000111))))
(let ((.def_74 (fp.mul RNE x5 (fp #b1 #b01111110 #b11000111001010110000001))))
(let ((.def_69 (fp.mul RNE x4 (fp #b1 #b01111110 #b01110100101111000110101))))
(let ((.def_64 (fp.mul RNE x3 (fp #b0 #b01111110 #b11010011011101001011110))))
(let ((.def_60 (fp.mul RNE x2 (fp #b1 #b01111110 #b10001100110011001100110))))
(let ((.def_55 (fp.mul RNE x1 (fp #b0 #b01111101 #b00100100110111010011000))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111000 #b01000111101011100001010))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_56 (fp.add RNE .def_52 .def_55)))
(let ((.def_61 (fp.add RNE .def_56 .def_60)))
(let ((.def_65 (fp.add RNE .def_61 .def_64)))
(let ((.def_70 (fp.add RNE .def_65 .def_69)))
(let ((.def_75 (fp.add RNE .def_70 .def_74)))
(let ((.def_79 (fp.add RNE .def_75 .def_78)))
(let ((.def_80 (fp.leq (fp #b1 #b01111110 #b11110111110011101101101) .def_79)))
.def_80))))))))))))))))
(assert (let ((.def_113 (fp.mul RNE x6 (fp #b0 #b01111110 #b01011101001011110001101))))
(let ((.def_109 (fp.mul RNE x5 (fp #b1 #b01111110 #b00110100101111000110101))))
(let ((.def_104 (fp.mul RNE x4 (fp #b0 #b01111100 #b10111110011101101100100))))
(let ((.def_100 (fp.mul RNE x3 (fp #b0 #b01111101 #b00001011010000111001011))))
(let ((.def_96 (fp.mul RNE x2 (fp #b1 #b01111101 #b01010111000010100011111))))
(let ((.def_91 (fp.mul RNE x1 (fp #b0 #b01111100 #b01011010000111001010110))))
(let ((.def_87 (fp.mul RNE x0 (fp #b1 #b01111011 #b01001011110001101010100))))
(let ((.def_88 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_87)))
(let ((.def_92 (fp.add RNE .def_88 .def_91)))
(let ((.def_97 (fp.add RNE .def_92 .def_96)))
(let ((.def_101 (fp.add RNE .def_97 .def_100)))
(let ((.def_105 (fp.add RNE .def_101 .def_104)))
(let ((.def_110 (fp.add RNE .def_105 .def_109)))
(let ((.def_114 (fp.add RNE .def_110 .def_113)))
(let ((.def_115 (fp.leq (fp #b1 #b01111100 #b01111010111000010100100) .def_114)))
.def_115))))))))))))))))
(assert (let ((.def_150 (fp.mul RNE x6 (fp #b1 #b01111101 #b11110100101111000110101))))
(let ((.def_145 (fp.mul RNE x5 (fp #b1 #b01111011 #b01101000011100101011000))))
(let ((.def_140 (fp.mul RNE x4 (fp #b1 #b01111110 #b00011010000111001010110))))
(let ((.def_135 (fp.mul RNE x3 (fp #b0 #b01111110 #b10100000010000011000101))))
(let ((.def_131 (fp.mul RNE x2 (fp #b1 #b01111110 #b01101011100001010001111))))
(let ((.def_126 (fp.mul RNE x1 (fp #b1 #b01111011 #b01100000010000011000101))))
(let ((.def_121 (fp.mul RNE x0 (fp #b0 #b01111110 #b01010001111010111000011))))
(let ((.def_122 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_121)))
(let ((.def_127 (fp.add RNE .def_122 .def_126)))
(let ((.def_132 (fp.add RNE .def_127 .def_131)))
(let ((.def_136 (fp.add RNE .def_132 .def_135)))
(let ((.def_141 (fp.add RNE .def_136 .def_140)))
(let ((.def_146 (fp.add RNE .def_141 .def_145)))
(let ((.def_151 (fp.add RNE .def_146 .def_150)))
(let ((.def_152 (fp.leq .def_151 (fp #b1 #b01111101 #b01111010111000010100100))))
.def_152))))))))))))))))
(assert (let ((.def_183 (fp.mul RNE x6 (fp #b0 #b01111110 #b11100011110101110000101))))
(let ((.def_179 (fp.mul RNE x5 (fp #b0 #b01111110 #b11101100000010000011001))))
(let ((.def_175 (fp.mul RNE x4 (fp #b1 #b01111110 #b11010110000001000001100))))
(let ((.def_170 (fp.mul RNE x3 (fp #b1 #b01111110 #b00110100001110010101100))))
(let ((.def_165 (fp.mul RNE x2 (fp #b1 #b01111101 #b01110010101100000010000))))
(let ((.def_160 (fp.mul RNE x1 (fp #b1 #b01111100 #b10011101101100100010111))))
(let ((.def_155 (fp.mul RNE x0 (fp #b0 #b01111101 #b01010111000010100011111))))
(let ((.def_156 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_155)))
(let ((.def_161 (fp.add RNE .def_156 .def_160)))
(let ((.def_166 (fp.add RNE .def_161 .def_165)))
(let ((.def_171 (fp.add RNE .def_166 .def_170)))
(let ((.def_176 (fp.add RNE .def_171 .def_175)))
(let ((.def_180 (fp.add RNE .def_176 .def_179)))
(let ((.def_184 (fp.add RNE .def_180 .def_183)))
(let ((.def_185 (fp.leq (fp #b0 #b01111110 #b10101111100111011011001) .def_184)))
.def_185))))))))))))))))
(assert (let ((.def_220 (fp.mul RNE x6 (fp #b1 #b01111101 #b00001100010010011011101))))
(let ((.def_215 (fp.mul RNE x5 (fp #b1 #b01111110 #b11100001110010101100000))))
(let ((.def_210 (fp.mul RNE x4 (fp #b0 #b01111110 #b11011001000101101000100))))
(let ((.def_206 (fp.mul RNE x3 (fp #b0 #b01111101 #b01100000010000011000101))))
(let ((.def_202 (fp.mul RNE x2 (fp #b1 #b01111110 #b00001100110011001100110))))
(let ((.def_197 (fp.mul RNE x1 (fp #b1 #b01111011 #b01001111110111110011110))))
(let ((.def_192 (fp.mul RNE x0 (fp #b1 #b01111110 #b11111001110110110010001))))
(let ((.def_193 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_192)))
(let ((.def_198 (fp.add RNE .def_193 .def_197)))
(let ((.def_203 (fp.add RNE .def_198 .def_202)))
(let ((.def_207 (fp.add RNE .def_203 .def_206)))
(let ((.def_211 (fp.add RNE .def_207 .def_210)))
(let ((.def_216 (fp.add RNE .def_211 .def_215)))
(let ((.def_221 (fp.add RNE .def_216 .def_220)))
(let ((.def_222 (fp.leq .def_221 (fp #b1 #b01111101 #b01000111101011100001010))))
.def_222))))))))))))))))
(assert (let ((.def_250 (fp.mul RNE x6 (fp #b1 #b01111110 #b11011100101011000000100))))
(let ((.def_244 (fp.mul RNE x4 (fp #b1 #b01110111 #b00000110001001001101111))))
(let ((.def_239 (fp.mul RNE x3 (fp #b1 #b01111011 #b00000010000011000100101))))
(let ((.def_234 (fp.mul RNE x2 (fp #b0 #b01111101 #b00101100000010000011001))))
(let ((.def_230 (fp.mul RNE x1 (fp #b0 #b01111101 #b01000010100011110101110))))
(let ((.def_226 (fp.mul RNE x0 (fp #b1 #b01111110 #b11110111010010111100011))))
(let ((.def_227 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_226)))
(let ((.def_231 (fp.add RNE .def_227 .def_230)))
(let ((.def_235 (fp.add RNE .def_231 .def_234)))
(let ((.def_240 (fp.add RNE .def_235 .def_239)))
(let ((.def_245 (fp.add RNE .def_240 .def_244)))
(let ((.def_109 (fp.mul RNE x5 (fp #b1 #b01111110 #b00110100101111000110101))))
(let ((.def_246 (fp.add RNE .def_109 .def_245)))
(let ((.def_251 (fp.add RNE .def_246 .def_250)))
(let ((.def_252 (fp.leq (fp #b1 #b01111101 #b11110100101111000110101) .def_251)))
.def_252))))))))))))))))
(assert (let ((.def_284 (fp.mul RNE x6 (fp #b0 #b01111100 #b11011001000101101000100))))
(let ((.def_280 (fp.mul RNE x5 (fp #b1 #b01111100 #b11001100110011001100110))))
(let ((.def_275 (fp.mul RNE x4 (fp #b0 #b01111110 #b10011011101001011110010))))
(let ((.def_271 (fp.mul RNE x3 (fp #b1 #b01111110 #b00001101010011111110000))))
(let ((.def_266 (fp.mul RNE x2 (fp #b1 #b01111011 #b11010111000010100011111))))
(let ((.def_261 (fp.mul RNE x1 (fp #b0 #b01111110 #b00100111011011001000110))))
(let ((.def_257 (fp.mul RNE x0 (fp #b0 #b01111001 #b10001001001101110100110))))
(let ((.def_258 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_257)))
(let ((.def_262 (fp.add RNE .def_258 .def_261)))
(let ((.def_267 (fp.add RNE .def_262 .def_266)))
(let ((.def_272 (fp.add RNE .def_267 .def_271)))
(let ((.def_276 (fp.add RNE .def_272 .def_275)))
(let ((.def_281 (fp.add RNE .def_276 .def_280)))
(let ((.def_285 (fp.add RNE .def_281 .def_284)))
(let ((.def_286 (fp.leq (fp #b0 #b01111101 #b00001001001101110100110) .def_285)))
.def_286))))))))))))))))
(assert (let ((.def_315 (fp.mul RNE x6 (fp #b1 #b01111110 #b00000011100101011000001))))
(let ((.def_310 (fp.mul RNE x5 (fp #b1 #b01111110 #b00001111010111000010100))))
(let ((.def_305 (fp.mul RNE x4 (fp #b0 #b01111001 #b10011001100110011001101))))
(let ((.def_300 (fp.mul RNE x2 (fp #b0 #b01111001 #b11101011100001010001111))))
(let ((.def_296 (fp.mul RNE x1 (fp #b1 #b01111110 #b01001001101110100101111))))
(let ((.def_291 (fp.mul RNE x0 (fp #b0 #b01111100 #b11101111100111011011001))))
(let ((.def_292 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_291)))
(let ((.def_297 (fp.add RNE .def_292 .def_296)))
(let ((.def_301 (fp.add RNE .def_297 .def_300)))
(let ((.def_239 (fp.mul RNE x3 (fp #b1 #b01111011 #b00000010000011000100101))))
(let ((.def_302 (fp.add RNE .def_239 .def_301)))
(let ((.def_306 (fp.add RNE .def_302 .def_305)))
(let ((.def_311 (fp.add RNE .def_306 .def_310)))
(let ((.def_316 (fp.add RNE .def_311 .def_315)))
(let ((.def_317 (fp.leq (fp #b0 #b01111101 #b00100011110101110000101) .def_316)))
.def_317))))))))))))))))
(assert (let ((.def_345 (fp.mul RNE x6 (fp #b1 #b01111100 #b10110010001011010000111))))
(let ((.def_340 (fp.mul RNE x5 (fp #b0 #b01111110 #b11010001111010111000011))))
(let ((.def_336 (fp.mul RNE x4 (fp #b0 #b01111100 #b00110101001111110111110))))
(let ((.def_332 (fp.mul RNE x3 (fp #b1 #b01111110 #b01101110100101111000111))))
(let ((.def_329 (fp.mul RNE x2 (fp #b1 #b01111100 #b11111001110110110010001))))
(let ((.def_324 (fp.mul RNE x1 (fp #b0 #b01111110 #b01010001111010111000011))))
(let ((.def_322 (fp.mul RNE x0 (fp #b0 #b01111101 #b10010000011000100100111))))
(let ((.def_323 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_322)))
(let ((.def_325 (fp.add RNE .def_323 .def_324)))
(let ((.def_330 (fp.add RNE .def_325 .def_329)))
(let ((.def_333 (fp.add RNE .def_330 .def_332)))
(let ((.def_337 (fp.add RNE .def_333 .def_336)))
(let ((.def_341 (fp.add RNE .def_337 .def_340)))
(let ((.def_346 (fp.add RNE .def_341 .def_345)))
(let ((.def_347 (fp.leq .def_346 (fp #b0 #b01111110 #b01100011110101110000101))))
.def_347))))))))))))))))
(assert (let ((.def_374 (fp.mul RNE x6 (fp #b0 #b01111011 #b10000101000111101011100))))
(let ((.def_370 (fp.mul RNE x5 (fp #b0 #b01111101 #b10011110101110000101001))))
(let ((.def_366 (fp.mul RNE x4 (fp #b1 #b01111110 #b10010011111101111100111))))
(let ((.def_361 (fp.mul RNE x3 (fp #b1 #b01111110 #b00101111100111011011001))))
(let ((.def_356 (fp.mul RNE x2 (fp #b1 #b01111100 #b01111010111000010100100))))
(let ((.def_354 (fp.mul RNE x1 (fp #b1 #b01111110 #b01111101011100001010010))))
(let ((.def_349 (fp.mul RNE x0 (fp #b1 #b01111110 #b01010001111010111000011))))
(let ((.def_350 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_349)))
(let ((.def_355 (fp.add RNE .def_350 .def_354)))
(let ((.def_357 (fp.add RNE .def_355 .def_356)))
(let ((.def_362 (fp.add RNE .def_357 .def_361)))
(let ((.def_367 (fp.add RNE .def_362 .def_366)))
(let ((.def_371 (fp.add RNE .def_367 .def_370)))
(let ((.def_375 (fp.add RNE .def_371 .def_374)))
(let ((.def_376 (fp.leq (fp #b0 #b01111001 #b10001001001101110100110) .def_375)))
.def_376))))))))))))))))
(assert (let ((.def_407 (fp.mul RNE x6 (fp #b0 #b01111101 #b11011101001011110001101))))
(let ((.def_403 (fp.mul RNE x5 (fp #b1 #b01111110 #b01011011101001011110010))))
(let ((.def_398 (fp.mul RNE x4 (fp #b0 #b01110111 #b10001001001101110100110))))
(let ((.def_394 (fp.mul RNE x3 (fp #b0 #b01111110 #b10010100011110101110001))))
(let ((.def_390 (fp.mul RNE x2 (fp #b0 #b01111101 #b00110110010001011010001))))
(let ((.def_386 (fp.mul RNE x1 (fp #b0 #b01111101 #b01110100101111000110101))))
(let ((.def_382 (fp.mul RNE x0 (fp #b1 #b01111101 #b10110010001011010000111))))
(let ((.def_383 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_382)))
(let ((.def_387 (fp.add RNE .def_383 .def_386)))
(let ((.def_391 (fp.add RNE .def_387 .def_390)))
(let ((.def_395 (fp.add RNE .def_391 .def_394)))
(let ((.def_399 (fp.add RNE .def_395 .def_398)))
(let ((.def_404 (fp.add RNE .def_399 .def_403)))
(let ((.def_408 (fp.add RNE .def_404 .def_407)))
(let ((.def_409 (fp.leq (fp #b0 #b01111100 #b00111011011001000101101) .def_408)))
.def_409))))))))))))))))
(assert (let ((.def_445 (fp.mul RNE x6 (fp #b1 #b01111011 #b01011100001010001111011))))
(let ((.def_440 (fp.mul RNE x5 (fp #b0 #b01111110 #b10000100000110001001010))))
(let ((.def_436 (fp.mul RNE x4 (fp #b1 #b01111110 #b10010100111111011111010))))
(let ((.def_431 (fp.mul RNE x3 (fp #b1 #b01111101 #b10010101100000010000011))))
(let ((.def_426 (fp.mul RNE x2 (fp #b1 #b01111110 #b01001010110000001000010))))
(let ((.def_421 (fp.mul RNE x1 (fp #b1 #b01111100 #b00011000100100110111010))))
(let ((.def_416 (fp.mul RNE x0 (fp #b1 #b01111110 #b00001100010010011011101))))
(let ((.def_417 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_416)))
(let ((.def_422 (fp.add RNE .def_417 .def_421)))
(let ((.def_427 (fp.add RNE .def_422 .def_426)))
(let ((.def_432 (fp.add RNE .def_427 .def_431)))
(let ((.def_437 (fp.add RNE .def_432 .def_436)))
(let ((.def_441 (fp.add RNE .def_437 .def_440)))
(let ((.def_446 (fp.add RNE .def_441 .def_445)))
(let ((.def_447 (fp.leq (fp #b1 #b01111110 #b11101011100001010001111) .def_446)))
.def_447))))))))))))))))
(check-sat)
