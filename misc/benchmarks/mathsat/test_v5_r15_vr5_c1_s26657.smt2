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
(assert (let ((.def_61 (fp.mul RNE x4 (fp #b0 #b01111110 #b11011011001000101101000))))
(let ((.def_57 (fp.mul RNE x3 (fp #b0 #b01111110 #b11100001110010101100000))))
(let ((.def_53 (fp.mul RNE x2 (fp #b0 #b01111101 #b11111110111110011101110))))
(let ((.def_49 (fp.mul RNE x1 (fp #b1 #b01111110 #b01110001001001101110101))))
(let ((.def_44 (fp.mul RNE x0 (fp #b1 #b01111001 #b10101001111110111110100))))
(let ((.def_45 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_44)))
(let ((.def_50 (fp.add RNE .def_45 .def_49)))
(let ((.def_54 (fp.add RNE .def_50 .def_53)))
(let ((.def_58 (fp.add RNE .def_54 .def_57)))
(let ((.def_62 (fp.add RNE .def_58 .def_61)))
(let ((.def_63 (fp.leq (fp #b1 #b01111110 #b00000100000110001001010) .def_62)))
.def_63))))))))))))
(assert (let ((.def_87 (fp.mul RNE x4 (fp #b0 #b01111100 #b10011001100110011001101))))
(let ((.def_83 (fp.mul RNE x3 (fp #b1 #b01111101 #b11000111101011100001010))))
(let ((.def_78 (fp.mul RNE x2 (fp #b0 #b01111110 #b01101101100100010110100))))
(let ((.def_74 (fp.mul RNE x1 (fp #b0 #b01111110 #b11011110101110000101001))))
(let ((.def_70 (fp.mul RNE x0 (fp #b1 #b01111110 #b01011011001000101101000))))
(let ((.def_71 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_70)))
(let ((.def_75 (fp.add RNE .def_71 .def_74)))
(let ((.def_79 (fp.add RNE .def_75 .def_78)))
(let ((.def_84 (fp.add RNE .def_79 .def_83)))
(let ((.def_88 (fp.add RNE .def_84 .def_87)))
(let ((.def_89 (fp.leq (fp #b1 #b01111110 #b10010011011101001011110) .def_88)))
.def_89))))))))))))
(assert (let ((.def_112 (fp.mul RNE x4 (fp #b0 #b01111100 #b11010000111001010110000))))
(let ((.def_108 (fp.mul RNE x3 (fp #b1 #b01111110 #b01011110001101010100000))))
(let ((.def_103 (fp.mul RNE x2 (fp #b0 #b01111110 #b00100001010001111010111))))
(let ((.def_99 (fp.mul RNE x1 (fp #b1 #b01111110 #b00111000010100011110110))))
(let ((.def_94 (fp.mul RNE x0 (fp #b0 #b01111110 #b00101010011111101111101))))
(let ((.def_95 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_94)))
(let ((.def_100 (fp.add RNE .def_95 .def_99)))
(let ((.def_104 (fp.add RNE .def_100 .def_103)))
(let ((.def_109 (fp.add RNE .def_104 .def_108)))
(let ((.def_113 (fp.add RNE .def_109 .def_112)))
(let ((.def_114 (fp.leq .def_113 (fp #b0 #b01111110 #b00111101011100001010010))))
.def_114))))))))))))
(assert (let ((.def_137 (fp.mul RNE x4 (fp #b1 #b01111110 #b10001011110001101010100))))
(let ((.def_132 (fp.mul RNE x3 (fp #b0 #b01111110 #b10000001100010010011100))))
(let ((.def_128 (fp.mul RNE x2 (fp #b0 #b01111101 #b11010110000001000001100))))
(let ((.def_124 (fp.mul RNE x1 (fp #b1 #b01111110 #b00010010111100011010101))))
(let ((.def_119 (fp.mul RNE x0 (fp #b0 #b01111101 #b01111000110101001111111))))
(let ((.def_120 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_119)))
(let ((.def_125 (fp.add RNE .def_120 .def_124)))
(let ((.def_129 (fp.add RNE .def_125 .def_128)))
(let ((.def_133 (fp.add RNE .def_129 .def_132)))
(let ((.def_138 (fp.add RNE .def_133 .def_137)))
(let ((.def_139 (fp.leq (fp #b0 #b01111101 #b01010111000010100011111) .def_138)))
.def_139))))))))))))
(assert (let ((.def_161 (fp.mul RNE x4 (fp #b0 #b01111110 #b11101110100101111000111))))
(let ((.def_157 (fp.mul RNE x3 (fp #b0 #b01111110 #b01011001000101101000100))))
(let ((.def_153 (fp.mul RNE x2 (fp #b1 #b01111110 #b10001110010101100000010))))
(let ((.def_148 (fp.mul RNE x1 (fp #b0 #b01111010 #b11001010110000001000010))))
(let ((.def_144 (fp.mul RNE x0 (fp #b0 #b01111101 #b11010100111111011111010))))
(let ((.def_145 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_144)))
(let ((.def_149 (fp.add RNE .def_145 .def_148)))
(let ((.def_154 (fp.add RNE .def_149 .def_153)))
(let ((.def_158 (fp.add RNE .def_154 .def_157)))
(let ((.def_162 (fp.add RNE .def_158 .def_161)))
(let ((.def_163 (fp.leq .def_162 (fp #b0 #b01111100 #b01111100111011011001001))))
.def_163))))))))))))
(assert (let ((.def_189 (fp.mul RNE x4 (fp #b0 #b01111110 #b10111101011100001010010))))
(let ((.def_185 (fp.mul RNE x3 (fp #b1 #b01111110 #b11001010001111010111000))))
(let ((.def_180 (fp.mul RNE x2 (fp #b1 #b01111101 #b11001001101110100101111))))
(let ((.def_175 (fp.mul RNE x1 (fp #b1 #b01111100 #b01001001101110100101111))))
(let ((.def_170 (fp.mul RNE x0 (fp #b1 #b01111110 #b00101011100001010001111))))
(let ((.def_171 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_170)))
(let ((.def_176 (fp.add RNE .def_171 .def_175)))
(let ((.def_181 (fp.add RNE .def_176 .def_180)))
(let ((.def_186 (fp.add RNE .def_181 .def_185)))
(let ((.def_190 (fp.add RNE .def_186 .def_189)))
(let ((.def_191 (fp.leq (fp #b1 #b01111110 #b00000000000000000000000) .def_190)))
.def_191))))))))))))
(assert (let ((.def_213 (fp.mul RNE x4 (fp #b0 #b01111010 #b11100011010100111111100))))
(let ((.def_209 (fp.mul RNE x3 (fp #b1 #b01111110 #b10100011010100111111100))))
(let ((.def_204 (fp.mul RNE x2 (fp #b0 #b01111110 #b00111101111100111011011))))
(let ((.def_200 (fp.mul RNE x1 (fp #b1 #b01111101 #b11000101101000011100101))))
(let ((.def_195 (fp.mul RNE x0 (fp #b0 #b01111100 #b11010000111001010110000))))
(let ((.def_196 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_195)))
(let ((.def_201 (fp.add RNE .def_196 .def_200)))
(let ((.def_205 (fp.add RNE .def_201 .def_204)))
(let ((.def_210 (fp.add RNE .def_205 .def_209)))
(let ((.def_214 (fp.add RNE .def_210 .def_213)))
(let ((.def_215 (fp.leq .def_214 (fp #b1 #b01111110 #b11100100110111010011000))))
.def_215))))))))))))
(assert (let ((.def_239 (fp.mul RNE x4 (fp #b1 #b01111110 #b00011111101111100111011))))
(let ((.def_234 (fp.mul RNE x3 (fp #b1 #b01111101 #b10111010010111100011011))))
(let ((.def_229 (fp.mul RNE x2 (fp #b1 #b01111110 #b11001000001100010010011))))
(let ((.def_224 (fp.mul RNE x1 (fp #b0 #b01111101 #b11101001011110001101010))))
(let ((.def_220 (fp.mul RNE x0 (fp #b1 #b01111101 #b11010110000001000001100))))
(let ((.def_221 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_220)))
(let ((.def_225 (fp.add RNE .def_221 .def_224)))
(let ((.def_230 (fp.add RNE .def_225 .def_229)))
(let ((.def_235 (fp.add RNE .def_230 .def_234)))
(let ((.def_240 (fp.add RNE .def_235 .def_239)))
(let ((.def_241 (fp.leq .def_240 (fp #b1 #b01111110 #b01010110000001000001100))))
.def_241))))))))))))
(assert (let ((.def_262 (fp.mul RNE x4 (fp #b0 #b01111101 #b11010100111111011111010))))
(let ((.def_260 (fp.mul RNE x3 (fp #b1 #b01111110 #b10101100000010000011001))))
(let ((.def_255 (fp.mul RNE x2 (fp #b0 #b01111010 #b11011011001000101101000))))
(let ((.def_251 (fp.mul RNE x1 (fp #b0 #b01111100 #b11101011100001010001111))))
(let ((.def_247 (fp.mul RNE x0 (fp #b0 #b01111110 #b11001101010011111110000))))
(let ((.def_248 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_247)))
(let ((.def_252 (fp.add RNE .def_248 .def_251)))
(let ((.def_256 (fp.add RNE .def_252 .def_255)))
(let ((.def_261 (fp.add RNE .def_256 .def_260)))
(let ((.def_263 (fp.add RNE .def_261 .def_262)))
(let ((.def_264 (fp.leq .def_263 (fp #b1 #b01111110 #b10101000111101011100001))))
.def_264))))))))))))
(assert (let ((.def_288 (fp.mul RNE x4 (fp #b0 #b01111110 #b10001010110000001000010))))
(let ((.def_284 (fp.mul RNE x3 (fp #b0 #b01111110 #b10110101001111110111110))))
(let ((.def_280 (fp.mul RNE x2 (fp #b0 #b01111110 #b01100110011001100110011))))
(let ((.def_276 (fp.mul RNE x1 (fp #b1 #b01111110 #b01110110010001011010001))))
(let ((.def_271 (fp.mul RNE x0 (fp #b1 #b01111011 #b10001101010011111110000))))
(let ((.def_272 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_271)))
(let ((.def_277 (fp.add RNE .def_272 .def_276)))
(let ((.def_281 (fp.add RNE .def_277 .def_280)))
(let ((.def_285 (fp.add RNE .def_281 .def_284)))
(let ((.def_289 (fp.add RNE .def_285 .def_288)))
(let ((.def_290 (fp.leq .def_289 (fp #b1 #b01111110 #b10010010111100011010101))))
.def_290))))))))))))
(assert (let ((.def_313 (fp.mul RNE x4 (fp #b1 #b01111110 #b01011010100111111011111))))
(let ((.def_308 (fp.mul RNE x3 (fp #b1 #b01111110 #b00100001010001111010111))))
(let ((.def_305 (fp.mul RNE x2 (fp #b0 #b01111100 #b11011011001000101101000))))
(let ((.def_301 (fp.mul RNE x1 (fp #b0 #b01111110 #b10010011111101111100111))))
(let ((.def_297 (fp.mul RNE x0 (fp #b1 #b01111101 #b00111100011010100111111))))
(let ((.def_298 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_297)))
(let ((.def_302 (fp.add RNE .def_298 .def_301)))
(let ((.def_306 (fp.add RNE .def_302 .def_305)))
(let ((.def_309 (fp.add RNE .def_306 .def_308)))
(let ((.def_314 (fp.add RNE .def_309 .def_313)))
(let ((.def_315 (fp.leq (fp #b1 #b01111110 #b10110011001100110011010) .def_314)))
.def_315))))))))))))
(assert (let ((.def_338 (fp.mul RNE x4 (fp #b1 #b01111110 #b10110111010010111100011))))
(let ((.def_333 (fp.mul RNE x3 (fp #b1 #b01111110 #b00011010100111111011111))))
(let ((.def_328 (fp.mul RNE x2 (fp #b1 #b01111101 #b11100111011011001000110))))
(let ((.def_323 (fp.mul RNE x1 (fp #b0 #b01111110 #b01011110001101010100000))))
(let ((.def_321 (fp.mul RNE x0 (fp #b1 #b01111110 #b10110111110011101101101))))
(let ((.def_322 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_321)))
(let ((.def_324 (fp.add RNE .def_322 .def_323)))
(let ((.def_329 (fp.add RNE .def_324 .def_328)))
(let ((.def_334 (fp.add RNE .def_329 .def_333)))
(let ((.def_339 (fp.add RNE .def_334 .def_338)))
(let ((.def_340 (fp.leq .def_339 (fp #b0 #b01111110 #b11000100100110111010011))))
.def_340))))))))))))
(assert (let ((.def_363 (fp.mul RNE x4 (fp #b1 #b01111101 #b10101100000010000011001))))
(let ((.def_358 (fp.mul RNE x3 (fp #b0 #b01111011 #b10011101101100100010111))))
(let ((.def_354 (fp.mul RNE x2 (fp #b0 #b01111101 #b01110111110011101101101))))
(let ((.def_350 (fp.mul RNE x1 (fp #b1 #b01111110 #b10110110010001011010001))))
(let ((.def_345 (fp.mul RNE x0 (fp #b1 #b01111110 #b01101101100100010110100))))
(let ((.def_346 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_345)))
(let ((.def_351 (fp.add RNE .def_346 .def_350)))
(let ((.def_355 (fp.add RNE .def_351 .def_354)))
(let ((.def_359 (fp.add RNE .def_355 .def_358)))
(let ((.def_364 (fp.add RNE .def_359 .def_363)))
(let ((.def_365 (fp.leq .def_364 (fp #b1 #b01111110 #b10010000111001010110000))))
.def_365))))))))))))
(assert (let ((.def_389 (fp.mul RNE x4 (fp #b0 #b01111100 #b11110111110011101101101))))
(let ((.def_385 (fp.mul RNE x3 (fp #b1 #b01111100 #b10100111111011111001111))))
(let ((.def_380 (fp.mul RNE x2 (fp #b0 #b01111110 #b01011000100100110111010))))
(let ((.def_376 (fp.mul RNE x1 (fp #b1 #b01111101 #b01000100100110111010011))))
(let ((.def_371 (fp.mul RNE x0 (fp #b1 #b01111100 #b11000110101001111111000))))
(let ((.def_372 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_371)))
(let ((.def_377 (fp.add RNE .def_372 .def_376)))
(let ((.def_381 (fp.add RNE .def_377 .def_380)))
(let ((.def_386 (fp.add RNE .def_381 .def_385)))
(let ((.def_390 (fp.add RNE .def_386 .def_389)))
(let ((.def_391 (fp.leq .def_390 (fp #b0 #b01111110 #b11111100011010100111111))))
.def_391))))))))))))
(assert (let ((.def_414 (fp.mul RNE x4 (fp #b0 #b01111110 #b00111010010111100011011))))
(let ((.def_410 (fp.mul RNE x3 (fp #b0 #b01111110 #b10000011100101011000001))))
(let ((.def_406 (fp.mul RNE x2 (fp #b1 #b01111101 #b10000100000110001001010))))
(let ((.def_401 (fp.mul RNE x1 (fp #b0 #b01111100 #b00111101011100001010010))))
(let ((.def_397 (fp.mul RNE x0 (fp #b0 #b01111110 #b01101010011111101111101))))
(let ((.def_398 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_397)))
(let ((.def_402 (fp.add RNE .def_398 .def_401)))
(let ((.def_407 (fp.add RNE .def_402 .def_406)))
(let ((.def_411 (fp.add RNE .def_407 .def_410)))
(let ((.def_415 (fp.add RNE .def_411 .def_414)))
(let ((.def_416 (fp.leq (fp #b1 #b01111110 #b00010001111010111000011) .def_415)))
.def_416))))))))))))
(check-sat)
