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
(assert (let ((.def_61 (fp.mul RNE x4 (fp #b1 #b01111101 #b01011000000100000110001))))
(let ((.def_56 (fp.mul RNE x3 (fp #b0 #b01111100 #b11011011001000101101000))))
(let ((.def_52 (fp.mul RNE x2 (fp #b0 #b01111110 #b00100011010100111111100))))
(let ((.def_48 (fp.mul RNE x1 (fp #b1 #b01111110 #b00110010101100000010000))))
(let ((.def_43 (fp.mul RNE x0 (fp #b0 #b01111011 #b01100000010000011000101))))
(let ((.def_44 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_43)))
(let ((.def_49 (fp.add RNE .def_44 .def_48)))
(let ((.def_53 (fp.add RNE .def_49 .def_52)))
(let ((.def_57 (fp.add RNE .def_53 .def_56)))
(let ((.def_62 (fp.add RNE .def_57 .def_61)))
(let ((.def_63 (fp.leq (fp #b1 #b01111101 #b10011111101111100111011) .def_62)))
.def_63))))))))))))
(assert (let ((.def_86 (fp.mul RNE x4 (fp #b0 #b01111011 #b00100110111010010111100))))
(let ((.def_82 (fp.mul RNE x3 (fp #b0 #b01111101 #b00000101000111101011100))))
(let ((.def_78 (fp.mul RNE x2 (fp #b1 #b01111101 #b10111110011101101100100))))
(let ((.def_73 (fp.mul RNE x1 (fp #b0 #b01111101 #b00000010000011000100101))))
(let ((.def_69 (fp.mul RNE x0 (fp #b1 #b01111100 #b00010110100001110010110))))
(let ((.def_70 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_69)))
(let ((.def_74 (fp.add RNE .def_70 .def_73)))
(let ((.def_79 (fp.add RNE .def_74 .def_78)))
(let ((.def_83 (fp.add RNE .def_79 .def_82)))
(let ((.def_87 (fp.add RNE .def_83 .def_86)))
(let ((.def_88 (fp.leq (fp #b0 #b01111100 #b01001101110100101111001) .def_87)))
.def_88))))))))))))
(assert (let ((.def_111 (fp.mul RNE x4 (fp #b0 #b01111110 #b11000100100110111010011))))
(let ((.def_107 (fp.mul RNE x3 (fp #b0 #b01111101 #b00010101100000010000011))))
(let ((.def_103 (fp.mul RNE x2 (fp #b1 #b01111110 #b10001101110100101111001))))
(let ((.def_98 (fp.mul RNE x1 (fp #b0 #b01111110 #b00000011100101011000001))))
(let ((.def_94 (fp.mul RNE x0 (fp #b0 #b01111110 #b11110000001000001100010))))
(let ((.def_95 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_94)))
(let ((.def_99 (fp.add RNE .def_95 .def_98)))
(let ((.def_104 (fp.add RNE .def_99 .def_103)))
(let ((.def_108 (fp.add RNE .def_104 .def_107)))
(let ((.def_112 (fp.add RNE .def_108 .def_111)))
(let ((.def_113 (fp.leq (fp #b1 #b01111110 #b11100000010000011000101) .def_112)))
.def_113))))))))))))
(assert (let ((.def_134 (fp.mul RNE x4 (fp #b0 #b01111100 #b11100101011000000100001))))
(let ((.def_130 (fp.mul RNE x3 (fp #b1 #b01111110 #b01100001110010101100000))))
(let ((.def_125 (fp.mul RNE x2 (fp #b1 #b01111100 #b11000100100110111010011))))
(let ((.def_119 (fp.mul RNE x0 (fp #b1 #b01111110 #b01010111100011010101000))))
(let ((.def_120 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_119)))
(let ((.def_98 (fp.mul RNE x1 (fp #b0 #b01111110 #b00000011100101011000001))))
(let ((.def_121 (fp.add RNE .def_98 .def_120)))
(let ((.def_126 (fp.add RNE .def_121 .def_125)))
(let ((.def_131 (fp.add RNE .def_126 .def_130)))
(let ((.def_135 (fp.add RNE .def_131 .def_134)))
(let ((.def_136 (fp.leq .def_135 (fp #b0 #b01111010 #b11010010111100011010101))))
.def_136))))))))))))
(assert (let ((.def_161 (fp.mul RNE x4 (fp #b1 #b01111101 #b10011010100111111011111))))
(let ((.def_156 (fp.mul RNE x3 (fp #b1 #b01111110 #b11100011010100111111100))))
(let ((.def_151 (fp.mul RNE x2 (fp #b0 #b01111101 #b11001101110100101111001))))
(let ((.def_147 (fp.mul RNE x1 (fp #b1 #b01111110 #b00000110101001111111000))))
(let ((.def_142 (fp.mul RNE x0 (fp #b1 #b01111110 #b00110110010001011010001))))
(let ((.def_143 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_142)))
(let ((.def_148 (fp.add RNE .def_143 .def_147)))
(let ((.def_152 (fp.add RNE .def_148 .def_151)))
(let ((.def_157 (fp.add RNE .def_152 .def_156)))
(let ((.def_162 (fp.add RNE .def_157 .def_161)))
(let ((.def_163 (fp.leq (fp #b0 #b01111100 #b10010111100011010101000) .def_162)))
.def_163))))))))))))
(assert (let ((.def_184 (fp.mul RNE x4 (fp #b0 #b01111110 #b00100010110100001110011))))
(let ((.def_180 (fp.mul RNE x3 (fp #b0 #b01111101 #b10110111010010111100011))))
(let ((.def_176 (fp.mul RNE x2 (fp #b0 #b01111110 #b00111001110110110010001))))
(let ((.def_172 (fp.mul RNE x1 (fp #b1 #b01111011 #b00010110100001110010110))))
(let ((.def_167 (fp.mul RNE x0 (fp #b0 #b01111110 #b00110010101100000010000))))
(let ((.def_168 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_167)))
(let ((.def_173 (fp.add RNE .def_168 .def_172)))
(let ((.def_177 (fp.add RNE .def_173 .def_176)))
(let ((.def_181 (fp.add RNE .def_177 .def_180)))
(let ((.def_185 (fp.add RNE .def_181 .def_184)))
(let ((.def_186 (fp.leq (fp #b1 #b01111110 #b10101111000110101010000) .def_185)))
.def_186))))))))))))
(assert (let ((.def_207 (fp.mul RNE x4 (fp #b1 #b01111110 #b00100101111000110101010))))
(let ((.def_202 (fp.mul RNE x3 (fp #b0 #b01111110 #b00001101110100101111001))))
(let ((.def_198 (fp.mul RNE x2 (fp #b0 #b01111110 #b00010110000001000001100))))
(let ((.def_194 (fp.mul RNE x1 (fp #b0 #b01111101 #b00010101100000010000011))))
(let ((.def_192 (fp.mul RNE x0 (fp #b1 #b01111101 #b10010110100001110010110))))
(let ((.def_193 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_192)))
(let ((.def_195 (fp.add RNE .def_193 .def_194)))
(let ((.def_199 (fp.add RNE .def_195 .def_198)))
(let ((.def_203 (fp.add RNE .def_199 .def_202)))
(let ((.def_208 (fp.add RNE .def_203 .def_207)))
(let ((.def_209 (fp.leq .def_208 (fp #b0 #b01111100 #b00011110101110000101001))))
.def_209))))))))))))
(assert (let ((.def_231 (fp.mul RNE x4 (fp #b0 #b01111101 #b00001101010011111110000))))
(let ((.def_227 (fp.mul RNE x3 (fp #b0 #b01111100 #b01111110111110011101110))))
(let ((.def_223 (fp.mul RNE x2 (fp #b0 #b01111110 #b00011111001110110110010))))
(let ((.def_219 (fp.mul RNE x1 (fp #b0 #b01111110 #b10111110011101101100100))))
(let ((.def_215 (fp.mul RNE x0 (fp #b0 #b01111110 #b10000111101011100001010))))
(let ((.def_216 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_215)))
(let ((.def_220 (fp.add RNE .def_216 .def_219)))
(let ((.def_224 (fp.add RNE .def_220 .def_223)))
(let ((.def_228 (fp.add RNE .def_224 .def_227)))
(let ((.def_232 (fp.add RNE .def_228 .def_231)))
(let ((.def_233 (fp.leq (fp #b1 #b01111110 #b11000011100101011000001) .def_232)))
.def_233))))))))))))
(assert (let ((.def_253 (fp.mul RNE x4 (fp #b0 #b01111100 #b00011010100111111011111))))
(let ((.def_249 (fp.mul RNE x3 (fp #b0 #b01111110 #b10001101110100101111001))))
(let ((.def_247 (fp.mul RNE x2 (fp #b1 #b01111110 #b10001111010111000010100))))
(let ((.def_242 (fp.mul RNE x1 (fp #b0 #b01111110 #b10100011010100111111100))))
(let ((.def_238 (fp.mul RNE x0 (fp #b0 #b01111110 #b00101011100001010001111))))
(let ((.def_239 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_238)))
(let ((.def_243 (fp.add RNE .def_239 .def_242)))
(let ((.def_248 (fp.add RNE .def_243 .def_247)))
(let ((.def_250 (fp.add RNE .def_248 .def_249)))
(let ((.def_254 (fp.add RNE .def_250 .def_253)))
(let ((.def_255 (fp.leq .def_254 (fp #b0 #b01111110 #b01011100101011000000100))))
.def_255))))))))))))
(assert (let ((.def_280 (fp.mul RNE x4 (fp #b1 #b01111110 #b10101011100001010001111))))
(let ((.def_275 (fp.mul RNE x3 (fp #b1 #b01111110 #b00011100001010001111011))))
(let ((.def_270 (fp.mul RNE x2 (fp #b0 #b01111101 #b01001000101101000011101))))
(let ((.def_266 (fp.mul RNE x1 (fp #b0 #b01111101 #b11110101110000101001000))))
(let ((.def_262 (fp.mul RNE x0 (fp #b1 #b01111110 #b10111011111001110110110))))
(let ((.def_263 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_262)))
(let ((.def_267 (fp.add RNE .def_263 .def_266)))
(let ((.def_271 (fp.add RNE .def_267 .def_270)))
(let ((.def_276 (fp.add RNE .def_271 .def_275)))
(let ((.def_281 (fp.add RNE .def_276 .def_280)))
(let ((.def_282 (fp.leq .def_281 (fp #b1 #b01111110 #b00101111100111011011001))))
.def_282))))))))))))
(assert (let ((.def_304 (fp.mul RNE x4 (fp #b0 #b01111100 #b01101010011111101111101))))
(let ((.def_300 (fp.mul RNE x3 (fp #b0 #b01111110 #b00110011001100110011010))))
(let ((.def_296 (fp.mul RNE x2 (fp #b0 #b01111101 #b10000001000001100010010))))
(let ((.def_292 (fp.mul RNE x1 (fp #b1 #b01111010 #b01001111110111110011110))))
(let ((.def_287 (fp.mul RNE x0 (fp #b0 #b01111110 #b00001111110111110011110))))
(let ((.def_288 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_287)))
(let ((.def_293 (fp.add RNE .def_288 .def_292)))
(let ((.def_297 (fp.add RNE .def_293 .def_296)))
(let ((.def_301 (fp.add RNE .def_297 .def_300)))
(let ((.def_305 (fp.add RNE .def_301 .def_304)))
(let ((.def_306 (fp.leq (fp #b0 #b01111110 #b00011110101110000101001) .def_305)))
.def_306))))))))))))
(assert (let ((.def_327 (fp.mul RNE x4 (fp #b0 #b01111110 #b11011010100111111011111))))
(let ((.def_323 (fp.mul RNE x3 (fp #b1 #b01111100 #b01110010101100000010000))))
(let ((.def_318 (fp.mul RNE x2 (fp #b0 #b01111100 #b11001000101101000011101))))
(let ((.def_314 (fp.mul RNE x1 (fp #b1 #b01111101 #b11011010000111001010110))))
(let ((.def_309 (fp.mul RNE x0 (fp #b0 #b01111011 #b11001010110000001000010))))
(let ((.def_310 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_309)))
(let ((.def_315 (fp.add RNE .def_310 .def_314)))
(let ((.def_319 (fp.add RNE .def_315 .def_318)))
(let ((.def_324 (fp.add RNE .def_319 .def_323)))
(let ((.def_328 (fp.add RNE .def_324 .def_327)))
(let ((.def_329 (fp.leq .def_328 (fp #b0 #b01111100 #b11100101011000000100001))))
.def_329))))))))))))
(assert (let ((.def_350 (fp.mul RNE x4 (fp #b0 #b01111010 #b10000001000001100010010))))
(let ((.def_346 (fp.mul RNE x3 (fp #b0 #b01111110 #b01011000100100110111010))))
(let ((.def_342 (fp.mul RNE x2 (fp #b1 #b01111110 #b01101100000010000011001))))
(let ((.def_337 (fp.mul RNE x1 (fp #b1 #b01111110 #b11100000010000011000101))))
(let ((.def_335 (fp.mul RNE x0 (fp #b0 #b01111110 #b01001111010111000010100))))
(let ((.def_336 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_335)))
(let ((.def_338 (fp.add RNE .def_336 .def_337)))
(let ((.def_343 (fp.add RNE .def_338 .def_342)))
(let ((.def_347 (fp.add RNE .def_343 .def_346)))
(let ((.def_351 (fp.add RNE .def_347 .def_350)))
(let ((.def_352 (fp.leq .def_351 (fp #b1 #b01111110 #b01001000101101000011101))))
.def_352))))))))))))
(assert (let ((.def_375 (fp.mul RNE x4 (fp #b1 #b01111101 #b00010001011010000111001))))
(let ((.def_370 (fp.mul RNE x3 (fp #b0 #b01111110 #b11110010101100000010000))))
(let ((.def_366 (fp.mul RNE x2 (fp #b0 #b01111110 #b10000001100010010011100))))
(let ((.def_362 (fp.mul RNE x1 (fp #b0 #b01111110 #b10010011111101111100111))))
(let ((.def_358 (fp.mul RNE x0 (fp #b0 #b01111110 #b10110111110011101101101))))
(let ((.def_359 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_358)))
(let ((.def_363 (fp.add RNE .def_359 .def_362)))
(let ((.def_367 (fp.add RNE .def_363 .def_366)))
(let ((.def_371 (fp.add RNE .def_367 .def_370)))
(let ((.def_376 (fp.add RNE .def_371 .def_375)))
(let ((.def_377 (fp.leq (fp #b1 #b01111101 #b11011000000100000110001) .def_376)))
.def_377))))))))))))
(assert (let ((.def_400 (fp.mul RNE x4 (fp #b0 #b01111110 #b00010111100011010101000))))
(let ((.def_396 (fp.mul RNE x3 (fp #b1 #b01111101 #b10000000000000000000000))))
(let ((.def_391 (fp.mul RNE x2 (fp #b1 #b01111110 #b10100110011001100110011))))
(let ((.def_386 (fp.mul RNE x1 (fp #b0 #b01111110 #b00001111010111000010100))))
(let ((.def_382 (fp.mul RNE x0 (fp #b0 #b01111000 #b00000110001001001101111))))
(let ((.def_383 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_382)))
(let ((.def_387 (fp.add RNE .def_383 .def_386)))
(let ((.def_392 (fp.add RNE .def_387 .def_391)))
(let ((.def_397 (fp.add RNE .def_392 .def_396)))
(let ((.def_401 (fp.add RNE .def_397 .def_400)))
(let ((.def_402 (fp.leq (fp #b0 #b01111101 #b11010111000010100011111) .def_401)))
.def_402))))))))))))
(check-sat)
