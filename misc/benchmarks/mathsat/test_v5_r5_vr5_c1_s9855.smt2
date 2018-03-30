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
(assert (let ((.def_61 (fp.mul RNE x4 (fp #b0 #b01111011 #b00101011000000100000110))))
(let ((.def_57 (fp.mul RNE x3 (fp #b0 #b01111110 #b10110101001111110111110))))
(let ((.def_53 (fp.mul RNE x2 (fp #b0 #b01111101 #b10011000100100110111010))))
(let ((.def_49 (fp.mul RNE x1 (fp #b1 #b01111110 #b10110011001100110011010))))
(let ((.def_44 (fp.mul RNE x0 (fp #b1 #b01111110 #b00010111000010100011111))))
(let ((.def_45 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_44)))
(let ((.def_50 (fp.add RNE .def_45 .def_49)))
(let ((.def_54 (fp.add RNE .def_50 .def_53)))
(let ((.def_58 (fp.add RNE .def_54 .def_57)))
(let ((.def_62 (fp.add RNE .def_58 .def_61)))
(let ((.def_63 (fp.leq .def_62 (fp #b1 #b01110111 #b00000110001001001101111))))
.def_63))))))))))))
(assert (let ((.def_87 (fp.mul RNE x4 (fp #b1 #b01111101 #b01001011110001101010100))))
(let ((.def_82 (fp.mul RNE x3 (fp #b0 #b01111101 #b11100111011011001000110))))
(let ((.def_78 (fp.mul RNE x2 (fp #b1 #b01111110 #b11100101011000000100001))))
(let ((.def_73 (fp.mul RNE x1 (fp #b1 #b01111100 #b10010001011010000111001))))
(let ((.def_68 (fp.mul RNE x0 (fp #b0 #b01111110 #b01101110000101000111101))))
(let ((.def_69 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_68)))
(let ((.def_74 (fp.add RNE .def_69 .def_73)))
(let ((.def_79 (fp.add RNE .def_74 .def_78)))
(let ((.def_83 (fp.add RNE .def_79 .def_82)))
(let ((.def_88 (fp.add RNE .def_83 .def_87)))
(let ((.def_89 (fp.leq (fp #b0 #b01111110 #b01110000101000111101100) .def_88)))
.def_89))))))))))))
(assert (let ((.def_114 (fp.mul RNE x4 (fp #b0 #b01111110 #b10111011111001110110110))))
(let ((.def_110 (fp.mul RNE x3 (fp #b1 #b01111110 #b00010100111111011111010))))
(let ((.def_105 (fp.mul RNE x2 (fp #b1 #b01111101 #b00101101000011100101011))))
(let ((.def_100 (fp.mul RNE x1 (fp #b0 #b01111100 #b00000100000110001001010))))
(let ((.def_96 (fp.mul RNE x0 (fp #b1 #b01111110 #b01110110110010001011010))))
(let ((.def_97 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_96)))
(let ((.def_101 (fp.add RNE .def_97 .def_100)))
(let ((.def_106 (fp.add RNE .def_101 .def_105)))
(let ((.def_111 (fp.add RNE .def_106 .def_110)))
(let ((.def_115 (fp.add RNE .def_111 .def_114)))
(let ((.def_116 (fp.leq (fp #b1 #b01111110 #b11011010000111001010110) .def_115)))
.def_116))))))))))))
(assert (let ((.def_139 (fp.mul RNE x4 (fp #b0 #b01111101 #b00010111100011010101000))))
(let ((.def_135 (fp.mul RNE x3 (fp #b1 #b01111110 #b11011100001010001111011))))
(let ((.def_130 (fp.mul RNE x2 (fp #b0 #b01111101 #b11110001101010011111110))))
(let ((.def_126 (fp.mul RNE x1 (fp #b1 #b01110110 #b00000110001001001101111))))
(let ((.def_121 (fp.mul RNE x0 (fp #b0 #b01111110 #b01110011101101100100011))))
(let ((.def_122 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_121)))
(let ((.def_127 (fp.add RNE .def_122 .def_126)))
(let ((.def_131 (fp.add RNE .def_127 .def_130)))
(let ((.def_136 (fp.add RNE .def_131 .def_135)))
(let ((.def_140 (fp.add RNE .def_136 .def_139)))
(let ((.def_141 (fp.leq .def_140 (fp #b0 #b01111011 #b10110110010001011010001))))
.def_141))))))))))))
(assert (let ((.def_167 (fp.mul RNE x4 (fp #b1 #b01111101 #b11101011100001010001111))))
(let ((.def_162 (fp.mul RNE x3 (fp #b1 #b01111110 #b10011100101011000000100))))
(let ((.def_157 (fp.mul RNE x2 (fp #b1 #b01111110 #b00111111011111001110111))))
(let ((.def_152 (fp.mul RNE x1 (fp #b1 #b01111101 #b10000110001001001101111))))
(let ((.def_147 (fp.mul RNE x0 (fp #b1 #b01111100 #b00000110001001001101111))))
(let ((.def_148 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_147)))
(let ((.def_153 (fp.add RNE .def_148 .def_152)))
(let ((.def_158 (fp.add RNE .def_153 .def_157)))
(let ((.def_163 (fp.add RNE .def_158 .def_162)))
(let ((.def_168 (fp.add RNE .def_163 .def_167)))
(let ((.def_169 (fp.leq .def_168 (fp #b0 #b01111110 #b11000001100010010011100))))
.def_169))))))))))))
(check-sat)
