(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
(declare-fun x3 () (_ FloatingPoint 8 24))
(declare-fun x4 () (_ FloatingPoint 8 24))
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
(assert (let ((.def_60 (fp.mul RNE x4 (fp #b1 #b01111101 #b00100010110100001110011))))
(let ((.def_55 (fp.mul RNE x3 (fp #b0 #b01111101 #b11011000000100000110001))))
(let ((.def_51 (fp.mul RNE x2 (fp #b0 #b01111110 #b11100110111010010111100))))
(let ((.def_47 (fp.mul RNE x1 (fp #b0 #b01111100 #b01010110000001000001100))))
(let ((.def_43 (fp.mul RNE x0 (fp #b1 #b01111101 #b10111000010100011110110))))
(let ((.def_44 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_43)))
(let ((.def_48 (fp.add RNE .def_44 .def_47)))
(let ((.def_52 (fp.add RNE .def_48 .def_51)))
(let ((.def_56 (fp.add RNE .def_52 .def_55)))
(let ((.def_61 (fp.add RNE .def_56 .def_60)))
(let ((.def_62 (fp.leq .def_61 (fp #b0 #b01111100 #b11000000100000110001001))))
.def_62))))))))))))
(assert (let ((.def_84 (fp.mul RNE x4 (fp #b0 #b01111110 #b01010001111010111000011))))
(let ((.def_80 (fp.mul RNE x3 (fp #b0 #b01111110 #b01110010101100000010000))))
(let ((.def_76 (fp.mul RNE x2 (fp #b0 #b01111101 #b00011110101110000101001))))
(let ((.def_72 (fp.mul RNE x1 (fp #b0 #b01111011 #b00010010011011101001100))))
(let ((.def_68 (fp.mul RNE x0 (fp #b1 #b01111110 #b01011010000111001010110))))
(let ((.def_69 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_68)))
(let ((.def_73 (fp.add RNE .def_69 .def_72)))
(let ((.def_77 (fp.add RNE .def_73 .def_76)))
(let ((.def_81 (fp.add RNE .def_77 .def_80)))
(let ((.def_85 (fp.add RNE .def_81 .def_84)))
(let ((.def_86 (fp.leq (fp #b0 #b01111101 #b10011011101001011110010) .def_85)))
.def_86))))))))))))
(assert (let ((.def_109 (fp.mul RNE x4 (fp #b0 #b01111110 #b10000111101011100001010))))
(let ((.def_105 (fp.mul RNE x3 (fp #b1 #b01111110 #b00110111010010111100011))))
(let ((.def_100 (fp.mul RNE x2 (fp #b0 #b01111110 #b00110100101111000110101))))
(let ((.def_96 (fp.mul RNE x1 (fp #b1 #b01111101 #b01010000111001010110000))))
(let ((.def_91 (fp.mul RNE x0 (fp #b0 #b01111110 #b01110000101000111101100))))
(let ((.def_92 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_91)))
(let ((.def_97 (fp.add RNE .def_92 .def_96)))
(let ((.def_101 (fp.add RNE .def_97 .def_100)))
(let ((.def_106 (fp.add RNE .def_101 .def_105)))
(let ((.def_110 (fp.add RNE .def_106 .def_109)))
(let ((.def_111 (fp.leq .def_110 (fp #b0 #b01111110 #b00100111111011111001111))))
.def_111))))))))))))
(assert (let ((.def_135 (fp.mul RNE x4 (fp #b1 #b01111100 #b11111001110110110010001))))
(let ((.def_130 (fp.mul RNE x3 (fp #b1 #b01111110 #b00110101001111110111110))))
(let ((.def_125 (fp.mul RNE x2 (fp #b0 #b01111110 #b01101000011100101011000))))
(let ((.def_121 (fp.mul RNE x1 (fp #b0 #b01111101 #b10100100110111010011000))))
(let ((.def_117 (fp.mul RNE x0 (fp #b1 #b01111101 #b00000100000110001001010))))
(let ((.def_118 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_117)))
(let ((.def_122 (fp.add RNE .def_118 .def_121)))
(let ((.def_126 (fp.add RNE .def_122 .def_125)))
(let ((.def_131 (fp.add RNE .def_126 .def_130)))
(let ((.def_136 (fp.add RNE .def_131 .def_135)))
(let ((.def_137 (fp.leq (fp #b0 #b01111100 #b11100001010001111010111) .def_136)))
.def_137))))))))))))
(assert (let ((.def_160 (fp.mul RNE x4 (fp #b0 #b01111110 #b00010011011101001011110))))
(let ((.def_156 (fp.mul RNE x3 (fp #b0 #b01111101 #b11010010111100011010101))))
(let ((.def_152 (fp.mul RNE x2 (fp #b0 #b01111101 #b10000010000011000100101))))
(let ((.def_148 (fp.mul RNE x1 (fp #b1 #b01111110 #b01010100111111011111010))))
(let ((.def_143 (fp.mul RNE x0 (fp #b1 #b01111101 #b01101001011110001101010))))
(let ((.def_144 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_143)))
(let ((.def_149 (fp.add RNE .def_144 .def_148)))
(let ((.def_153 (fp.add RNE .def_149 .def_152)))
(let ((.def_157 (fp.add RNE .def_153 .def_156)))
(let ((.def_161 (fp.add RNE .def_157 .def_160)))
(let ((.def_162 (fp.leq (fp #b0 #b01111110 #b00000010000011000100101) .def_161)))
.def_162))))))))))))
(check-sat)
