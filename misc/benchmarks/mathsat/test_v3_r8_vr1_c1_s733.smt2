(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
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
(assert (let ((.def_44 (fp.mul RNE x2 (fp #b0 #b01111011 #b01101000011100101011000))))
(let ((.def_40 (fp.mul RNE x1 (fp #b1 #b01111110 #b01110000001000001100010))))
(let ((.def_35 (fp.mul RNE x0 (fp #b0 #b01111101 #b00011000100100110111010))))
(let ((.def_36 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_35)))
(let ((.def_41 (fp.add RNE .def_36 .def_40)))
(let ((.def_45 (fp.add RNE .def_41 .def_44)))
(let ((.def_46 (fp.leq .def_45 (fp #b1 #b01111100 #b01010011111101111100111))))
.def_46))))))))
(assert (let ((.def_61 (fp.mul RNE x2 (fp #b1 #b01111101 #b10011010100111111011111))))
(let ((.def_56 (fp.mul RNE x1 (fp #b0 #b01111110 #b00110011001100110011010))))
(let ((.def_52 (fp.mul RNE x0 (fp #b1 #b01111110 #b10000010000011000100101))))
(let ((.def_53 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_52)))
(let ((.def_57 (fp.add RNE .def_53 .def_56)))
(let ((.def_62 (fp.add RNE .def_57 .def_61)))
(let ((.def_63 (fp.leq (fp #b0 #b01111101 #b11110001101010011111110) .def_62)))
.def_63))))))))
(assert (let ((.def_76 (fp.mul RNE x2 (fp #b0 #b01111101 #b11010110000001000001100))))
(let ((.def_72 (fp.mul RNE x1 (fp #b0 #b01111110 #b00011001100110011001101))))
(let ((.def_68 (fp.mul RNE x0 (fp #b0 #b01111110 #b10110101001111110111110))))
(let ((.def_69 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_68)))
(let ((.def_73 (fp.add RNE .def_69 .def_72)))
(let ((.def_77 (fp.add RNE .def_73 .def_76)))
(let ((.def_78 (fp.leq .def_77 (fp #b0 #b01111110 #b00011000100100110111010))))
.def_78))))))))
(assert (let ((.def_93 (fp.mul RNE x2 (fp #b0 #b01111110 #b10100111011011001000110))))
(let ((.def_89 (fp.mul RNE x1 (fp #b1 #b01111110 #b00010010111100011010101))))
(let ((.def_84 (fp.mul RNE x0 (fp #b1 #b01111011 #b10010101100000010000011))))
(let ((.def_85 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_84)))
(let ((.def_90 (fp.add RNE .def_85 .def_89)))
(let ((.def_94 (fp.add RNE .def_90 .def_93)))
(let ((.def_95 (fp.leq .def_94 (fp #b0 #b01111110 #b10001110110110010001011))))
.def_95))))))))
(assert (let ((.def_110 (fp.mul RNE x2 (fp #b1 #b01111101 #b11110100101111000110101))))
(let ((.def_105 (fp.mul RNE x1 (fp #b0 #b01111101 #b11110011101101100100011))))
(let ((.def_101 (fp.mul RNE x0 (fp #b0 #b01111110 #b10010000011000100100111))))
(let ((.def_102 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_101)))
(let ((.def_106 (fp.add RNE .def_102 .def_105)))
(let ((.def_111 (fp.add RNE .def_106 .def_110)))
(let ((.def_112 (fp.leq (fp #b1 #b01111110 #b11110100101111000110101) .def_111)))
.def_112))))))))
(assert (let ((.def_127 (fp.mul RNE x2 (fp #b1 #b01111100 #b10110100001110010101100))))
(let ((.def_122 (fp.mul RNE x1 (fp #b0 #b01111110 #b01111110011101101100100))))
(let ((.def_118 (fp.mul RNE x0 (fp #b0 #b01111110 #b11010000111001010110000))))
(let ((.def_119 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_118)))
(let ((.def_123 (fp.add RNE .def_119 .def_122)))
(let ((.def_128 (fp.add RNE .def_123 .def_127)))
(let ((.def_129 (fp.leq .def_128 (fp #b1 #b01111110 #b11111101011100001010010))))
.def_129))))))))
(assert (let ((.def_144 (fp.mul RNE x2 (fp #b0 #b01111110 #b01111010010111100011011))))
(let ((.def_140 (fp.mul RNE x1 (fp #b1 #b01111100 #b11111001110110110010001))))
(let ((.def_135 (fp.mul RNE x0 (fp #b1 #b01111100 #b11110111110011101101101))))
(let ((.def_136 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_135)))
(let ((.def_141 (fp.add RNE .def_136 .def_140)))
(let ((.def_145 (fp.add RNE .def_141 .def_144)))
(let ((.def_146 (fp.leq .def_145 (fp #b0 #b01111110 #b10011110001101010100000))))
.def_146))))))))
(assert (let ((.def_160 (fp.mul RNE x2 (fp #b0 #b01111110 #b10101000011100101011000))))
(let ((.def_156 (fp.mul RNE x1 (fp #b1 #b01111001 #b11001010110000001000010))))
(let ((.def_151 (fp.mul RNE x0 (fp #b0 #b01111110 #b00010100011110101110001))))
(let ((.def_152 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_151)))
(let ((.def_157 (fp.add RNE .def_152 .def_156)))
(let ((.def_161 (fp.add RNE .def_157 .def_160)))
(let ((.def_162 (fp.leq (fp #b0 #b01111101 #b00001010001111010111000) .def_161)))
.def_162))))))))
(check-sat)
