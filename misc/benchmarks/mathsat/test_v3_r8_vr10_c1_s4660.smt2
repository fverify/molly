(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
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
(assert (let ((.def_45 (fp.mul RNE x2 (fp #b1 #b01111110 #b10011101001011110001101))))
(let ((.def_40 (fp.mul RNE x1 (fp #b1 #b01111101 #b11000001100010010011100))))
(let ((.def_35 (fp.mul RNE x0 (fp #b1 #b01111100 #b11011111001110110110010))))
(let ((.def_36 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_35)))
(let ((.def_41 (fp.add RNE .def_36 .def_40)))
(let ((.def_46 (fp.add RNE .def_41 .def_45)))
(let ((.def_47 (fp.leq (fp #b0 #b01111110 #b10110110010001011010001) .def_46)))
.def_47))))))))
(assert (let ((.def_63 (fp.mul RNE x2 (fp #b0 #b01111011 #b00000010000011000100101))))
(let ((.def_59 (fp.mul RNE x1 (fp #b1 #b01111100 #b10001001001101110100110))))
(let ((.def_54 (fp.mul RNE x0 (fp #b1 #b01111101 #b00101100000010000011001))))
(let ((.def_55 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_54)))
(let ((.def_60 (fp.add RNE .def_55 .def_59)))
(let ((.def_64 (fp.add RNE .def_60 .def_63)))
(let ((.def_65 (fp.leq .def_64 (fp #b1 #b01111101 #b01000100100110111010011))))
.def_65))))))))
(assert (let ((.def_80 (fp.mul RNE x2 (fp #b0 #b01111110 #b01000000100000110001001))))
(let ((.def_76 (fp.mul RNE x1 (fp #b1 #b01111110 #b11110100101111000110101))))
(let ((.def_71 (fp.mul RNE x0 (fp #b1 #b01111101 #b10101101000011100101011))))
(let ((.def_72 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_71)))
(let ((.def_77 (fp.add RNE .def_72 .def_76)))
(let ((.def_81 (fp.add RNE .def_77 .def_80)))
(let ((.def_82 (fp.leq (fp #b0 #b01111110 #b10100100010110100001110) .def_81)))
.def_82))))))))
(assert (let ((.def_96 (fp.mul RNE x2 (fp #b0 #b01111110 #b10110000101000111101100))))
(let ((.def_92 (fp.mul RNE x1 (fp #b1 #b01111110 #b11010100111111011111010))))
(let ((.def_87 (fp.mul RNE x0 (fp #b0 #b01111110 #b11010111000010100011111))))
(let ((.def_88 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_87)))
(let ((.def_93 (fp.add RNE .def_88 .def_92)))
(let ((.def_97 (fp.add RNE .def_93 .def_96)))
(let ((.def_98 (fp.leq (fp #b0 #b01111110 #b11000101101000011100101) .def_97)))
.def_98))))))))
(assert (let ((.def_114 (fp.mul RNE x2 (fp #b0 #b01111101 #b11011111001110110110010))))
(let ((.def_110 (fp.mul RNE x1 (fp #b1 #b01111110 #b00011001000101101000100))))
(let ((.def_105 (fp.mul RNE x0 (fp #b1 #b01111011 #b10100001110010101100000))))
(let ((.def_106 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_105)))
(let ((.def_111 (fp.add RNE .def_106 .def_110)))
(let ((.def_115 (fp.add RNE .def_111 .def_114)))
(let ((.def_116 (fp.leq .def_115 (fp #b1 #b01111101 #b10111001010110000001000))))
.def_116))))))))
(assert (let ((.def_130 (fp.mul RNE x2 (fp #b0 #b01111101 #b11101000011100101011000))))
(let ((.def_126 (fp.mul RNE x1 (fp #b0 #b01111110 #b10100010110100001110011))))
(let ((.def_122 (fp.mul RNE x0 (fp #b0 #b01111101 #b10001111010111000010100))))
(let ((.def_123 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_122)))
(let ((.def_127 (fp.add RNE .def_123 .def_126)))
(let ((.def_131 (fp.add RNE .def_127 .def_130)))
(let ((.def_132 (fp.leq .def_131 (fp #b1 #b01111101 #b10010001011010000111001))))
.def_132))))))))
(assert (let ((.def_146 (fp.mul RNE x2 (fp #b1 #b01111110 #b10111010010111100011011))))
(let ((.def_141 (fp.mul RNE x1 (fp #b0 #b01111110 #b01110101110000101001000))))
(let ((.def_137 (fp.mul RNE x0 (fp #b0 #b01111100 #b00001100010010011011101))))
(let ((.def_138 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_137)))
(let ((.def_142 (fp.add RNE .def_138 .def_141)))
(let ((.def_147 (fp.add RNE .def_142 .def_146)))
(let ((.def_148 (fp.leq (fp #b0 #b01111110 #b10010100011110101110001) .def_147)))
.def_148))))))))
(assert (let ((.def_162 (fp.mul RNE x2 (fp #b1 #b01111110 #b00010111000010100011111))))
(let ((.def_157 (fp.mul RNE x1 (fp #b0 #b01111100 #b00001010001111010111000))))
(let ((.def_153 (fp.mul RNE x0 (fp #b0 #b01111010 #b10101001111110111110100))))
(let ((.def_154 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_153)))
(let ((.def_158 (fp.add RNE .def_154 .def_157)))
(let ((.def_163 (fp.add RNE .def_158 .def_162)))
(let ((.def_164 (fp.leq .def_163 (fp #b0 #b01111100 #b01111100111011011001001))))
.def_164))))))))
(check-sat)