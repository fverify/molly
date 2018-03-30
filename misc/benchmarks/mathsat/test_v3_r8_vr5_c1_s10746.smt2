(declare-fun x0 () (_ FloatingPoint 8 24))
(declare-fun x1 () (_ FloatingPoint 8 24))
(declare-fun x2 () (_ FloatingPoint 8 24))
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
(assert (let ((.def_43 (fp.mul RNE x2 (fp #b0 #b01111011 #b11100111011011001000110))))
(let ((.def_39 (fp.mul RNE x1 (fp #b0 #b01111101 #b00111000010100011110110))))
(let ((.def_35 (fp.mul RNE x0 (fp #b1 #b01111110 #b01011111101111100111011))))
(let ((.def_36 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_35)))
(let ((.def_40 (fp.add RNE .def_36 .def_39)))
(let ((.def_44 (fp.add RNE .def_40 .def_43)))
(let ((.def_45 (fp.leq .def_44 (fp #b0 #b01111100 #b11001110110110010001011))))
.def_45))))))))
(assert (let ((.def_61 (fp.mul RNE x2 (fp #b1 #b01111110 #b01110010101100000010000))))
(let ((.def_56 (fp.mul RNE x1 (fp #b1 #b01111011 #b11000110101001111111000))))
(let ((.def_51 (fp.mul RNE x0 (fp #b1 #b01111110 #b10100110011001100110011))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_57 (fp.add RNE .def_52 .def_56)))
(let ((.def_62 (fp.add RNE .def_57 .def_61)))
(let ((.def_63 (fp.leq (fp #b0 #b01111110 #b10110010101100000010000) .def_62)))
.def_63))))))))
(assert (let ((.def_79 (fp.mul RNE x2 (fp #b1 #b01111100 #b10011101101100100010111))))
(let ((.def_74 (fp.mul RNE x1 (fp #b1 #b01111110 #b10111001010110000001000))))
(let ((.def_69 (fp.mul RNE x0 (fp #b0 #b01111101 #b00111111011111001110111))))
(let ((.def_70 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_69)))
(let ((.def_75 (fp.add RNE .def_70 .def_74)))
(let ((.def_80 (fp.add RNE .def_75 .def_79)))
(let ((.def_81 (fp.leq (fp #b1 #b01111110 #b01100100010110100001110) .def_80)))
.def_81))))))))
(assert (let ((.def_96 (fp.mul RNE x2 (fp #b1 #b01111110 #b00110001101010011111110))))
(let ((.def_91 (fp.mul RNE x1 (fp #b0 #b01111101 #b10110110010001011010001))))
(let ((.def_87 (fp.mul RNE x0 (fp #b1 #b01111101 #b01110011101101100100011))))
(let ((.def_88 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_87)))
(let ((.def_92 (fp.add RNE .def_88 .def_91)))
(let ((.def_97 (fp.add RNE .def_92 .def_96)))
(let ((.def_98 (fp.leq (fp #b0 #b01111101 #b10110001001001101110101) .def_97)))
.def_98))))))))
(assert (let ((.def_114 (fp.mul RNE x2 (fp #b1 #b01111110 #b01111111011111001110111))))
(let ((.def_109 (fp.mul RNE x1 (fp #b1 #b01111110 #b01010100011110101110001))))
(let ((.def_104 (fp.mul RNE x0 (fp #b1 #b01111001 #b10111010010111100011011))))
(let ((.def_105 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_104)))
(let ((.def_110 (fp.add RNE .def_105 .def_109)))
(let ((.def_115 (fp.add RNE .def_110 .def_114)))
(let ((.def_116 (fp.leq (fp #b0 #b01111101 #b10000110001001001101111) .def_115)))
.def_116))))))))
(assert (let ((.def_131 (fp.mul RNE x2 (fp #b1 #b01111110 #b00000001000001100010010))))
(let ((.def_126 (fp.mul RNE x1 (fp #b1 #b01111110 #b01111010010111100011011))))
(let ((.def_121 (fp.mul RNE x0 (fp #b0 #b01111101 #b10011001100110011001101))))
(let ((.def_122 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_121)))
(let ((.def_127 (fp.add RNE .def_122 .def_126)))
(let ((.def_132 (fp.add RNE .def_127 .def_131)))
(let ((.def_133 (fp.leq .def_132 (fp #b0 #b01111110 #b00111111011111001110111))))
.def_133))))))))
(assert (let ((.def_144 (fp.mul RNE x2 (fp #b0 #b01111110 #b10010110100001110010110))))
(let ((.def_140 (fp.mul RNE x1 (fp #b0 #b01111011 #b11100111011011001000110))))
(let ((.def_138 (fp.mul RNE x0 (fp #b0 #b01111110 #b10010100111111011111010))))
(let ((.def_139 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_138)))
(let ((.def_141 (fp.add RNE .def_139 .def_140)))
(let ((.def_145 (fp.add RNE .def_141 .def_144)))
(let ((.def_146 (fp.leq .def_145 (fp #b0 #b01111110 #b10111101011100001010010))))
.def_146))))))))
(assert (let ((.def_162 (fp.mul RNE x2 (fp #b1 #b01111101 #b00111100011010100111111))))
(let ((.def_157 (fp.mul RNE x1 (fp #b0 #b01111110 #b01001001101110100101111))))
(let ((.def_153 (fp.mul RNE x0 (fp #b1 #b01111110 #b10010110000001000001100))))
(let ((.def_154 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_153)))
(let ((.def_158 (fp.add RNE .def_154 .def_157)))
(let ((.def_163 (fp.add RNE .def_158 .def_162)))
(let ((.def_164 (fp.leq .def_163 (fp #b1 #b01111101 #b01100111011011001000110))))
.def_164))))))))
(check-sat)
