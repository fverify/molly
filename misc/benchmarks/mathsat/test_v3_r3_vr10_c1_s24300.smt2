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
(assert (let ((.def_44 (fp.mul RNE x2 (fp #b1 #b01111110 #b10001000101101000011101))))
(let ((.def_39 (fp.mul RNE x1 (fp #b1 #b01111110 #b00010011011101001011110))))
(let ((.def_34 (fp.mul RNE x0 (fp #b0 #b01111110 #b11000010000011000100101))))
(let ((.def_35 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_34)))
(let ((.def_40 (fp.add RNE .def_35 .def_39)))
(let ((.def_45 (fp.add RNE .def_40 .def_44)))
(let ((.def_46 (fp.leq .def_45 (fp #b0 #b01111100 #b01011110001101010100000))))
.def_46))))))))
(assert (let ((.def_60 (fp.mul RNE x2 (fp #b1 #b01111110 #b01011001000101101000100))))
(let ((.def_55 (fp.mul RNE x1 (fp #b0 #b01111110 #b01000101000111101011100))))
(let ((.def_51 (fp.mul RNE x0 (fp #b0 #b01111100 #b10101001111110111110100))))
(let ((.def_52 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_51)))
(let ((.def_56 (fp.add RNE .def_52 .def_55)))
(let ((.def_61 (fp.add RNE .def_56 .def_60)))
(let ((.def_62 (fp.leq (fp #b0 #b01111100 #b11001110110110010001011) .def_61)))
.def_62))))))))
(assert (let ((.def_76 (fp.mul RNE x2 (fp #b0 #b01111110 #b00000011100101011000001))))
(let ((.def_72 (fp.mul RNE x1 (fp #b1 #b01111011 #b10101001111110111110100))))
(let ((.def_67 (fp.mul RNE x0 (fp #b0 #b01111100 #b00000000000000000000000))))
(let ((.def_68 (fp.add RNE (fp #b0 #b00000000 #b00000000000000000000000) .def_67)))
(let ((.def_73 (fp.add RNE .def_68 .def_72)))
(let ((.def_77 (fp.add RNE .def_73 .def_76)))
(let ((.def_78 (fp.leq (fp #b0 #b01111110 #b11011011101001011110010) .def_77)))
.def_78))))))))
(check-sat)