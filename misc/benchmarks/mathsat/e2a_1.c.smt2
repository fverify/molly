(declare-fun b34 () (_ FloatingPoint 11 53))
(declare-fun b31 () (_ FloatingPoint 11 53))
(declare-fun b22 () (_ FloatingPoint 11 53))
(declare-fun b12 () (_ FloatingPoint 11 53))
(declare-fun b27 () (_ FloatingPoint 11 53))
(declare-fun b16 () (_ FloatingPoint 11 53))
(declare-fun b10 () (_ FloatingPoint 11 53))
(declare-fun b24 () (_ FloatingPoint 11 53))
(assert (let ((.def_27 (fp.leq b34 b22)))
(let ((.def_24 (fp.leq b22 b31)))
(let ((.def_20 (fp.leq b27 b10)))
(let ((.def_17 (fp.leq b10 b24)))
(let ((.def_14 (fp.leq b10 b12)))
(let ((.def_11 (fp.add RNE b10 b16)))
(let ((.def_13 (fp.lt b12 .def_11)))
(let ((.def_15 (and .def_13 .def_14)))
(let ((.def_18 (and .def_15 .def_17)))
(let ((.def_21 (and .def_18 .def_20)))
(let ((.def_25 (and .def_21 .def_24)))
(let ((.def_28 (and .def_25 .def_27)))
.def_28)))))))))))))
(check-sat)
(exit)
