(declare-fun b20 () (_ FloatingPoint 11 53))
(declare-fun b28 () (_ FloatingPoint 11 53))
(declare-fun b42 () (_ FloatingPoint 11 53))
(declare-fun b45 () (_ FloatingPoint 11 53))
(declare-fun b23 () (_ FloatingPoint 11 53))
(declare-fun b32 () (_ FloatingPoint 11 53))
(declare-fun b35 () (_ FloatingPoint 11 53))
(declare-fun b10 () (_ FloatingPoint 11 53))
(declare-fun b22 () (_ FloatingPoint 11 53))
(declare-fun b25 () (_ FloatingPoint 11 53))
(declare-fun b16 () (_ FloatingPoint 11 53))
(declare-fun b12 () (_ FloatingPoint 11 53))
(assert (let ((.def_39 (fp.leq b45 b23)))
(let ((.def_36 (fp.leq b23 b42)))
(let ((.def_32 (fp.leq b35 b22)))
(let ((.def_30 (fp.leq b22 b32)))
(let ((.def_27 (fp.leq b35 b10)))
(let ((.def_24 (fp.leq b10 b32)))
(let ((.def_21 (fp.leq b28 b20)))
(let ((.def_18 (fp.leq b20 b25)))
(let ((.def_14 (fp.leq b10 b12)))
(let ((.def_11 (fp.add RNE b10 b16)))
(let ((.def_13 (fp.lt b12 .def_11)))
(let ((.def_15 (and .def_13 .def_14)))
(let ((.def_19 (and .def_15 .def_18)))
(let ((.def_22 (and .def_19 .def_21)))
(let ((.def_25 (and .def_22 .def_24)))
(let ((.def_28 (and .def_25 .def_27)))
(let ((.def_31 (and .def_28 .def_30)))
(let ((.def_33 (and .def_31 .def_32)))
(let ((.def_37 (and .def_33 .def_36)))
(let ((.def_40 (and .def_37 .def_39)))
.def_40)))))))))))))))))))))
(check-sat)