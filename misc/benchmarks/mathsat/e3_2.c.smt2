(declare-fun b51 () (_ FloatingPoint 11 53))
(declare-fun b13 () (_ FloatingPoint 11 53))
(declare-fun b10 () (_ FloatingPoint 11 53))
(declare-fun b11 () (_ FloatingPoint 11 53))
(declare-fun b17 () (_ FloatingPoint 11 53))
(declare-fun b54 () (_ FloatingPoint 11 53))
(declare-fun b20 () (_ FloatingPoint 11 53))
(assert (let ((.def_40 (fp.leq b54 b17)))
(let ((.def_38 (fp.leq b17 b51)))
(let ((.def_36 (fp.leq b54 b13)))
(let ((.def_34 (fp.leq b13 b51)))
(let ((.def_32 (fp.leq b54 b11)))
(let ((.def_30 (fp.leq b11 b51)))
(let ((.def_28 (fp.leq b54 b10)))
(let ((.def_25 (fp.leq b10 b51)))
(let ((.def_21 (fp.add RNE b11 b10)))
(let ((.def_22 (fp.lt .def_21 b13)))
(let ((.def_16 (fp.mul RNE b10 b20)))
(let ((.def_18 (fp.add RNE b17 b13)))
(let ((.def_19 (fp.lt .def_18 .def_16)))
(let ((.def_10 (fp.neg b11)))
(let ((.def_12 (fp.add RNE .def_10 b10)))
(let ((.def_14 (fp.lt .def_12 b17)))
(let ((.def_20 (and .def_14 .def_19)))
(let ((.def_23 (and .def_20 .def_22)))
(let ((.def_26 (and .def_23 .def_25)))
(let ((.def_29 (and .def_26 .def_28)))
(let ((.def_31 (and .def_29 .def_30)))
(let ((.def_33 (and .def_31 .def_32)))
(let ((.def_35 (and .def_33 .def_34)))
(let ((.def_37 (and .def_35 .def_36)))
(let ((.def_39 (and .def_37 .def_38)))
(let ((.def_41 (and .def_39 .def_40)))
.def_41)))))))))))))))))))))))))))
(check-sat)