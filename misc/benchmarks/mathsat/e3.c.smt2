(declare-fun b13 () (_ FloatingPoint 11 53))
(declare-fun b25 () (_ FloatingPoint 11 53))
(declare-fun b22 () (_ FloatingPoint 11 53))
(declare-fun b82 () (_ FloatingPoint 11 53))
(declare-fun b14 () (_ FloatingPoint 11 53))
(declare-fun b34 () (_ FloatingPoint 11 53))
(declare-fun b43 () (_ FloatingPoint 11 53))
(declare-fun b85 () (_ FloatingPoint 11 53))
(declare-fun b16 () (_ FloatingPoint 11 53))
(declare-fun b131 () (_ FloatingPoint 11 53))
(declare-fun b126 () (_ FloatingPoint 11 53))
(assert (let ((.def_33 (fp.add RNE b13 b14)))
(let ((.def_63 (fp.lt .def_33 b126)))
(let ((.def_26 (fp.neg b14)))
(let ((.def_27 (fp.add RNE b13 .def_26)))
(let ((.def_61 (fp.lt .def_27 b131)))
(let ((.def_19 (fp.mul RNE b13 b25)))
(let ((.def_58 (fp.add RNE b131 b126)))
(let ((.def_59 (fp.lt .def_58 .def_19)))
(let ((.def_56 (fp.leq b22 b82)))
(let ((.def_54 (fp.leq b85 b22)))
(let ((.def_52 (fp.leq b16 b82)))
(let ((.def_50 (fp.leq b85 b16)))
(let ((.def_48 (fp.leq b13 b82)))
(let ((.def_46 (fp.leq b85 b13)))
(let ((.def_44 (fp.leq b14 b82)))
(let ((.def_41 (fp.leq b85 b14)))
(let ((.def_38 (= b131 b22)))
(let ((.def_36 (= b126 b16)))
(let ((.def_34 (fp.lt .def_33 b16)))
(let ((.def_35 (not .def_34)))
(let ((.def_37 (and .def_35 .def_36)))
(let ((.def_39 (and .def_37 .def_38)))
(let ((.def_42 (and .def_39 .def_41)))
(let ((.def_45 (and .def_42 .def_44)))
(let ((.def_47 (and .def_45 .def_46)))
(let ((.def_49 (and .def_47 .def_48)))
(let ((.def_51 (and .def_49 .def_50)))
(let ((.def_53 (and .def_51 .def_52)))
(let ((.def_55 (and .def_53 .def_54)))
(let ((.def_57 (and .def_55 .def_56)))
(let ((.def_60 (and .def_57 .def_59)))
(let ((.def_62 (and .def_60 .def_61)))
(let ((.def_64 (and .def_62 .def_63)))
(let ((.def_30 (fp.mul RNE b13 b14)))
(let ((.def_31 (fp.lt .def_30 b16)))
(let ((.def_32 (not .def_31)))
(let ((.def_65 (and .def_32 .def_64)))
(let ((.def_28 (fp.lt .def_27 b22)))
(let ((.def_29 (not .def_28)))
(let ((.def_66 (and .def_29 .def_65)))
(let ((.def_22 (fp.add RNE b16 b22)))
(let ((.def_23 (fp.lt .def_22 .def_19)))
(let ((.def_24 (not .def_23)))
(let ((.def_67 (and .def_24 .def_66)))
(let ((.def_15 (= b126 b34)))
(let ((.def_16 (not .def_15)))
(let ((.def_68 (and .def_16 .def_67)))
(let ((.def_11 (= b131 b43)))
(let ((.def_12 (not .def_11)))
(let ((.def_69 (and .def_12 .def_68)))
.def_69)))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)