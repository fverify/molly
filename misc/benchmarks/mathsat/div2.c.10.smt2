(declare-fun b38 () (_ FloatingPoint 8 24))
(declare-fun b26 () (_ FloatingPoint 8 24))
(declare-fun b14 () (_ FloatingPoint 8 24))
(declare-fun b29 () (_ FloatingPoint 8 24))
(declare-fun b35 () (_ FloatingPoint 8 24))
(declare-fun b20 () (_ FloatingPoint 8 24))
(declare-fun b17 () (_ FloatingPoint 8 24))
(declare-fun b10 () (_ FloatingPoint 8 24))
(declare-fun b32 () (_ FloatingPoint 8 24))
(declare-fun b11 () (_ FloatingPoint 8 24))
(declare-fun b41 () (_ FloatingPoint 8 24))
(declare-fun b23 () (_ FloatingPoint 8 24))
(assert (let ((.def_70 (fp.leq b41 b38)))
(let ((.def_12 (fp.div RNE b10 b11)))
(let ((.def_14 (fp.div RNE .def_12 b14)))
(let ((.def_16 (fp.div RNE .def_14 b17)))
(let ((.def_18 (fp.div RNE .def_16 b20)))
(let ((.def_20 (fp.div RNE .def_18 b23)))
(let ((.def_22 (fp.div RNE .def_20 b26)))
(let ((.def_24 (fp.div RNE .def_22 b29)))
(let ((.def_26 (fp.div RNE .def_24 b32)))
(let ((.def_28 (fp.div RNE .def_26 b35)))
(let ((.def_68 (fp.lt b38 .def_28)))
(let ((.def_66 (fp.leq b41 b35)))
(let ((.def_64 (fp.lt b35 .def_26)))
(let ((.def_62 (fp.leq b41 b32)))
(let ((.def_60 (fp.lt b32 .def_24)))
(let ((.def_58 (fp.leq b41 b29)))
(let ((.def_56 (fp.lt b29 .def_22)))
(let ((.def_54 (fp.leq b41 b26)))
(let ((.def_52 (fp.lt b26 .def_20)))
(let ((.def_50 (fp.leq b41 b23)))
(let ((.def_48 (fp.lt b23 .def_18)))
(let ((.def_46 (fp.leq b41 b20)))
(let ((.def_44 (fp.lt b20 .def_16)))
(let ((.def_42 (fp.leq b41 b17)))
(let ((.def_40 (fp.lt b17 .def_14)))
(let ((.def_38 (fp.leq b41 b14)))
(let ((.def_36 (fp.lt b14 .def_12)))
(let ((.def_34 (fp.leq b41 b11)))
(let ((.def_30 (fp.div RNE .def_28 b38)))
(let ((.def_32 (fp.lt .def_30 b41)))
(let ((.def_11 (fp.lt b11 b10)))
(let ((.def_33 (and .def_11 .def_32)))
(let ((.def_35 (and .def_33 .def_34)))
(let ((.def_37 (and .def_35 .def_36)))
(let ((.def_39 (and .def_37 .def_38)))
(let ((.def_41 (and .def_39 .def_40)))
(let ((.def_43 (and .def_41 .def_42)))
(let ((.def_45 (and .def_43 .def_44)))
(let ((.def_47 (and .def_45 .def_46)))
(let ((.def_49 (and .def_47 .def_48)))
(let ((.def_51 (and .def_49 .def_50)))
(let ((.def_53 (and .def_51 .def_52)))
(let ((.def_55 (and .def_53 .def_54)))
(let ((.def_57 (and .def_55 .def_56)))
(let ((.def_59 (and .def_57 .def_58)))
(let ((.def_61 (and .def_59 .def_60)))
(let ((.def_63 (and .def_61 .def_62)))
(let ((.def_65 (and .def_63 .def_64)))
(let ((.def_67 (and .def_65 .def_66)))
(let ((.def_69 (and .def_67 .def_68)))
(let ((.def_71 (and .def_69 .def_70)))
.def_71))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
