(declare-fun b37 () (_ FloatingPoint 8 24))
(declare-fun b69 () (_ FloatingPoint 8 24))
(declare-fun b72 () (_ FloatingPoint 8 24))
(declare-fun b31 () (_ FloatingPoint 8 24))
(declare-fun b13 () (_ FloatingPoint 8 24))
(declare-fun b34 () (_ FloatingPoint 8 24))
(declare-fun b22 () (_ FloatingPoint 8 24))
(declare-fun b11 () (_ FloatingPoint 8 24))
(declare-fun b41 () (_ FloatingPoint 11 53))
(declare-fun b28 () (_ FloatingPoint 8 24))
(declare-fun b16 () (_ FloatingPoint 8 24))
(declare-fun b25 () (_ FloatingPoint 8 24))
(declare-fun b19 () (_ FloatingPoint 8 24))
(assert (let ((.def_71 (fp.lt b37 b72)))
(let ((.def_69 (fp.lt b69 b37)))
(let ((.def_67 (fp.lt b34 b72)))
(let ((.def_65 (fp.lt b69 b34)))
(let ((.def_63 (fp.lt b31 b72)))
(let ((.def_61 (fp.lt b69 b31)))
(let ((.def_59 (fp.lt b28 b72)))
(let ((.def_57 (fp.lt b69 b28)))
(let ((.def_55 (fp.lt b25 b72)))
(let ((.def_53 (fp.lt b69 b25)))
(let ((.def_51 (fp.lt b22 b72)))
(let ((.def_49 (fp.lt b69 b22)))
(let ((.def_47 (fp.lt b19 b72)))
(let ((.def_45 (fp.lt b69 b19)))
(let ((.def_43 (fp.lt b16 b72)))
(let ((.def_41 (fp.lt b69 b16)))
(let ((.def_39 (fp.lt b13 b72)))
(let ((.def_37 (fp.lt b69 b13)))
(let ((.def_35 (fp.lt b11 b72)))
(let ((.def_13 (fp.mul RNE b11 b13)))
(let ((.def_15 (fp.mul RNE .def_13 b16)))
(let ((.def_17 (fp.mul RNE .def_15 b19)))
(let ((.def_19 (fp.mul RNE .def_17 b22)))
(let ((.def_21 (fp.mul RNE .def_19 b25)))
(let ((.def_23 (fp.mul RNE .def_21 b28)))
(let ((.def_25 (fp.mul RNE .def_23 b31)))
(let ((.def_27 (fp.mul RNE .def_25 b34)))
(let ((.def_29 (fp.mul RNE .def_27 b37)))
(let ((.def_30 ((_ to_fp 11 53) RNE .def_29)))
(let ((.def_32 (fp.lt b41 .def_30)))
(let ((.def_11 (fp.lt b69 b11)))
(let ((.def_33 (and .def_11 .def_32)))
(let ((.def_36 (and .def_33 .def_35)))
(let ((.def_38 (and .def_36 .def_37)))
(let ((.def_40 (and .def_38 .def_39)))
(let ((.def_42 (and .def_40 .def_41)))
(let ((.def_44 (and .def_42 .def_43)))
(let ((.def_46 (and .def_44 .def_45)))
(let ((.def_48 (and .def_46 .def_47)))
(let ((.def_50 (and .def_48 .def_49)))
(let ((.def_52 (and .def_50 .def_51)))
(let ((.def_54 (and .def_52 .def_53)))
(let ((.def_56 (and .def_54 .def_55)))
(let ((.def_58 (and .def_56 .def_57)))
(let ((.def_60 (and .def_58 .def_59)))
(let ((.def_62 (and .def_60 .def_61)))
(let ((.def_64 (and .def_62 .def_63)))
(let ((.def_66 (and .def_64 .def_65)))
(let ((.def_68 (and .def_66 .def_67)))
(let ((.def_70 (and .def_68 .def_69)))
(let ((.def_72 (and .def_70 .def_71)))
.def_72))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
