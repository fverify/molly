(declare-fun |c::main::1::c!0@1#1| () (_ FloatingPoint 8 24))
(declare-fun |goto_symex::&92;guard#1| () Bool)
(declare-fun |c::main::1::b!0@1#1| () (_ FloatingPoint 8 24))
(declare-fun |c::main::1::a!0@1#1| () (_ FloatingPoint 8 24))
(assert (let ((.def_19 (fp.add RNE |c::main::1::a!0@1#1| |c::main::1::b!0@1#1|)))
(let ((.def_20 (fp.add RNE |c::main::1::c!0@1#1| .def_19)))
(let ((.def_16 (fp.add RNE |c::main::1::b!0@1#1| |c::main::1::c!0@1#1|)))
(let ((.def_17 (fp.add RNE |c::main::1::a!0@1#1| .def_16)))
(let ((.def_18 (fp.neg .def_17)))
(let ((.def_21 (fp.add RNE .def_18 .def_20)))
(let ((.def_24 (fp.leq .def_21 (fp #b0 #b10000010 #b01000000000000000000000))))
(let ((.def_68 (not .def_24)))
(let ((.def_63 ((_ to_fp 11 53) RNE .def_17)))
(let ((.def_65 (fp.lt (_ -oo 11 53) .def_63)))
(let ((.def_64 (fp.lt .def_63 (_ +oo 11 53))))
(let ((.def_66 (and .def_64 .def_65)))
(let ((.def_56 ((_ to_fp 11 53) RNE .def_20)))
(let ((.def_60 (fp.lt (_ -oo 11 53) .def_56)))
(let ((.def_58 (fp.lt .def_56 (_ +oo 11 53))))
(let ((.def_61 (and .def_58 .def_60)))
(let ((.def_49 (fp.neg |c::main::1::c!0@1#1|)))
(let ((.def_53 (fp.add RNE |c::main::1::b!0@1#1| .def_49)))
(let ((.def_54 (fp.leq .def_53 (fp #b0 #b01111011 #b10011001100110011001101))))
(let ((.def_50 (fp.add RNE |c::main::1::a!0@1#1| .def_49)))
(let ((.def_51 (fp.leq .def_50 (fp #b0 #b01111011 #b10011001100110011001101))))
(let ((.def_43 (fp.neg |c::main::1::b!0@1#1|)))
(let ((.def_44 (fp.add RNE |c::main::1::a!0@1#1| .def_43)))
(let ((.def_47 (fp.leq .def_44 (fp #b0 #b01111011 #b10011001100110011001101))))
(let ((.def_41 (fp.leq |c::main::1::c!0@1#1| |c::main::1::b!0@1#1|)))
(let ((.def_39 (fp.leq |c::main::1::b!0@1#1| |c::main::1::a!0@1#1|)))
(let ((.def_34 ((_ to_fp 11 53) RNE |c::main::1::c!0@1#1|)))
(let ((.def_37 (fp.lt (fp #b1 #b10000001111 #b1000011010100000000000000000000000000000000000000000) .def_34)))
(let ((.def_35 (fp.lt .def_34 (fp #b0 #b10000001111 #b1000011010100000000000000000000000000000000000000000))))
(let ((.def_29 ((_ to_fp 11 53) RNE |c::main::1::b!0@1#1|)))
(let ((.def_32 (fp.lt (fp #b1 #b10000001111 #b1000011010100000000000000000000000000000000000000000) .def_29)))
(let ((.def_30 (fp.lt .def_29 (fp #b0 #b10000001111 #b1000011010100000000000000000000000000000000000000000))))
(let ((.def_10 ((_ to_fp 11 53) RNE |c::main::1::a!0@1#1|)))
(let ((.def_27 (fp.lt (fp #b1 #b10000001111 #b1000011010100000000000000000000000000000000000000000) .def_10)))
(let ((.def_13 (fp.lt .def_10 (fp #b0 #b10000001111 #b1000011010100000000000000000000000000000000000000000))))
(let ((.def_28 (and .def_13 .def_27)))
(let ((.def_31 (and .def_28 .def_30)))
(let ((.def_33 (and .def_31 .def_32)))
(let ((.def_36 (and .def_33 .def_35)))
(let ((.def_38 (and .def_36 .def_37)))
(let ((.def_40 (and .def_38 .def_39)))
(let ((.def_42 (and .def_40 .def_41)))
(let ((.def_48 (and .def_42 .def_47)))
(let ((.def_52 (and .def_48 .def_51)))
(let ((.def_55 (and .def_52 .def_54)))
(let ((.def_62 (and .def_55 .def_61)))
(let ((.def_67 (and .def_62 .def_66)))
(let ((.def_69 (and .def_67 .def_68)))
.def_69)))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
