(declare-fun |c::main::1::IN!0@1#0| () (_ FloatingPoint 8 24))
(assert (let ((.def_17 (fp.mul RNE |c::main::1::IN!0@1#0| |c::main::1::IN!0@1#0|)))
(let ((.def_25 (fp.mul RNE |c::main::1::IN!0@1#0| .def_17)))
(let ((.def_26 (fp.mul RNE |c::main::1::IN!0@1#0| .def_25)))
(let ((.def_31 (fp.mul RNE |c::main::1::IN!0@1#0| .def_26)))
(let ((.def_32 (fp.mul RNE |c::main::1::IN!0@1#0| .def_31)))
(let ((.def_35 (fp.div RNE .def_32 (fp #b0 #b10001000 #b01101000000000000000000))))
(let ((.def_29 (fp.div RNE .def_26 (fp #b0 #b10000011 #b10000000000000000000000))))
(let ((.def_20 (fp.div RNE .def_17 (fp #b0 #b10000000 #b00000000000000000000000))))
(let ((.def_21 (fp.neg .def_20)))
(let ((.def_24 (fp.add RNE .def_21 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_30 (fp.add RNE .def_24 .def_29)))
(let ((.def_36 (fp.add RNE .def_30 .def_35)))
(let ((.def_46 (fp.mul RNE |c::main::1::IN!0@1#0| .def_32)))
(let ((.def_49 (fp.div RNE .def_46 (fp #b0 #b10001011 #b00111011000000000000000))))
(let ((.def_44 (fp.div RNE .def_31 (fp #b0 #b10000101 #b11100000000000000000000))))
(let ((.def_39 (fp.div RNE .def_25 (fp #b0 #b10000001 #b10000000000000000000000))))
(let ((.def_40 (fp.neg .def_39)))
(let ((.def_41 (fp.add RNE |c::main::1::IN!0@1#0| .def_40)))
(let ((.def_45 (fp.add RNE .def_41 .def_44)))
(let ((.def_50 (fp.add RNE .def_45 .def_49)))
(let ((.def_51 (fp.div RNE .def_50 .def_36)))
(let ((.def_52 (fp.neg .def_51)))
(let ((.def_53 (fp.add RNE |c::main::1::IN!0@1#0| .def_52)))
(let ((.def_54 (fp.mul RNE .def_53 .def_53)))
(let ((.def_58 (fp.mul RNE .def_53 .def_54)))
(let ((.def_59 (fp.mul RNE .def_53 .def_58)))
(let ((.def_62 (fp.mul RNE .def_53 .def_59)))
(let ((.def_63 (fp.mul RNE .def_53 .def_62)))
(let ((.def_64 (fp.div RNE .def_63 (fp #b0 #b10001000 #b01101000000000000000000))))
(let ((.def_60 (fp.div RNE .def_59 (fp #b0 #b10000011 #b10000000000000000000000))))
(let ((.def_55 (fp.div RNE .def_54 (fp #b0 #b10000000 #b00000000000000000000000))))
(let ((.def_56 (fp.neg .def_55)))
(let ((.def_57 (fp.add RNE (fp #b0 #b01111111 #b00000000000000000000000) .def_56)))
(let ((.def_61 (fp.add RNE .def_57 .def_60)))
(let ((.def_65 (fp.add RNE .def_61 .def_64)))
(let ((.def_71 (fp.mul RNE .def_53 .def_63)))
(let ((.def_72 (fp.div RNE .def_71 (fp #b0 #b10001011 #b00111011000000000000000))))
(let ((.def_69 (fp.div RNE .def_62 (fp #b0 #b10000101 #b11100000000000000000000))))
(let ((.def_66 (fp.div RNE .def_58 (fp #b0 #b10000001 #b10000000000000000000000))))
(let ((.def_67 (fp.neg .def_66)))
(let ((.def_68 (fp.add RNE .def_53 .def_67)))
(let ((.def_70 (fp.add RNE .def_68 .def_69)))
(let ((.def_73 (fp.add RNE .def_70 .def_72)))
(let ((.def_74 (fp.div RNE .def_73 .def_65)))
(let ((.def_75 (fp.neg .def_74)))
(let ((.def_76 (fp.add RNE .def_53 .def_75)))
(let ((.def_77 (fp.mul RNE .def_76 .def_76)))
(let ((.def_81 (fp.mul RNE .def_76 .def_77)))
(let ((.def_82 (fp.mul RNE .def_76 .def_81)))
(let ((.def_85 (fp.mul RNE .def_76 .def_82)))
(let ((.def_86 (fp.mul RNE .def_76 .def_85)))
(let ((.def_87 (fp.div RNE .def_86 (fp #b0 #b10001000 #b01101000000000000000000))))
(let ((.def_83 (fp.div RNE .def_82 (fp #b0 #b10000011 #b10000000000000000000000))))
(let ((.def_78 (fp.div RNE .def_77 (fp #b0 #b10000000 #b00000000000000000000000))))
(let ((.def_79 (fp.neg .def_78)))
(let ((.def_80 (fp.add RNE (fp #b0 #b01111111 #b00000000000000000000000) .def_79)))
(let ((.def_84 (fp.add RNE .def_80 .def_83)))
(let ((.def_88 (fp.add RNE .def_84 .def_87)))
(let ((.def_94 (fp.mul RNE .def_76 .def_86)))
(let ((.def_95 (fp.div RNE .def_94 (fp #b0 #b10001011 #b00111011000000000000000))))
(let ((.def_92 (fp.div RNE .def_85 (fp #b0 #b10000101 #b11100000000000000000000))))
(let ((.def_89 (fp.div RNE .def_81 (fp #b0 #b10000001 #b10000000000000000000000))))
(let ((.def_90 (fp.neg .def_89)))
(let ((.def_91 (fp.add RNE .def_76 .def_90)))
(let ((.def_93 (fp.add RNE .def_91 .def_92)))
(let ((.def_96 (fp.add RNE .def_93 .def_95)))
(let ((.def_97 (fp.div RNE .def_96 .def_88)))
(let ((.def_98 (fp.neg .def_97)))
(let ((.def_99 (fp.add RNE .def_76 .def_98)))
(let ((.def_100 ((_ to_fp 11 53) RNE .def_99)))
(let ((.def_103 (fp.lt .def_100 (fp #b0 #b01111111011 #b1001100110011001100110011001100110011001100110011010))))
(let ((.def_104 (not .def_103)))
(let ((.def_15 (fp.lt (fp #b1 #b01111100 #b10011001100110011001101) |c::main::1::IN!0@1#0|)))
(let ((.def_12 (fp.lt |c::main::1::IN!0@1#0| (fp #b0 #b01111100 #b10011001100110011001101))))
(let ((.def_16 (and .def_12 .def_15)))
(let ((.def_105 (and .def_16 .def_104)))
.def_105)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
