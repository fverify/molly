(declare-fun |c::main::1::IN!0@1#0| () (_ FloatingPoint 8 24))
(assert (let ((.def_17 (fp.mul RNE |c::main::1::IN!0@1#0| |c::main::1::IN!0@1#0|)))
(let ((.def_23 (fp.mul RNE |c::main::1::IN!0@1#0| .def_17)))
(let ((.def_24 (fp.mul RNE |c::main::1::IN!0@1#0| .def_23)))
(let ((.def_29 (fp.mul RNE |c::main::1::IN!0@1#0| .def_24)))
(let ((.def_30 (fp.mul RNE |c::main::1::IN!0@1#0| .def_29)))
(let ((.def_33 (fp.div RNE .def_30 (fp #b0 #b10001000 #b01101000000000000000000))))
(let ((.def_27 (fp.div RNE .def_24 (fp #b0 #b10000011 #b10000000000000000000000))))
(let ((.def_18 (fp.div RNE .def_17 (fp #b0 #b10000000 #b00000000000000000000000))))
(let ((.def_19 (fp.neg .def_18)))
(let ((.def_22 (fp.add RNE .def_19 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_28 (fp.add RNE .def_22 .def_27)))
(let ((.def_34 (fp.add RNE .def_28 .def_33)))
(let ((.def_44 (fp.mul RNE |c::main::1::IN!0@1#0| .def_30)))
(let ((.def_47 (fp.div RNE .def_44 (fp #b0 #b10001011 #b00111011000000000000000))))
(let ((.def_42 (fp.div RNE .def_29 (fp #b0 #b10000101 #b11100000000000000000000))))
(let ((.def_37 (fp.div RNE .def_23 (fp #b0 #b10000001 #b10000000000000000000000))))
(let ((.def_38 (fp.neg .def_37)))
(let ((.def_39 (fp.add RNE |c::main::1::IN!0@1#0| .def_38)))
(let ((.def_43 (fp.add RNE .def_39 .def_42)))
(let ((.def_48 (fp.add RNE .def_43 .def_47)))
(let ((.def_49 (fp.div RNE .def_48 .def_34)))
(let ((.def_50 (fp.neg .def_49)))
(let ((.def_51 (fp.add RNE |c::main::1::IN!0@1#0| .def_50)))
(let ((.def_52 ((_ to_fp 11 53) RNE .def_51)))
(let ((.def_55 (fp.lt .def_52 (fp #b0 #b01111111011 #b1001100110011001100110011001100110011001100110011010))))
(let ((.def_56 (not .def_55)))
(let ((.def_15 (fp.lt (fp #b1 #b10000000 #b00000000000000000000000) |c::main::1::IN!0@1#0|)))
(let ((.def_12 (fp.lt |c::main::1::IN!0@1#0| (fp #b0 #b10000000 #b00000000000000000000000))))
(let ((.def_16 (and .def_12 .def_15)))
(let ((.def_57 (and .def_16 .def_56)))
.def_57)))))))))))))))))))))))))))))))
(check-sat)
