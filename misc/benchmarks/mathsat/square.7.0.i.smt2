(declare-fun |c::main::1::IN!0@1#0| () (_ FloatingPoint 8 24))
(assert (let ((.def_45 (fp.leq (fp #b0 #b00000000 #b00000000000000000000000) |c::main::1::IN!0@1#0|)))
(let ((.def_44 (fp.lt |c::main::1::IN!0@1#0| (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_46 (and .def_44 .def_45)))
(let ((.def_30 (fp.mul RNE |c::main::1::IN!0@1#0| (fp #b0 #b01111010 #b01000000000000000000000))))
(let ((.def_31 (fp.mul RNE |c::main::1::IN!0@1#0| .def_30)))
(let ((.def_32 (fp.mul RNE |c::main::1::IN!0@1#0| .def_31)))
(let ((.def_33 (fp.mul RNE |c::main::1::IN!0@1#0| .def_32)))
(let ((.def_34 (fp.neg .def_33)))
(let ((.def_24 (fp.mul RNE |c::main::1::IN!0@1#0| (fp #b0 #b01111011 #b00000000000000000000000))))
(let ((.def_25 (fp.mul RNE |c::main::1::IN!0@1#0| .def_24)))
(let ((.def_26 (fp.mul RNE |c::main::1::IN!0@1#0| .def_25)))
(let ((.def_18 (fp.mul RNE |c::main::1::IN!0@1#0| (fp #b0 #b01111100 #b00000000000000000000000))))
(let ((.def_19 (fp.mul RNE |c::main::1::IN!0@1#0| .def_18)))
(let ((.def_20 (fp.neg .def_19)))
(let ((.def_12 (fp.mul RNE |c::main::1::IN!0@1#0| (fp #b0 #b01111110 #b00000000000000000000000))))
(let ((.def_15 (fp.add RNE .def_12 (fp #b0 #b01111111 #b00000000000000000000000))))
(let ((.def_21 (fp.add RNE .def_15 .def_20)))
(let ((.def_27 (fp.add RNE .def_21 .def_26)))
(let ((.def_35 (fp.add RNE .def_27 .def_34)))
(let ((.def_42 (fp.lt .def_35 (fp #b0 #b01111111 #b01100110011001100110011))))
(let ((.def_43 (not .def_42)))
(let ((.def_47 (and .def_43 .def_46)))
(let ((.def_38 (fp.leq (fp #b0 #b00000000 #b00000000000000000000000) .def_35)))
(let ((.def_39 (not .def_38)))
(let ((.def_48 (and .def_39 .def_47)))
.def_48))))))))))))))))))))))))))
(check-sat)
