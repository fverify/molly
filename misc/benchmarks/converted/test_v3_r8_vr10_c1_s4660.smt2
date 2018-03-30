(declare-fun lit_x0 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x0))
(declare-fun lit_x1 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x1))
(declare-fun lit_x2 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x2))
(define-fun lit_10 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 10.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_13 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 10.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun const_0 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_14 () (_ FloatingPoint 8 24) (fp.add RNE lit_x0 const_0))
(assert (fp.isNormal lit_14))
(define-fun lit_15 () Bool (fp.leq lit_13 lit_14))
(define-fun lit_16 () Bool (fp.leq lit_14 lit_10))
(define-fun lit_17 () Bool (and lit_15 lit_16))
(define-fun lit_18 () (_ FloatingPoint 8 24) (fp.add RNE lit_x1 const_0))
(assert (fp.isNormal lit_18))
(define-fun lit_19 () Bool (fp.leq lit_13 lit_18))
(define-fun lit_20 () Bool (fp.leq lit_18 lit_10))
(define-fun lit_21 () Bool (and lit_19 lit_20))
(define-fun lit_22 () (_ FloatingPoint 8 24) (fp.add RNE lit_x2 const_0))
(assert (fp.isNormal lit_22))
(define-fun lit_23 () Bool (fp.leq lit_13 lit_22))
(define-fun lit_24 () Bool (fp.leq lit_22 lit_10))
(define-fun lit_25 () Bool (and lit_23 lit_24))
(define-fun lit_12 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_31 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.144999995827674865722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_33 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.458000004291534423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_34 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_33))
(assert (fp.isNormal lit_34))
(define-fun lit_35 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_34))
(assert (fp.isNormal lit_35))
(define-fun lit_37 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.239999994635581970214843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_38 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_37))
(assert (fp.isNormal lit_38))
(define-fun lit_39 () (_ FloatingPoint 8 24) (fp.add RNE lit_35 lit_38))
(assert (fp.isNormal lit_39))
(define-fun lit_41 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.175999999046325683593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_42 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_41))
(assert (fp.isNormal lit_42))
(define-fun lit_43 () (_ FloatingPoint 8 24) (fp.add RNE lit_39 lit_42))
(assert (fp.isNormal lit_43))
(define-fun lit_44 () Bool (fp.leq lit_31 lit_43))
(define-fun lit_46 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.174999997019767761230468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_48 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.564000010490417480468750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_49 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_48))
(assert (fp.isNormal lit_49))
(define-fun lit_50 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_49))
(assert (fp.isNormal lit_50))
(define-fun lit_53 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.694000005722045898437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_54 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_53))
(assert (fp.isNormal lit_54))
(define-fun lit_55 () (_ FloatingPoint 8 24) (fp.add RNE lit_50 lit_54))
(assert (fp.isNormal lit_55))
(define-fun lit_58 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.412999987602233886718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_59 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_58))
(assert (fp.isNormal lit_59))
(define-fun lit_60 () (_ FloatingPoint 8 24) (fp.add RNE lit_55 lit_59))
(assert (fp.isNormal lit_60))
(define-fun lit_61 () Bool (fp.leq lit_60 lit_46))
(define-fun lit_63 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.547999978065490722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_66 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.637000024318695068359375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_67 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_66))
(assert (fp.isNormal lit_67))
(define-fun lit_68 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_67))
(assert (fp.isNormal lit_68))
(define-fun lit_70 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.391999989748001098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_71 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_70))
(assert (fp.isNormal lit_71))
(define-fun lit_72 () (_ FloatingPoint 8 24) (fp.add RNE lit_68 lit_71))
(assert (fp.isNormal lit_72))
(define-fun lit_75 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.967999994754791259765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_76 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_75))
(assert (fp.isNormal lit_76))
(define-fun lit_77 () (_ FloatingPoint 8 24) (fp.add RNE lit_72 lit_76))
(assert (fp.isNormal lit_77))
(define-fun lit_78 () Bool (fp.leq lit_63 lit_77))
(define-fun lit_81 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.097999997437000274658203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_83 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.875999987125396728515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_84 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_83))
(assert (fp.isNormal lit_84))
(define-fun lit_85 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_84))
(assert (fp.isNormal lit_85))
(define-fun lit_87 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.219999998807907104492187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_88 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_87))
(assert (fp.isNormal lit_88))
(define-fun lit_89 () (_ FloatingPoint 8 24) (fp.add RNE lit_85 lit_88))
(assert (fp.isNormal lit_89))
(define-fun lit_92 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.879000008106231689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_93 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_92))
(assert (fp.isNormal lit_93))
(define-fun lit_94 () (_ FloatingPoint 8 24) (fp.add RNE lit_89 lit_93))
(assert (fp.isNormal lit_94))
(define-fun lit_95 () Bool (fp.leq lit_94 lit_81))
(define-fun lit_98 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.039999999105930328369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_100 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.391000002622604370117187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_101 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_100))
(assert (fp.isNormal lit_101))
(define-fun lit_102 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_101))
(assert (fp.isNormal lit_102))
(define-fun lit_104 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.938000023365020751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_105 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_104))
(assert (fp.isNormal lit_105))
(define-fun lit_106 () (_ FloatingPoint 8 24) (fp.add RNE lit_102 lit_105))
(assert (fp.isNormal lit_106))
(define-fun lit_108 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.177000001072883605957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_109 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_108))
(assert (fp.isNormal lit_109))
(define-fun lit_110 () (_ FloatingPoint 8 24) (fp.add RNE lit_106 lit_109))
(assert (fp.isNormal lit_110))
(define-fun lit_111 () Bool (fp.leq lit_98 lit_110))
(define-fun lit_113 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.234999999403953552246093750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_115 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.261999994516372680664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_116 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_115))
(assert (fp.isNormal lit_116))
(define-fun lit_117 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_116))
(assert (fp.isNormal lit_117))
(define-fun lit_119 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.675000011920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_120 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_119))
(assert (fp.isNormal lit_120))
(define-fun lit_121 () (_ FloatingPoint 8 24) (fp.add RNE lit_117 lit_120))
(assert (fp.isNormal lit_121))
(define-fun lit_124 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.620999991893768310546875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_125 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_124))
(assert (fp.isNormal lit_125))
(define-fun lit_126 () (_ FloatingPoint 8 24) (fp.add RNE lit_121 lit_125))
(assert (fp.isNormal lit_126))
(define-fun lit_127 () Bool (fp.leq lit_113 lit_126))
(define-fun lit_130 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.021999999880790710449218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_133 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.375999987125396728515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_134 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_133))
(assert (fp.isNormal lit_134))
(define-fun lit_135 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_134))
(assert (fp.isNormal lit_135))
(define-fun lit_138 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.518000006675720214843750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_139 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_138))
(assert (fp.isNormal lit_139))
(define-fun lit_140 () (_ FloatingPoint 8 24) (fp.add RNE lit_135 lit_139))
(assert (fp.isNormal lit_140))
(define-fun lit_142 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.149000003933906555175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_143 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_142))
(assert (fp.isNormal lit_143))
(define-fun lit_144 () (_ FloatingPoint 8 24) (fp.add RNE lit_140 lit_143))
(assert (fp.isNormal lit_144))
(define-fun lit_145 () Bool (fp.leq lit_144 lit_130))
(define-fun lit_148 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.048999998718500137329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_151 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.667999982833862304687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_152 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_151))
(assert (fp.isNormal lit_152))
(define-fun lit_153 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_152))
(assert (fp.isNormal lit_153))
(define-fun lit_155 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.263999998569488525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_156 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_155))
(assert (fp.isNormal lit_156))
(define-fun lit_157 () (_ FloatingPoint 8 24) (fp.add RNE lit_153 lit_156))
(assert (fp.isNormal lit_157))
(define-fun lit_160 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.551999986171722412109375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_161 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_160))
(assert (fp.isNormal lit_161))
(define-fun lit_162 () (_ FloatingPoint 8 24) (fp.add RNE lit_157 lit_161))
(assert (fp.isNormal lit_162))
(define-fun lit_163 () Bool (fp.leq lit_162 lit_148))
(define-fun top_level_new0 () Bool (and lit_44 lit_127))
(define-fun top_level_new1 () Bool (and top_level_new0 lit_145))
(define-fun top_level_new2 () Bool (and top_level_new1 lit_163))
(define-fun top_level_new3 () Bool (and top_level_new2 lit_78))
(define-fun top_level_new4 () Bool (and top_level_new3 lit_95))
(define-fun top_level_new5 () Bool (and top_level_new4 lit_25))
(define-fun top_level_new6 () Bool (and top_level_new5 lit_21))
(define-fun top_level_new7 () Bool (and top_level_new6 lit_17))
(define-fun top_level_new8 () Bool (and top_level_new7 lit_61))
(define-fun propexp () Bool (and top_level_new8 lit_111))
(assert propexp)
(check-sat)
;(get-model)
(exit)