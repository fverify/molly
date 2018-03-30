(declare-fun lit_x0 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x0))
(declare-fun lit_x1 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x1))
(declare-fun lit_x2 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x2))
(declare-fun lit_x3 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x3))
(declare-fun lit_x4 () (_ FloatingPoint 8 24))
(assert (fp.isNormal lit_x4))
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
(define-fun lit_26 () (_ FloatingPoint 8 24) (fp.add RNE lit_x3 const_0))
(assert (fp.isNormal lit_26))
(define-fun lit_27 () Bool (fp.leq lit_13 lit_26))
(define-fun lit_28 () Bool (fp.leq lit_26 lit_10))
(define-fun lit_29 () Bool (and lit_27 lit_28))
(define-fun lit_30 () (_ FloatingPoint 8 24) (fp.add RNE lit_x4 const_0))
(assert (fp.isNormal lit_30))
(define-fun lit_31 () Bool (fp.leq lit_13 lit_30))
(define-fun lit_32 () Bool (fp.leq lit_30 lit_10))
(define-fun lit_33 () Bool (and lit_31 lit_32))
(define-fun lit_12 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_39 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.218999996781349182128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_42 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.430000007152557373046875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_43 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_42))
(assert (fp.isNormal lit_43))
(define-fun lit_44 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_43))
(assert (fp.isNormal lit_44))
(define-fun lit_46 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.166999995708465576171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_47 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_46))
(assert (fp.isNormal lit_47))
(define-fun lit_48 () (_ FloatingPoint 8 24) (fp.add RNE lit_44 lit_47))
(assert (fp.isNormal lit_48))
(define-fun lit_50 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.950999975204467773437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_51 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_50))
(assert (fp.isNormal lit_51))
(define-fun lit_52 () (_ FloatingPoint 8 24) (fp.add RNE lit_48 lit_51))
(assert (fp.isNormal lit_52))
(define-fun lit_54 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.460999995470046997070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_55 () (_ FloatingPoint 8 24) (fp.mul RNE lit_26 lit_54))
(assert (fp.isNormal lit_55))
(define-fun lit_56 () (_ FloatingPoint 8 24) (fp.add RNE lit_52 lit_55))
(assert (fp.isNormal lit_56))
(define-fun lit_59 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.284000009298324584960937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_60 () (_ FloatingPoint 8 24) (fp.mul RNE lit_30 lit_59))
(assert (fp.isNormal lit_60))
(define-fun lit_61 () (_ FloatingPoint 8 24) (fp.add RNE lit_56 lit_60))
(assert (fp.isNormal lit_61))
(define-fun lit_62 () Bool (fp.leq lit_61 lit_39))
(define-fun lit_64 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.402000010013580322265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_67 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.675999999046325683593750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_68 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_67))
(assert (fp.isNormal lit_68))
(define-fun lit_69 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_68))
(assert (fp.isNormal lit_69))
(define-fun lit_71 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.067000001668930053710937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_72 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_71))
(assert (fp.isNormal lit_72))
(define-fun lit_73 () (_ FloatingPoint 8 24) (fp.add RNE lit_69 lit_72))
(assert (fp.isNormal lit_73))
(define-fun lit_75 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.280000001192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_76 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_75))
(assert (fp.isNormal lit_76))
(define-fun lit_77 () (_ FloatingPoint 8 24) (fp.add RNE lit_73 lit_76))
(assert (fp.isNormal lit_77))
(define-fun lit_79 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.723999977111816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_80 () (_ FloatingPoint 8 24) (fp.mul RNE lit_26 lit_79))
(assert (fp.isNormal lit_80))
(define-fun lit_81 () (_ FloatingPoint 8 24) (fp.add RNE lit_77 lit_80))
(assert (fp.isNormal lit_81))
(define-fun lit_83 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.660000026226043701171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_84 () (_ FloatingPoint 8 24) (fp.mul RNE lit_30 lit_83))
(assert (fp.isNormal lit_84))
(define-fun lit_85 () (_ FloatingPoint 8 24) (fp.add RNE lit_81 lit_84))
(assert (fp.isNormal lit_85))
(define-fun lit_86 () Bool (fp.leq lit_64 lit_85))
(define-fun lit_88 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.578000009059906005859375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_90 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.720000028610229492187500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_91 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_90))
(assert (fp.isNormal lit_91))
(define-fun lit_92 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_91))
(assert (fp.isNormal lit_92))
(define-fun lit_95 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.328999996185302734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_96 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_95))
(assert (fp.isNormal lit_96))
(define-fun lit_97 () (_ FloatingPoint 8 24) (fp.add RNE lit_92 lit_96))
(assert (fp.isNormal lit_97))
(define-fun lit_99 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.602999985218048095703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_100 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_99))
(assert (fp.isNormal lit_100))
(define-fun lit_101 () (_ FloatingPoint 8 24) (fp.add RNE lit_97 lit_100))
(assert (fp.isNormal lit_101))
(define-fun lit_104 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.607999980449676513671875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_105 () (_ FloatingPoint 8 24) (fp.mul RNE lit_26 lit_104))
(assert (fp.isNormal lit_105))
(define-fun lit_106 () (_ FloatingPoint 8 24) (fp.add RNE lit_101 lit_105))
(assert (fp.isNormal lit_106))
(define-fun lit_108 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.764999985694885253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_109 () (_ FloatingPoint 8 24) (fp.mul RNE lit_30 lit_108))
(assert (fp.isNormal lit_109))
(define-fun lit_110 () (_ FloatingPoint 8 24) (fp.add RNE lit_106 lit_109))
(assert (fp.isNormal lit_110))
(define-fun lit_111 () Bool (fp.leq lit_110 lit_88))
(define-fun lit_113 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.234999999403953552246093750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_116 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.254000008106231689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_117 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_116))
(assert (fp.isNormal lit_117))
(define-fun lit_118 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_117))
(assert (fp.isNormal lit_118))
(define-fun lit_120 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.411000013351440429687500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_121 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_120))
(assert (fp.isNormal lit_121))
(define-fun lit_122 () (_ FloatingPoint 8 24) (fp.add RNE lit_118 lit_121))
(assert (fp.isNormal lit_122))
(define-fun lit_124 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.703999996185302734375000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_125 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_124))
(assert (fp.isNormal lit_125))
(define-fun lit_126 () (_ FloatingPoint 8 24) (fp.add RNE lit_122 lit_125))
(assert (fp.isNormal lit_126))
(define-fun lit_129 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.603999972343444824218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_130 () (_ FloatingPoint 8 24) (fp.mul RNE lit_26 lit_129))
(assert (fp.isNormal lit_130))
(define-fun lit_131 () (_ FloatingPoint 8 24) (fp.add RNE lit_126 lit_130))
(assert (fp.isNormal lit_131))
(define-fun lit_134 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.246999993920326232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_135 () (_ FloatingPoint 8 24) (fp.mul RNE lit_30 lit_134))
(assert (fp.isNormal lit_135))
(define-fun lit_136 () (_ FloatingPoint 8 24) (fp.add RNE lit_131 lit_135))
(assert (fp.isNormal lit_136))
(define-fun lit_137 () Bool (fp.leq lit_113 lit_136))
(define-fun lit_139 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.504000008106231689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_142 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.352999985218048095703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_143 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_142))
(assert (fp.isNormal lit_143))
(define-fun lit_144 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_143))
(assert (fp.isNormal lit_144))
(define-fun lit_147 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.666000008583068847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_148 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_147))
(assert (fp.isNormal lit_148))
(define-fun lit_149 () (_ FloatingPoint 8 24) (fp.add RNE lit_144 lit_148))
(assert (fp.isNormal lit_149))
(define-fun lit_151 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.377000004053115844726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_152 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_151))
(assert (fp.isNormal lit_152))
(define-fun lit_153 () (_ FloatingPoint 8 24) (fp.add RNE lit_149 lit_152))
(assert (fp.isNormal lit_153))
(define-fun lit_155 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.456000000238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_156 () (_ FloatingPoint 8 24) (fp.mul RNE lit_26 lit_155))
(assert (fp.isNormal lit_156))
(define-fun lit_157 () (_ FloatingPoint 8 24) (fp.add RNE lit_153 lit_156))
(assert (fp.isNormal lit_157))
(define-fun lit_159 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.537999987602233886718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_160 () (_ FloatingPoint 8 24) (fp.mul RNE lit_30 lit_159))
(assert (fp.isNormal lit_160))
(define-fun lit_161 () (_ FloatingPoint 8 24) (fp.add RNE lit_157 lit_160))
(assert (fp.isNormal lit_161))
(define-fun lit_162 () Bool (fp.leq lit_139 lit_161))
(define-fun top_level_new0 () Bool (and lit_162 lit_86))
(define-fun top_level_new1 () Bool (and top_level_new0 lit_62))
(define-fun top_level_new2 () Bool (and top_level_new1 lit_25))
(define-fun top_level_new3 () Bool (and top_level_new2 lit_137))
(define-fun top_level_new4 () Bool (and top_level_new3 lit_33))
(define-fun top_level_new5 () Bool (and top_level_new4 lit_21))
(define-fun top_level_new6 () Bool (and top_level_new5 lit_17))
(define-fun top_level_new7 () Bool (and top_level_new6 lit_111))
(define-fun propexp () Bool (and top_level_new7 lit_29))
(assert propexp)
(check-sat)
;(get-model)
(exit)