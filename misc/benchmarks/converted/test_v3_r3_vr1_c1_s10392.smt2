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
(define-fun lit_31 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.171000003814697265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_33 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.879000008106231689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_34 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_33))
(assert (fp.isNormal lit_34))
(define-fun lit_35 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_34))
(assert (fp.isNormal lit_35))
(define-fun lit_38 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.537999987602233886718750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_39 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_38))
(assert (fp.isNormal lit_39))
(define-fun lit_40 () (_ FloatingPoint 8 24) (fp.add RNE lit_35 lit_39))
(assert (fp.isNormal lit_40))
(define-fun lit_43 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.767000019550323486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_44 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_43))
(assert (fp.isNormal lit_44))
(define-fun lit_45 () (_ FloatingPoint 8 24) (fp.add RNE lit_40 lit_44))
(assert (fp.isNormal lit_45))
(define-fun lit_46 () Bool (fp.leq lit_45 lit_31))
(define-fun lit_48 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.225999996066093444824218750000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_50 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.208000004291534423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_51 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_50))
(assert (fp.isNormal lit_51))
(define-fun lit_52 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_51))
(assert (fp.isNormal lit_52))
(define-fun lit_54 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.634999990463256835937500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_55 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_54))
(assert (fp.isNormal lit_55))
(define-fun lit_56 () (_ FloatingPoint 8 24) (fp.add RNE lit_52 lit_55))
(assert (fp.isNormal lit_56))
(define-fun lit_59 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.674000024795532226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_60 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_59))
(assert (fp.isNormal lit_60))
(define-fun lit_61 () (_ FloatingPoint 8 24) (fp.add RNE lit_56 lit_60))
(assert (fp.isNormal lit_61))
(define-fun lit_62 () Bool (fp.leq lit_48 lit_61))
(define-fun lit_64 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.929000020027160644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_66 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_67 () (_ FloatingPoint 8 24) (fp.mul RNE lit_14 lit_66))
(assert (fp.isNormal lit_67))
(define-fun lit_68 () (_ FloatingPoint 8 24) (fp.add RNE lit_12 lit_67))
(assert (fp.isNormal lit_68))
(define-fun lit_71 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 0.104000002145767211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun lit_72 () (_ FloatingPoint 8 24) (fp.mul RNE lit_18 lit_71))
(assert (fp.isNormal lit_72))
(define-fun lit_73 () (_ FloatingPoint 8 24) (fp.add RNE lit_68 lit_72))
(assert (fp.isNormal lit_73))
(define-fun lit_75 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.507000029087066650390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun lit_76 () (_ FloatingPoint 8 24) (fp.mul RNE lit_22 lit_75))
(assert (fp.isNormal lit_76))
(define-fun lit_77 () (_ FloatingPoint 8 24) (fp.add RNE lit_73 lit_76))
(assert (fp.isNormal lit_77))
(define-fun lit_78 () Bool (fp.leq lit_64 lit_77))
(define-fun top_level_new0 () Bool (and lit_46 lit_78))
(define-fun top_level_new1 () Bool (and top_level_new0 lit_62))
(define-fun top_level_new2 () Bool (and top_level_new1 lit_25))
(define-fun top_level_new3 () Bool (and top_level_new2 lit_21))
(define-fun propexp () Bool (and top_level_new3 lit_17))
(assert propexp)
(check-sat)
;(get-model)
(exit)