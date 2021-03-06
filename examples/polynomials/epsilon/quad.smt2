(define-fun epsilon () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.0004))
(define-fun const0 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(declare-fun c () (_ FloatingPoint 8 24))
(assert (fp.isNormal c))
(declare-fun a () (_ FloatingPoint 8 24))
(assert (fp.isNormal a))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(define-fun arithexp4 () (_ FloatingPoint 8 24) (fp.mul RNE x x))
(assert (fp.isNormal arithexp4))
(define-fun arithexp2 () (_ FloatingPoint 8 24) (fp.mul RNE a arithexp4))
(assert (fp.isNormal arithexp2))
(declare-fun b () (_ FloatingPoint 8 24))
(assert (fp.isNormal b))
(define-fun arithexp3 () (_ FloatingPoint 8 24) (fp.mul RNE b x))
(assert (fp.isNormal arithexp3))
(define-fun arithexp1 () (_ FloatingPoint 8 24) (fp.add RNE arithexp2 arithexp3))
(assert (fp.isNormal arithexp1))
(define-fun arithexp () (_ FloatingPoint 8 24) (fp.add RNE arithexp1 c))
(assert (fp.isNormal arithexp))
(define-fun prop () Bool (fp.gt arithexp epsilon))
(declare-fun d () (_ FloatingPoint 8 24))
(assert (fp.isNormal d))
(define-fun arithexp5 () (_ FloatingPoint 8 24) (fp.mul RNE d d))
(assert (fp.isNormal arithexp5))
(define-fun arithexp7 () (_ FloatingPoint 8 24) (fp.mul RNE b b))
(assert (fp.isNormal arithexp7))
(define-fun const1 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 4.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun arithexp9 () (_ FloatingPoint 8 24) (fp.mul RNE a c))
(assert (fp.isNormal arithexp9))
(define-fun arithexp8 () (_ FloatingPoint 8 24) (fp.mul RNE const1 arithexp9))
(assert (fp.isNormal arithexp8))
(define-fun arithexp6 () (_ FloatingPoint 8 24) (fp.sub RNE arithexp7 arithexp8))
(assert (fp.isNormal arithexp6))
(define-fun prop1 () Bool (fp.eq arithexp5 arithexp6))
(define-fun const2 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 1.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun arithexp13 () (_ FloatingPoint 8 24) (fp.mul RNE const2 b))
(assert (fp.isNormal arithexp13))
(define-fun arithexp11 () (_ FloatingPoint 8 24) (fp.add RNE arithexp13 d))
(assert (fp.isNormal arithexp11))
(define-fun const3 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 2.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun arithexp12 () (_ FloatingPoint 8 24) (fp.mul RNE const3 a))
(assert (fp.isNormal arithexp12))
(define-fun arithexp10 () (_ FloatingPoint 8 24) (fp.div RNE arithexp11 arithexp12))
(assert (fp.isNormal arithexp10))
(define-fun prop2 () Bool (fp.eq x arithexp10))
(define-fun propexp3 () Bool (and prop1 prop2))
(define-fun propexp1 () Bool (and prop propexp3))
(define-fun const4 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 100.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun prop3 () Bool (fp.geq b const4))
(define-fun const5 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 100.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun prop4 () Bool (fp.leq b const5))
(define-fun propexp6 () Bool (and prop3 prop4))
(define-fun prop5 () Bool (fp.geq a const4))
(define-fun prop6 () Bool (fp.leq a const5))
(define-fun propexp7 () Bool (and prop5 prop6))
(define-fun propexp4 () Bool (and propexp6 propexp7))
(define-fun prop7 () Bool (fp.geq c const4))
(define-fun prop8 () Bool (fp.leq c const5))
(define-fun propexp5 () Bool (and prop7 prop8))
(define-fun propexp2 () Bool (and propexp4 propexp5))
(define-fun propexp () Bool (and propexp1 propexp2))
(assert propexp)
(check-sat)
;(get-model)
(exit)