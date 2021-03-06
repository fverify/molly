(define-fun epsilon () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.0632))
(define-fun const0 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isNormal y))
(define-fun const1 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 2.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun arithexp3 () (_ FloatingPoint 8 24) (fp.sub RNE y const1))
(assert (fp.isNormal arithexp3))
(define-fun arithexp5 () (_ FloatingPoint 8 24) (fp.add RNE y const1))
(assert (fp.isNormal arithexp5))
(define-fun arithexp4 () (_ FloatingPoint 8 24) (fp.mul RNE y arithexp5))
(assert (fp.isNormal arithexp4))
(define-fun arithexp1 () (_ FloatingPoint 8 24) (fp.mul RNE arithexp3 arithexp4))
(assert (fp.isNormal arithexp1))
(define-fun arithexp8 () (_ FloatingPoint 8 24) (fp.mul RNE y y))
(assert (fp.isNormal arithexp8))
(define-fun arithexp6 () (_ FloatingPoint 8 24) (fp.mul RNE arithexp8 y))
(assert (fp.isNormal arithexp6))
(define-fun const2 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 4.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun arithexp7 () (_ FloatingPoint 8 24) (fp.mul RNE const2 y))
(assert (fp.isNormal arithexp7))
(define-fun arithexp2 () (_ FloatingPoint 8 24) (fp.sub RNE arithexp6 arithexp7))
(assert (fp.isNormal arithexp2))
(define-fun arithexp () (_ FloatingPoint 8 24) (fp.sub RNE arithexp1 arithexp2))
(assert (fp.isNormal arithexp))
(define-fun prop () Bool (fp.gt arithexp epsilon))
(define-fun const3 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 100.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun prop1 () Bool (fp.geq y const3))
(define-fun const4 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 100.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun prop2 () Bool (fp.leq y const4))
(define-fun propexp1 () Bool (and prop1 prop2))
(define-fun propexp () Bool (and prop propexp1))
(assert propexp)
(check-sat)
;(get-model)
(exit)