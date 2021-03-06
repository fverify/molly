(define-fun epsilon () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 7.3728))
(define-fun const0 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(define-fun arithexp6 () (_ FloatingPoint 8 24) (fp.mul RNE x x))
(assert (fp.isNormal arithexp6))
(define-fun arithexp5 () (_ FloatingPoint 8 24) (fp.mul RNE x arithexp6))
(assert (fp.isNormal arithexp5))
(define-fun arithexp3 () (_ FloatingPoint 8 24) (fp.mul RNE x arithexp5))
(assert (fp.isNormal arithexp3))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isNormal y))
(define-fun arithexp8 () (_ FloatingPoint 8 24) (fp.mul RNE y y))
(assert (fp.isNormal arithexp8))
(define-fun arithexp7 () (_ FloatingPoint 8 24) (fp.mul RNE y arithexp8))
(assert (fp.isNormal arithexp7))
(define-fun arithexp4 () (_ FloatingPoint 8 24) (fp.mul RNE y arithexp7))
(assert (fp.isNormal arithexp4))
(define-fun arithexp1 () (_ FloatingPoint 8 24) (fp.sub RNE arithexp3 arithexp4))
(assert (fp.isNormal arithexp1))
(define-fun arithexp9 () (_ FloatingPoint 8 24) (fp.sub RNE x y))
(assert (fp.isNormal arithexp9))
(define-fun arithexp11 () (_ FloatingPoint 8 24) (fp.add RNE x y))
(assert (fp.isNormal arithexp11))
(define-fun arithexp13 () (_ FloatingPoint 8 24) (fp.mul RNE x x))
(assert (fp.isNormal arithexp13))
(define-fun arithexp14 () (_ FloatingPoint 8 24) (fp.mul RNE y y))
(assert (fp.isNormal arithexp14))
(define-fun arithexp12 () (_ FloatingPoint 8 24) (fp.add RNE arithexp13 arithexp14))
(assert (fp.isNormal arithexp12))
(define-fun arithexp10 () (_ FloatingPoint 8 24) (fp.mul RNE arithexp11 arithexp12))
(assert (fp.isNormal arithexp10))
(define-fun arithexp2 () (_ FloatingPoint 8 24) (fp.mul RNE arithexp9 arithexp10))
(assert (fp.isNormal arithexp2))
(define-fun arithexp () (_ FloatingPoint 8 24) (fp.sub RNE arithexp1 arithexp2))
(assert (fp.isNormal arithexp))
(define-fun prop () Bool (fp.gt arithexp epsilon))
(define-fun const1 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 100.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun prop1 () Bool (fp.geq x const1))
(define-fun const2 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 100.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun prop2 () Bool (fp.leq x const2))
(define-fun propexp2 () Bool (and prop1 prop2))
(define-fun prop3 () Bool (fp.geq y const1))
(define-fun prop4 () Bool (fp.leq y const2))
(define-fun propexp3 () Bool (and prop3 prop4))
(define-fun propexp1 () Bool (and propexp2 propexp3))
(define-fun propexp () Bool (and prop propexp1))
(assert propexp)
(check-sat)
;(get-model)
(exit)