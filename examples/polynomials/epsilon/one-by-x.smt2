(define-fun epsilon () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 1.6384))
(define-fun const0 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun const1 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 1.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNormal x))
(define-fun arithexp3 () (_ FloatingPoint 8 24) (fp.sub RNE const1 x))
(assert (fp.isNormal arithexp3))
(define-fun arithexp1 () (_ FloatingPoint 8 24) (fp.div RNE const1 arithexp3))
(assert (fp.isNormal arithexp1))
(define-fun arithexp6 () (_ FloatingPoint 8 24) (fp.mul RNE x x))
(assert (fp.isNormal arithexp6))
(define-fun arithexp10 () (_ FloatingPoint 8 24) (fp.mul RNE x x))
(assert (fp.isNormal arithexp10))
(define-fun arithexp8 () (_ FloatingPoint 8 24) (fp.mul RNE x arithexp10))
(assert (fp.isNormal arithexp8))
(define-fun arithexp12 () (_ FloatingPoint 8 24) (fp.mul RNE x x))
(assert (fp.isNormal arithexp12))
(define-fun arithexp11 () (_ FloatingPoint 8 24) (fp.mul RNE x arithexp12))
(assert (fp.isNormal arithexp11))
(define-fun arithexp9 () (_ FloatingPoint 8 24) (fp.mul RNE x arithexp11))
(assert (fp.isNormal arithexp9))
(define-fun arithexp7 () (_ FloatingPoint 8 24) (fp.add RNE arithexp8 arithexp9))
(assert (fp.isNormal arithexp7))
(define-fun arithexp5 () (_ FloatingPoint 8 24) (fp.add RNE arithexp6 arithexp7))
(assert (fp.isNormal arithexp5))
(define-fun arithexp4 () (_ FloatingPoint 8 24) (fp.add RNE x arithexp5))
(assert (fp.isNormal arithexp4))
(define-fun arithexp2 () (_ FloatingPoint 8 24) (fp.add RNE const1 arithexp4))
(assert (fp.isNormal arithexp2))
(define-fun arithexp () (_ FloatingPoint 8 24) (fp.sub RNE arithexp1 arithexp2))
(assert (fp.isNormal arithexp))
(define-fun prop () Bool (fp.gt arithexp epsilon))
(define-fun const2 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN (- 1.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(define-fun prop1 () Bool (fp.gt x const2))
(define-fun prop2 () Bool (fp.lt x const1))
(define-fun propexp1 () Bool (and prop1 prop2))
(define-fun propexp () Bool (and prop propexp1))
(assert propexp)
(check-sat)
;(get-model)
(exit)