(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun x () (_ FloatingPoint 8 24))
(define-fun arithexp () (_ FloatingPoint 8 24) (fp.mul RNE x y))
(define-fun prop () Bool (fp.eq arithexp y))
(define-fun const0 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 100.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))
(define-fun prop1 () Bool (fp.gt x const0))
(define-fun prop2 () Bool (fp.gt y const0))
(define-fun propexp1 () Bool (and prop1 prop2))
(define-fun propexp () Bool (and prop propexp1))
(assert propexp)
(check-sat)
;(get-model)
(exit)
