(declare-fun y () (_ FloatingPoint 8 24))
(define-fun x () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RNE (fp #b0 #b011 #b000000)));involves casting from lower prec
(assert (fp.eq y x))
(check-sat)
