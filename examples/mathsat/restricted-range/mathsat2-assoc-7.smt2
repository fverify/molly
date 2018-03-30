;; declare original Variables
(declare-fun a1 () (_ Float 8 23))
(declare-fun a2 () (_ Float 8 23))
(declare-fun a3 () (_ Float 8 23))
(declare-fun a4 () (_ Float 8 23))
(declare-fun a5 () (_ Float 8 23))
(declare-fun a6 () (_ Float 8 23))
(declare-fun a7 () (_ Float 8 23))
;; declare lower and upper value for range
(define-fun lower () (_ Float 8 23) ((_ fpnum 8 23) 1065353216))
(define-fun higher () (_ Float 8 23) ((_ fpnum 8 23) 1149239296))
;; range constraints for original variables
(define-fun r1 () Bool (and (fplt a1 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a1)))
(define-fun r2 () Bool (and (fplt a2 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a2)))
(define-fun r3 () Bool (and (fplt a3 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a3)))
(define-fun r4 () Bool (and (fplt a4 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a4)))
(define-fun r5 () Bool (and (fplt a5 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a5)))
(define-fun r6 () Bool (and (fplt a6 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a6)))
(define-fun r7 () Bool (and (fplt a7 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a7)))
;; assert range constraints for original variables
(assert (and r1 r2 r3 r4 r5 r6 r7))
;; define rhs: accumulation
(define-fun new () (_ Float 8 23) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a1 a2) a3) a4) a5) a6) a7))
;; define lhs: reduction
(define-fun new1 () (_ Float 8 23) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a1 a2) (fpadd fp_round_nearest_even a3 a4)) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a5 a6) a7)))
;; range constraints for lhs and rhs
(define-fun rnew () Bool (and (fplt new ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) new)))
(define-fun rnew1 () Bool (and (fplt new1 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) new1)))
;; assert range constraints for lhs and rhs
(assert (and rnew rnew1))
;; Define skeleton, assert it, check for sat
(define-fun skeleton () Bool (fpgt new1 new))
(assert skeleton)
(check-sat)
