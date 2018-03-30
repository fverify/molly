;; declare original Variables
(declare-fun a1 () (_ Float 8 23))
(declare-fun a2 () (_ Float 8 23))
(declare-fun a3 () (_ Float 8 23))
(declare-fun a4 () (_ Float 8 23))
(declare-fun a5 () (_ Float 8 23))
(declare-fun a6 () (_ Float 8 23))
(declare-fun a7 () (_ Float 8 23))
(declare-fun a8 () (_ Float 8 23))
(declare-fun a9 () (_ Float 8 23))
(declare-fun a10 () (_ Float 8 23))
(declare-fun a11 () (_ Float 8 23))
(declare-fun a12 () (_ Float 8 23))
(declare-fun a13 () (_ Float 8 23))
(declare-fun a14 () (_ Float 8 23))
(declare-fun a15 () (_ Float 8 23))
(declare-fun a16 () (_ Float 8 23))
(declare-fun a17 () (_ Float 8 23))
(declare-fun a18 () (_ Float 8 23))
(declare-fun a19 () (_ Float 8 23))
(declare-fun a20 () (_ Float 8 23))
(declare-fun a21 () (_ Float 8 23))
(declare-fun a22 () (_ Float 8 23))
(declare-fun a23 () (_ Float 8 23))
(declare-fun a24 () (_ Float 8 23))
;; declare lower and upper value for range
(define-fun lower () (_ Float 8 23) ((_ fpnum 8 23) 8388608))
(define-fun higher () (_ Float 8 23) ((_ fpnum 8 23) 1149239296))
;; range constraints for original variables
(define-fun r1 () Bool (and (fplt a1 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a1)))
(define-fun r2 () Bool (and (fplt a2 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a2)))
(define-fun r3 () Bool (and (fplt a3 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a3)))
(define-fun r4 () Bool (and (fplt a4 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a4)))
(define-fun r5 () Bool (and (fplt a5 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a5)))
(define-fun r6 () Bool (and (fplt a6 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a6)))
(define-fun r7 () Bool (and (fplt a7 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a7)))
(define-fun r8 () Bool (and (fplt a8 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a8)))
(define-fun r9 () Bool (and (fplt a9 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a9)))
(define-fun r10 () Bool (and (fplt a10 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a10)))
(define-fun r11 () Bool (and (fplt a11 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a11)))
(define-fun r12 () Bool (and (fplt a12 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a12)))
(define-fun r13 () Bool (and (fplt a13 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a13)))
(define-fun r14 () Bool (and (fplt a14 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a14)))
(define-fun r15 () Bool (and (fplt a15 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a15)))
(define-fun r16 () Bool (and (fplt a16 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a16)))
(define-fun r17 () Bool (and (fplt a17 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a17)))
(define-fun r18 () Bool (and (fplt a18 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a18)))
(define-fun r19 () Bool (and (fplt a19 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a19)))
(define-fun r20 () Bool (and (fplt a20 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a20)))
(define-fun r21 () Bool (and (fplt a21 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a21)))
(define-fun r22 () Bool (and (fplt a22 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a22)))
(define-fun r23 () Bool (and (fplt a23 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a23)))
(define-fun r24 () Bool (and (fplt a24 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) a24)))
;; assert range constraints for original variables
(assert (and r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24))
;; define rhs: accumulation
(define-fun new () (_ Float 8 23) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a1 a2) a3) a4) a5) a6) a7) a8) a9) a10) a11) a12) a13) a14) a15) a16) a17) a18) a19) a20) a21) a22) a23) a24))
;; define lhs: reduction
(define-fun new1 () (_ Float 8 23) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a1 a2) (fpadd fp_round_nearest_even a3 a4)) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a5 a6) (fpadd fp_round_nearest_even a7 a8))) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a9 a10) (fpadd fp_round_nearest_even a11 a12)) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a13 a14) (fpadd fp_round_nearest_even a15 a16)))) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a17 a18) (fpadd fp_round_nearest_even a19 a20)) (fpadd fp_round_nearest_even (fpadd fp_round_nearest_even a21 a22) (fpadd fp_round_nearest_even a23 a24)))))
;; range constraints for lhs and rhs
(define-fun rnew () Bool (and (fplt new ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) new)))
(define-fun rnew1 () Bool (and (fplt new1 ((_ fpnum 8 23) higher)) (fplt ((_ fpnum 8 23) lower) new1)))
;; assert range constraints for lhs and rhs
(assert (and rnew rnew1))
;; Define skeleton, assert it, check for sat
(define-fun skeleton () Bool (fpgt new1 new))
(assert skeleton)
(check-sat)
