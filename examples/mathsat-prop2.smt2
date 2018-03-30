;; Example FP SMT-LIB for (and (: p1 (= (+ (+ a b) c) 3.5)) (: p2 (= (- (* 3.5 b) c) a)))
;; declare FP format constants
;(define-fun plower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); small positive ~ + 2^-126
;(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); small negative nlowest ~ NEG 2^-126
;(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); large negative  NEG 1024.0
;(define-fun phigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); large positive  + 1024.0

;;declare variables from formula
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () (_ FloatingPoint 8 24))

;; standard range constraints on variables
;(define-fun a-r () Bool (or (and (fp.lt a phigher) (fp.lt plower a)) (and (fp.lt a nlower) (fp.lt nhigher a))))
;(assert a-r)
;(define-fun b-r () Bool (or (and (fp.lt b phigher) (fp.lt plower b)) (and (fp.lt b nlower) (fp.lt nhigher b))))
;(assert b-r)
;(define-fun c-r () Bool (or (and (fp.lt c phigher) (fp.lt plower c)) (and (fp.lt c nlower) (fp.lt nhigher c))))
;(assert c-r)

;; declare constants from formula
(define-fun const-3.5 () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTZ 3.5))

(define-fun exp2 () (_ FloatingPoint 8 24) (fp.add RNE a b))
(define-fun exp3 () (_ FloatingPoint 8 24) (fp.add RNE exp2 c))
(define-fun p1 () Bool (fp.eq exp3 const-3.5))

(define-fun exp4 () (_ FloatingPoint 8 24) (fp.mul RNE const-3.5 b))
(define-fun exp () (_ FloatingPoint 8 24) (fp.sub RNE exp4 c))
(define-fun p2 () Bool (fp.eq exp a))

(define-fun skeleton () Bool (and p1 p2))
(assert skeleton)
(check-sat)
