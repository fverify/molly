#lang racket
(require racket/flonum)
(require racket/base)
(require mzlib/string)

(define VAR-NAME-BASE "a")

(define (gen-red-formul low high op)
  (if (equal? low high)
      (string-append VAR-NAME-BASE (number->string (+ low 1)))
      (let* ((size (+ (- high low) 1))
             (mid (+ low (- (/ size 2) 1))))
        (string-append "("
                       op
                       " "
                       (gen-red-formul low mid op)
                       " "
                       (gen-red-formul (+ mid 1) high op)
                       ")"
                       ))))

(define (get-power-of-two num)
  (flexpt 2.0 (flfloor (fl* 1.4426950408889634 (fllog num)))))

(define (gen-red-formul-general low high op)
  (if (> low high) 
      ""
      (let* ((size (+ (- high low) 1))
             (power-of-two (get-power-of-two (->fl size))))
        (if (equal? (->fl size) power-of-two)
            (gen-red-formul low high op)
            (let* ((high-of-first (fl->exact-integer (+ low (- power-of-two 1))))
                   (low-of-second (+ high-of-first 1)))
              (string-append "("
                             op
                             " "
                             (gen-red-formul low high-of-first op)
                             " "
                             (gen-red-formul-general low-of-second high op)
                             ")"
                             ))))))

(define (gen-acc-formul-general n op)
  (if (equal? n 1)
      (string-append VAR-NAME-BASE "1")
      (string-append "(" op " "
                     (gen-acc-formul-general (- n 1) op)
                     " "
                     VAR-NAME-BASE
                     (number->string n)
                     ")")))


(define (gen-formula n)
  (string-append "(= "
                 (gen-acc-formul-general n "+")
                 " "
                 (gen-red-formul-general 0 (- n 1) "+")
                 ")"))

(define (generate-var-declarations n)
(if (equal? n 0)
  ""
  (string-append (generate-var-declarations (- n 1))
                 "(declare-fun a"
                 (number->string n)
                 " () (_ FloatingPoint 8 24))\n")))

(define (generate-range-constraints n)
(if (equal? n 0)
  ""
  (string-append (generate-range-constraints (- n 1))
                 "(define-fun r"
                 (number->string n)
                 " () Bool (and (fp.lt a"
                 (number->string n)
                 " higher) (fp.lt lower a"
                 (number->string n)
                 ")))\n")))

;(declare-fun a1 () (_ Float 8 23))
(define (generate-vars n)
  (if (equal? n 0)
  ""
  (string-append (generate-vars (- n 1))
                 " r" (number->string n))))

(define (top-level-generator n)
  (string-append ";; declare original Variables\n"
                 (generate-var-declarations n)
                 ";; declare lower and upper value for range\n"
                 "(define-fun lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1065353216 32)))\n"
                 "(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32)))\n"
                 "(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32)))\n"
                 "(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32)))\n"
                 "(define-fun delta () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1020054733 32)))\n"
                 ";; range constraints for original variables\n"
                 (generate-range-constraints n)
                 ";; assert range constraints for original variables\n"
                 "(assert (and"
                 (generate-vars n)
                 "))\n"
                 ";; define rhs: accumulation\n"
                 "(define-fun new () (_ FloatingPoint 8 24) "
                 (gen-acc-formul-general n "fp.add RNE")
                 ")\n"
                 ";; define lhs: reduction\n"
                 "(define-fun new1 () (_ FloatingPoint 8 24) "
                 (gen-red-formul-general 0 (- n 1) "fp.add RNE")
                 ")\n"
                 ";; range constraints for lhs and rhs\n"
                 "(define-fun rnew () Bool (or (and (fp.lt new higher) (fp.lt lower new)) (and (fp.lt new nlower) (fp.lt nhigher new))))\n"
                 "(define-fun rnew1 () Bool (or (and (fp.lt new1 higher) (fp.lt lower new1)) (and (fp.lt new1 nlower)(fp.lt nhigher new1))))\n"
                 ";; assert range constraints for lhs and rhs\n"
                 "(assert (and rnew rnew1))\n"
                 ";; Define skeleton, assert it, check for sat\n"
                 "(define-fun skeleton () Bool (fp.gt new1 new))\n"
                 ;;"(define-fun skeleton () Bool (fp.gt (fp.sub RNE new1 new) delta))\n"
                 "(assert skeleton)\n"
                 "(apply fpa2bv_approx)\n"
                 "(check-sat)\n"
                 ))

(define (main)
  (let ((number-of-vars (vector-ref (current-command-line-arguments) 0)))
    (display (top-level-generator (string->number number-of-vars)))))

(main)