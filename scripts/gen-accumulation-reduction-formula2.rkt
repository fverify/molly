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
      (string-append "(+ "
                     (gen-acc-formul-general (- n 1) op)
                     " "
                     VAR-NAME-BASE
                     (number->string n)
                     ")")))


(define (gen-formula n delta)
;  (string-append "(> "
 ;                (gen-red-formul-general 0 (- n 1) "+")
  ;               " "
   ;              (gen-acc-formul-general n "+")
    ;             ")" ))
  (string-append "(> (- "
                 (gen-red-formul-general 0 (- n 1) "+")
                 " "
                 (gen-acc-formul-general n "+")
                 ") " 
                 delta
                 ")"))

(define (main)
  (let ((number-of-vars (vector-ref (current-command-line-arguments) 0))
        (delta (vector-ref (current-command-line-arguments) 1)))
    ;(gen-formula (string->number number-of-vars) delta)))
    (gen-formula (string->number number-of-vars) delta)))

(main)
