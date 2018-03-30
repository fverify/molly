
#lang racket
;(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32)))))
;(define-fun skeleton () Bool (fp.gt (fp.add RNE  ((_ to_fp 8 24) RTZ  0.000000000000000000000000000000000000082284598952366268258543273910638864287642063852998358999549532411216072602666571356166969053447246551513671875000000000000000000) (fp.add RNE  ((_ to_fp 8 24) RTZ  0.000000000000000000000000000000000000011754949113416732378955649067140789937851180688768642721150604091057308153711602471958030946552753448486328125000000000000000000) (fp.add RNE  ((_ to_fp 8 24) RTZ  0.000000000000000000000000000000000000094039548065783000637498922977779654225493244541767001720700136502273380756378173828125000000000000000000000000000000000000000000) delta))) (fp.add RNE  ((_ to_fp 8 24) RTZ  0.000000000000000000000000000000000000094039548065783000637498922977779654225493244541767001720700136502273380756378173828125000000000000000000000000000000000000000000) (fp.add RNE  ((_ to_fp 8 24) RTZ  0.000000000000000000000000000000000000094039548065783000637498922977779654225493244541767001720700136502273380756378173828125000000000000000000000000000000000000000000) delta))))
;(assert skeleton)
;(check-sat)
;copy-paste for general e,m

;; required imports
(require redex/reduction-semantics)
(require mzlib/string)
(require math/flonum)
(require math/bigfloat)
(require racket/string)

(define trim-str "0")
(define SCRIPT-PRECISION 3000); seems to be safe for ``float''
(bf-precision SCRIPT-PRECISION); for the big-float library

;; defining parameters as constants for now
(define ROUND-TO-POSITIVE "round-to-positive")
(define ROUND-TO-NEGATIVE "round-to-negative")
(define ROUND-TO-ZERO "round-to-zero")
(define ROUND-TO-NEAREST-AWAY "round-to-nearest-away")
(define ROUND-TO-NEAREST-EVEN "round-to-nearest-even")
(define ROUND-TO-NEAREST-NEGATIVE "round-to-nearest-negative")
(define ROUND-TO-NEAREST-SIMPLE "round-to-nearest-simple")
(define define-fun-preamble "\n(define-fun range-split2 ((abs-var Real) (multiplier-var Real)) Bool\n\t(and\n")
(define NAMED-PROP-CONSTRAINTS "\n")

;; -----------------------------------------------------------------------------
(define SMT2-ROUNDING-FUNCTION-DEFINITIONS ";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Defining Rounding functions for the 5 IEEE-754 2008 compliant rounding modes
(define-fun rnd-to-negative ((x Real) (xr Real)) Bool
	(= xr (to_real (to_int x))))
      
(define-fun rnd-to-positive ((x Real) (xr Real)) Bool
	(and (=> (= x (to_real (to_int x))) (= xr x))
		   (=> (> x (to_real (to_int x))) (= xr (+ (to_real (to_int x)) 1.0)))))
		   
(define-fun rnd-to-zero ((x Real) (xr Real)) Bool
  (and (=> (>= x 0.0) (rnd-to-negative x xr))
  		 (=> (< x 0.0)  (rnd-to-positive x xr))))

(define-fun rnd-to-nearest-even ((x Real) (xr Real)) Bool
  (and      
    (=> (and (= 0.5 (- x (to_real (to_int x)))) (= 0 (rem (to_int x) 2))) (= xr (to_real (to_int x)))) 
    (=> (and (= 0.5 (- x (to_real (to_int x)))) (not (= 0 (rem (to_int x) 2)))) (= xr (+ (to_real (to_int x)) 1.0)))
    (=> (and (< (- x (to_real (to_int x))) 0.5)) (= xr (to_real (to_int x))))
    (=> (and (< 0.5 (- x (to_real (to_int x))))) (= xr (+ (to_real (to_int x)) 1.0)))))

(define-fun rnd-to-nearest-away ((x Real) (xr Real)) Bool
  (and     
    (=> (and (= 0.5 (- x (to_real (to_int x)))) (< 0.0 x)) (= xr (to_real (to_int (+ x 0.5))))) 
    (=> (and (= 0.5 (- x (to_real (to_int x)))) (< x 0.0)) (= xr (to_real (to_int (- x 0.5)))))
    (=> (< 0.5 (- x (to_real (to_int x)))) (= xr (+ (to_real (to_int x)) 1.0)))
    (=> (< (- x (to_real (to_int x))) 0.5) (= xr (to_real (to_int x))))))

;; Non-IEEE rounding modes for experimentation
(define-fun rnd-to-nearest-negative ((x Real) (xr Real)) Bool
  (and      
    (=> (< 0.5 (- x (to_real (to_int x)))) (= xr (+ (to_real (to_int x)) 1.0))) 
    (=> (<= (- x (to_real (to_int x))) 0.5) (= xr (to_real (to_int x))))))

;; below is away from zero for positive x, towards zero for negative x
(define-fun rnd-to-nearest-simple ((x Real) (xr Real)) Bool
	(= xr (to_real (to_int (+ x 0.5)))))

;; below is away from zero for negative x, towards zero for positive x
(define-fun rnd-to-nearest-simple2 ((x Real) (xr Real)) Bool
	(= xr (to_real (to_int (- x 0.5)))))
;;End of non-IEEE rounding modes

(define-fun fit ((x Real) (xr Real)) Bool
        (= xr (to_real (to_int x))))\n")

(define RND-HEADER "(define-fun rnd ((x Real) (xr Real)) Bool\n\t")

(define digits-per-bit (/ (log 2) (log 10)))

(define (bigfloat->decimal-string x)
  (define m (bigfloat->real (bflog10 (bfabs x))))
  (define n (* digits-per-bit (bigfloat-precision x)))
  (real->decimal-string (bigfloat->real x)
                        (max 1 (exact-ceiling (- n m)))))

(define (remove-trailing-zeroes str)
  (let ((result (string-trim str trim-str #:left? false)))
        (if (equal? result str)
            str
            (remove-trailing-zeroes result))))

;; takes in a rounding-mode returns the name of the rounding-function
(define (get-rounding-function-name mode)
  (cond 
    [(equal? ROUND-TO-NEGATIVE mode) "rnd-to-negative"]
    [(equal? ROUND-TO-POSITIVE mode) "rnd-to-positive"]
    [(equal? ROUND-TO-ZERO mode) "rnd-to-zero"]
    [(equal? ROUND-TO-NEAREST-AWAY mode) "rnd-to-nearest-away"]
    [(equal? ROUND-TO-NEAREST-EVEN mode) "rnd-to-nearest-even"]
    [(equal? ROUND-TO-NEAREST-NEGATIVE mode) "rnd-to-nearest-negative"]
    [(equal? ROUND-TO-NEAREST-SIMPLE mode) "rnd-to-nearest-simple"]))

;; gets the largest power of 2.0 <= the positive flonum num
;(define (get-power-of-two-lower num)
; (flexp2 (flfloor (fllog2 num))))

(define (get-power-of-two-lower num)
  (bfexp2 (bffloor (bflog2 num))))


;; gets the largest power of 2.0 >= the positive flonum num
;(define (get-power-of-two-higher num)
; (flexp2 (flceiling (fllog2 num))))
(define (get-power-of-two-higher num)
  (bfexp2 (bfceiling (bflog2 num))))

(define (real-arithmetic-operator? op)
  (or (equal? '+R op) (equal? '-R op) (equal? '*R op) (equal? '/R op)))

;; checks if the input is an arithmetic operator
(define (arithmetic-operator? op)
  (or (equal? '+ op) (equal? '- op) (equal? '* op) (equal? '/ op) (equal? '+R op) (equal? '-R op) (equal? '*R op) (equal? '/R op)))

(define (arithmetic-exp? exp)
 (and (list? exp) (arithmetic-operator? (first exp))))

;; checks if the input is a (binary) relational operator
(define (relational-operator? op)
  (or (equal? '= op) (equal? '< op) (equal? '<= op) (equal? '> op) (equal? '>= op)))

;; checks if the expression is of the form (<relational-operator> <exp> <exp>)
;; the two expressions that the operator relates are FP expressions
(define (relational-exp? exp)
  (and (list? exp) (relational-operator? (first exp))))

;; checks if an expression is of the form (not <exp>)
(define (not-exp? exp)
  (and (list? exp) (equal? 'not (first exp))))

;; checks if the input is a binary boolean operator
(define (binary-boolean-operator? op)
  (or (equal? 'and op) (equal? 'or op) (equal? 'xor op) (equal? '=> op)))

;; checks if the expression is of the form (<binary-boolean-operator> <exp> <exp>)
;; the two expressions that constitute exp (along with the operator) are either
;; relational or boolean expressions(binary or not?)
(define (binary-boolean-exp? exp)
  (and (list? exp) (binary-boolean-operator? (first exp))))

(define (get-op op)
  (cond
    [(equal? op '+R) '+]
    [(equal? op '-R) '-]
    [(equal? op '*R) '*]
    [(equal? op '/R) '/]))

;; z3-exp-gen : 
;; Consumes a binary operator, a result variable, left operand (a variable name), a right operand
;; (a variable name), a list of variables (that have already been used),
;; the rounding mode, the precision (a positive natural number) and returns a list, first element of which is 
;; a string containing the z3 code corresponding to the intended FP operation
;; assigned to the result variable and the second of which is the updated list of variables that are known as having/eventually being used.
(define (z3-exp-gen op result-var var-left var-right var-list rnd-mode precision lower higher)
  (cond
    [(arithmetic-operator? op);;delete check for rounding mode from here 
     (let* ((lower-power (get-power-of-two-lower lower))
            (higher-power (get-power-of-two-higher higher))
            (result-var-str (symbol->string result-var))
            (result-var-str-real (string-append result-var-str "-real"))
            (result-var-str-two-to-exp (string-append "two-to-exp-" result-var-str))
            (rnd-fn-name (get-rounding-function-name rnd-mode))
            (real-op? (real-arithmetic-operator? op))
            (decl-exp (if real-op? 
                          (string-append "\n(declare-const " result-var-str " Real)\n")
                          (string-append "\n(declare-const " result-var-str " Real)\n"
                                         "\n(declare-const abs-" result-var-str-real " Real)\n"; added for -ve
                                         
                                         "(declare-const " result-var-str-real " Real)\n"
                                         "(assert (and (<= " (remove-trailing-zeroes (bigfloat->decimal-string lower))  "  " result-var-str-real") (< "
                                         result-var-str-real " " (remove-trailing-zeroes (bigfloat->decimal-string higher)) ")))\n"
                                         "(assert (and (<= " (remove-trailing-zeroes (bigfloat->decimal-string lower))  "  " result-var-str") (< "
                                         result-var-str " " (remove-trailing-zeroes (bigfloat->decimal-string higher)) ")))\n"
                                         
                                         "(assert (=> (>= " result-var-str-real " 0.0) (= abs-" result-var-str-real " " result-var-str-real")))\n"
                                         "(assert (=> (< " result-var-str-real " 0.0) (= abs-" result-var-str-real " (- " result-var-str-real "))))\n"
                                         ;; next constraint added Jan 27 2014
                                         "(assert (and (<= " (remove-trailing-zeroes (bigfloat->decimal-string lower))  "  abs-" result-var-str-real") (< abs-"
                                         result-var-str-real " " (remove-trailing-zeroes (bigfloat->decimal-string higher)) ")))\n"
                                         "(declare-const " result-var-str-two-to-exp " Real)\n"
                                         "(declare-const two-to-exp-p-minus-e-" result-var-str " Real)\n"
                                         "(assert (range-split2 abs-" result-var-str "-real two-to-exp-p-minus-e-" result-var-str "))\n"
                                         )))       
            (sum-exp (if real-op?
                         (string-append "\n(assert (= " result-var-str " (" (symbol->string (get-op op)) " " (symbol->string var-left) " " 
                                        (symbol->string var-right) ")))\n")
                         (string-append  
                          "\n(assert (rnd (* "result-var-str "-real two-to-exp-p-minus-e-" result-var-str ") (* two-to-exp-p-minus-e-" result-var-str " " result-var-str ")))\n"
                          "\n(assert (= " result-var-str-real " (" (symbol->string op) " " (symbol->string var-left) " " 
                          (symbol->string var-right) ")))\n"
                          ))))
       (list (string-append decl-exp sum-exp) (list result-var
                                                    (string->symbol result-var-str-two-to-exp)
                                                    (string->symbol result-var-str-real))))] 
    [(relational-operator? op)
     (list (string-append "\n(" (symbol->string op) " " 
                          (symbol->string var-left) " " (symbol->string var-right) ")")
           (list result-var))]
    ))



;; returns all variables present in exp as a list
;; 
(define (get-all-variables-in exp)
  (cond
    [(eof-object? exp) '()]
    [(empty? exp) '()]
    [(number? exp)
     (list (cons (string->symbol (string-append "const-" (remove-trailing-zeroes (bigfloat->decimal-string (bf exp))) "-rounded")) (bf exp)))]
    [(not (list? exp)) 
     (list exp)]
    [(not-exp? exp)
     (get-all-variables-in (second exp))]
    [else (append (get-all-variables-in (second exp)) (get-all-variables-in (third exp)))]))

;;
;;
(define (generate-z3-constraints-for-exp result-var exp var-list rnd-mode precision lower higher var-list-file-name top-level? mixed-mode?)
  (cond
    [(not (list? exp)) (list "" var-list)];;ATOMICEXPR
    [(and (not (list? (second exp))) (not (list? (third exp))));;floating point expr FPEXPR
     (z3-exp-gen (first exp)  result-var (second exp) (third exp) var-list rnd-mode precision lower higher)]
    [(and (not (list? (second exp))) (list? (third exp)))
     (let* ((new-right-var (variable-not-in var-list (term new))); should actually include result-var,...
            (right-result (generate-z3-constraints-for-exp new-right-var (third exp) (cons new-right-var var-list) rnd-mode precision lower higher var-list-file-name false mixed-mode?))
            (exp-result 
             (z3-exp-gen (first exp) result-var (second exp) new-right-var 
                         (append (second right-result) (list new-right-var) var-list) rnd-mode precision lower higher))
            (temp (if top-level?
                      (with-output-to-file var-list-file-name (lambda () (display (symbol->string new-right-var)))#:exists 'append)
                      "none"))) 
       (list (string-append (first right-result) (first exp-result))
             (append (list new-right-var) (second right-result) (second exp-result))))]
    [(and (list? (second exp)) (not (list? (third exp))))
     (let* ((new-left-var (variable-not-in var-list (term new))); should actually include result-var,...
            (left-result (generate-z3-constraints-for-exp new-left-var (second exp) (cons new-left-var var-list) rnd-mode precision lower higher var-list-file-name false mixed-mode?))
            (exp-result 
             (z3-exp-gen (first exp) result-var new-left-var (third exp)  
                         (append (second left-result) (list new-left-var) var-list) rnd-mode precision lower higher))
            (temp (if top-level?
                      (with-output-to-file var-list-file-name (lambda () (display (symbol->string new-left-var)))#:exists 'append)
                      "none"))
            )
       
       (list (string-append (first left-result) (first exp-result))
             (append (list new-left-var) (second left-result) (second exp-result))))]
    [(and (list? (second exp)) (list? (third exp)))
     (let* ((new-vars (variables-not-in var-list (term (new new))))
            (new-left-var (first new-vars))
            (new-right-var (second new-vars))
            (temp (if top-level?
                      (with-output-to-file var-list-file-name (lambda () (display (convert-to-string new-vars)))#:exists 'append)
                      "none"))
            (left-result (generate-z3-constraints-for-exp new-left-var (second exp) (append var-list new-vars) rnd-mode precision lower higher var-list-file-name false mixed-mode?))
            (right-result (generate-z3-constraints-for-exp new-right-var (third exp) (append var-list new-vars (second left-result)) rnd-mode precision lower higher var-list-file-name false mixed-mode?))
            (exp-result 
             (z3-exp-gen (first exp) result-var new-left-var new-right-var
                         (append (second left-result) (second right-result) var-list new-vars) rnd-mode precision lower higher)))
       (list (string-append (first left-result) (first right-result) (first exp-result))
             (append (second left-result) (second right-result) (second exp-result) new-vars)))
     ]
    ))


;;
;;
(define (generate-initial-z3-code-precision precision)
  (string-append "(declare-const two-to-p Real)\n" "(assert (= two-to-p " (remove-trailing-zeroes (bigfloat->decimal-string (bfexp2 (bf precision)))) "))\n"))

;;
;;
(define  (generate-if-then-else-statements var-str lower higher acc)
  (if (> lower higher)
      acc
      (string-append "(ite (and (>= " var-str " " (number->string lower)
                     ") (< " var-str " " (number->string (* 2 lower)) ")) " (number->string lower)
                     "\n"
                     (generate-if-then-else-statements var-str (* 2 lower) higher (string-append acc ")"))
                     )))
;;added on Feb 18
(define  (generate-constraints-for-range-split var-str  lower higher lower-two-to-exp-p-minus-e-var)
  (if (bf>= lower higher)
      ""
      (string-append "\t\t(=> (and (<= " (remove-trailing-zeroes (bigfloat->decimal-string lower)) " " (string-trim (string-append "abs-" var-str) "-real")  
                     ") (< "  (string-trim (string-append "abs-" var-str) "-real")  " " (remove-trailing-zeroes (bigfloat->decimal-string (bf* (bf 2) lower))) "))  "
                     "(= multiplier-"
                     (string-trim var-str "-real") " " (remove-trailing-zeroes (bigfloat->decimal-string lower-two-to-exp-p-minus-e-var)) "))"
                     "\n"
                     (generate-constraints-for-range-split var-str  (bf* (bf 2) lower) higher 
                                                           (bf/ lower-two-to-exp-p-minus-e-var (bf 2.0))))))

;;
(define  (generate-flat-constraints var-str output-var-str lower higher acc lower-two-to-exp-p-minus-e-var input-var?)
  (if (>= lower higher)
      ""
      (if input-var?
          (string-append "(assert (=> (and (<= " (number->string lower) " " (string-trim (string-append "abs-" var-str) "-real")  
                         ") (< "  (string-trim (string-append "abs-" var-str) "-real")  " " (number->string (* 2 lower)) ")) (and (= "
                         output-var-str " "  (number->string lower) ") (= two-to-exp-p-minus-e-"
                         (string-trim var-str "-real") " " (number->string lower-two-to-exp-p-minus-e-var) "))))"
                         "\n"
                         (generate-flat-constraints var-str output-var-str (* 2 lower) higher (string-append acc ")") 
                                                    (/ lower-two-to-exp-p-minus-e-var 2.0) true))
          (string-append "(assert (=> (and (<= " (number->string lower) " " (string-append "abs-" var-str) 
                         ") (< "  (string-append "abs-" var-str)  " " (number->string (* 2 lower)) ")) (and (= "
                         output-var-str " "  (number->string lower) ") (= two-to-exp-p-minus-e-"
                         (string-trim var-str "-real") " " (number->string lower-two-to-exp-p-minus-e-var) "))))"
                         "\n"
                         (generate-flat-constraints var-str output-var-str (* 2 lower) higher (string-append acc ")") 
                                                    (/ lower-two-to-exp-p-minus-e-var 2.0) false)
                         ))))

;;
;;
(define (generate-constraint-for-exponent var lower higher precision rnd-mode)
  (if (symbol? var)
      (let* ((var-name (symbol->string var))
             (two-to-exp-var-name (string-append "two-to-exp-" var-name))
             (lower-exponent (+ (bigfloat-exponent (bf 0.001)) (- SCRIPT-PRECISION 1)))
             (lower-power (get-power-of-two-lower lower))
             (higher-power (get-power-of-two-higher higher))
             (rnd-fn-name (get-rounding-function-name rnd-mode)))
        (string-append
         "(assert (range-split2 abs-" var-name " two-to-exp-p-minus-e-" var-name "))\n"
         "\n(declare-const temp-" var-name " Real)"
         "\n(assert (= temp-" var-name " (* " var-name " two-to-exp-p-minus-e-" var-name ")))"
         ;"\n(assert (= temp-" var-name " (" "rnd" " temp-" var-name ")))\n"
         "\n(assert (fit temp-" var-name " temp-" var-name "))\n"
         ))
      ;; following portion added much later
      (let* ((var-name (symbol->string (car var)))
             (two-to-exp-var-name (string-append "two-to-exp-" var-name))
             (lower-power (get-power-of-two-lower lower))
             (higher-power (get-power-of-two-higher higher))
             (rnd-fn-name (get-rounding-function-name rnd-mode)))
        (string-append
         "(assert (range-split2 abs-" var-name " two-to-exp-p-minus-e-" var-name "))\n"
         "(assert (rnd" " (* " (remove-trailing-zeroes (bigfloat->decimal-string (cdr var))) " two-to-exp-p-minus-e-" var-name ") (* two-to-exp-p-minus-e-" var-name " " var-name ")
))\n"
         ))
      ))

;;
;;
(define (generate-constraint-for-bounds var-name lower higher mixed-mode?)
  ;; Commented on Jan 27th 2014 to ignore -ve and added next for only for +ve
  (string-append 
   "(assert (and (<= " (remove-trailing-zeroes(bigfloat->decimal-string lower))  "  " (symbol->string var-name)") (< "
   (symbol->string var-name) " " (remove-trailing-zeroes (bigfloat->decimal-string higher)) ")" 
   ")" ")\n"
   ;;The following line added on Jan 27 2014 for enforcing overall range on absolute value variable
   (if mixed-mode?
       ""
       (string-append "(assert (and (<= " (remove-trailing-zeroes (bigfloat->decimal-string lower))  " abs-" (symbol->string var-name)") (< abs-"
                      (symbol->string var-name) " " (remove-trailing-zeroes (bigfloat->decimal-string higher)) ")" 
                      "))\n"))
   "\n"));changed for -ve abs

;;
(define (get-var-symbol el)
  (if (symbol? el)
      el
      (car el)))

;;
(define (generate-initial-z3-code-var-list var-list lower higher precision rnd-mode mixed-mode?)
  (if (empty? var-list) ""
      (if mixed-mode?
          (string-append "(declare-const " (symbol->string (get-var-symbol (first var-list))) " Real)\n"
                         (if (not(symbol? (first var-list)))
                             (string-append "(assert (= " (symbol->string (get-var-symbol (first var-list))) " " (remove-trailing-zeroes (bigfloat->decimal-string (cdr (first var-list)))) "))\n")
                             (generate-constraint-for-bounds (get-var-symbol (first var-list)) lower higher mixed-mode?))
                         (generate-initial-z3-code-var-list (rest var-list) lower 
                                                            higher precision rnd-mode mixed-mode?))
          (string-append "(declare-const " (symbol->string (get-var-symbol (first var-list))) " Real)\n"
                         "(declare-const abs-" (symbol->string (get-var-symbol (first var-list))) " Real)\n";added for -ve
                         "(declare-const two-to-exp-" (symbol->string (get-var-symbol (first var-list))) " Real)\n"
                         "(declare-const two-to-exp-p-minus-e-" (symbol->string (get-var-symbol (first var-list))) " Real)\n"
                         "(assert (=> (>= " (symbol->string (get-var-symbol (first var-list))) " 0.0) (= abs-" (symbol->string (get-var-symbol (first var-list))) " " (symbol->string (get-var-symbol (first var-list)))")));added\n"
                         "(assert (=> (< " (symbol->string (get-var-symbol (first var-list))) " 0.0) (= abs-" (symbol->string (get-var-symbol (first var-list))) " (- " (symbol->string (get-var-symbol (first var-list))) "))));added\n"
                         (generate-constraint-for-bounds (get-var-symbol (first var-list)) lower higher mixed-mode?)
                         (generate-constraint-for-exponent (first var-list) lower higher precision rnd-mode);changed to constant exponent
                         (generate-initial-z3-code-var-list (rest var-list) lower 
                                                            higher precision rnd-mode mixed-mode?)))))
;;
(define (generate-initial-z3-code var-list precision lower higher rnd-mode mixed-mode?)
  (string-append ";;Initial declarations\n" (generate-initial-z3-code-precision precision) "\n"
                 (generate-initial-z3-code-var-list var-list lower higher (get-val-two-to-exp-p-minus-e-var precision (get-power-of-two-lower lower)) rnd-mode mixed-mode?) "\n"))

;;
(define (sat-validity-constraints type-of-check var-list result-var)
  (if (equal? type-of-check "validity")
      (list "\n(assert (not " "))")
      (list "\n(assert " ")"))); note: the returned function also nees to know how many parens to close

;;
(define (convert-to-string var-list)
  (if (empty? var-list)
      ""
      (let* ((first-element (first var-list))
             (var (get-var-symbol first-element)
                  ))
        (string-append (symbol->string var) " " (convert-to-string (rest var-list))))))

;;
(define (get-val-two-to-exp-p-minus-e-var precision lower)
  (bf/ (bfexp2 (bf precision)) (get-power-of-two-lower lower)))

;;
(define (fp-atomic-exp? exp)
  (or (symbol? exp) (number? exp)))
;)

;;
(define (naming-op? op)
  (equal? op ':))

;;
(define (named-prop? exp)
  (and (naming-op? (first exp)) (symbol? (second exp))))

;; note: var-list-filename is no longer required
(define (generate-skeleton s-expr var-list rnd-mode lower-two-to-exp-p-minus-e-var lower higher var-list-file-name precision mixed-mode? prop-name)
  (cond
    [(empty? s-expr) (list "" '() "")]
    [(not-exp? s-expr)
     (let* ((recursive-call-result (generate-skeleton (second s-expr)
                                                      var-list
                                                      rnd-mode
                                                      lower-two-to-exp-p-minus-e-var
                                                      lower
                                                      higher
                                                      var-list-file-name precision mixed-mode? prop-name))
            (skeleton-recursive-call-result (third recursive-call-result))
            (new-skeleton (string-append "(not " skeleton-recursive-call-result ")")))
       (list (first recursive-call-result) (second recursive-call-result) new-skeleton))]
    [(binary-boolean-exp? s-expr)
     (let* ((left-recursive-call-result (generate-skeleton (second s-expr)
                                                           var-list
                                                           rnd-mode
                                                           lower-two-to-exp-p-minus-e-var
                                                           lower
                                                           higher
                                                           var-list-file-name precision mixed-mode? prop-name))
            (right-recursive-call-result (generate-skeleton (third s-expr)
                                                            (append (second left-recursive-call-result) var-list)
                                                            rnd-mode
                                                            lower-two-to-exp-p-minus-e-var
                                                            lower
                                                            higher
                                                            var-list-file-name precision mixed-mode? prop-name))
            (skeleton-left-recursive-call-result (third left-recursive-call-result))
            (skeleton-right-recursive-call-result (third right-recursive-call-result))
            (new-skeleton (string-append "(" (symbol->string (first s-expr)) " " skeleton-left-recursive-call-result
                                         " " skeleton-right-recursive-call-result ")")))
       (list (string-append (first left-recursive-call-result) (first right-recursive-call-result))
             (append (second left-recursive-call-result) (second right-recursive-call-result))
             new-skeleton))]
    [(named-prop? s-expr)
     (let* ((check (set! NAMED-PROP-CONSTRAINTS (string-append NAMED-PROP-CONSTRAINTS 
                                                   ";approx: (assert (= " (expr->string (second s-expr)) " " (expr->string (third s-expr))"))\n"))))
(generate-skeleton (third s-expr) var-list rnd-mode lower-two-to-exp-p-minus-e-var lower higher var-list-file-name precision mixed-mode? (symbol->string (second s-expr))))]
    [(relational-exp? s-expr)
     (let* (
            (left-exp (second s-expr))
            (left-var (if (fp-atomic-exp? left-exp)
                          (if (number? left-exp)
                                (string-append "const-" (remove-trailing-zeroes (bigfloat->decimal-string (bf left-exp))))
                                 left-exp)
                          (variable-not-in var-list (term new))))
            ;(left-var (if (fp-atomic-exp? left-exp)
             ;             left-exp
              ;            (variable-not-in var-list (term new))))
            (left-result 
             (if (equal? left-var left-exp)
                 (list "" empty)
                 (generate-z3-constraints-for-exp left-var left-exp
                                                  (append (list left-var) var-list) rnd-mode
                                                  lower-two-to-exp-p-minus-e-var lower higher
                                                  var-list-file-name false mixed-mode?)))
            (right-exp (third s-expr))
            ;; old right-var replaced by this
            (right-var (if (fp-atomic-exp? right-exp)
                           (if (number? right-exp)
				(string-append "const-" (remove-trailing-zeroes (bigfloat->decimal-string (bf right-exp))))
                                 right-exp)
                           (variable-not-in (append (list left-var) (second left-result) var-list) (term new))))
            (right-result 
             (if (equal? right-var right-exp)
                 (list "" empty)
                 (generate-z3-constraints-for-exp right-var right-exp
                                                  (append (list left-var right-var (second left-result)) var-list) rnd-mode
                                                  lower-two-to-exp-p-minus-e-var lower higher
                                                  var-list-file-name false mixed-mode?)))

            (check (set! NAMED-PROP-CONSTRAINTS (string-append NAMED-PROP-CONSTRAINTS "(assert (= "prop-name " " 
                                                 "(" (symbol->string (first s-expr))
                                        	" " (symbol->string left-var)
                                         	" " (symbol->string right-var)
                                         	")))\n")))
     
            (new-skeleton prop-name
;; following 5 lines finally commented on Apr 10
;;                                       (string-append "(" 
                                         ;;(symbol->string (first s-expr)) 
                                         ;;" " (symbol->string left-var)
                                         ;;" " (symbol->string right-var)
                                         ;;")")
                                          )
            
            )
       (list (string-append (first left-result) (first right-result))
             (append (if (equal? left-exp left-var) empty (list left-var))
                     (if (equal? right-exp right-var) empty (list right-var))
                     (second left-result)
                     (second right-result))
             new-skeleton))]
    ))

;;
(define (replace-constants-with-vars s-expr)
  (cond 
    [(eof-object? s-expr) '()]
    [(empty? s-expr) '()]
    [(number? s-expr)
     (string->symbol (string-append "const-" (remove-trailing-zeroes (bigfloat->decimal-string (bf s-expr))) "-rounded"))]
    [(not-exp? s-expr) (list (first s-expr) (replace-constants-with-vars (second s-expr)))]
    [(relational-exp? s-expr) (list (first s-expr) (replace-constants-with-vars (second s-expr)) (replace-constants-with-vars (third s-expr)))]
    [(or (binary-boolean-exp? s-expr)(arithmetic-exp? s-expr))
     (list (first s-expr) (replace-constants-with-vars (second s-expr)) (replace-constants-with-vars (third s-expr)))]
    [else s-expr]))

;;
(define (get-error-check-stmt mode input-constant)
  (if (equal? mode "r");check if relative error
      (string-append "(assert (> abs-delta (* " input-constant " ideal-sum)))\n")
      (if (equal? mode "a")
          (string-append "(assert (> abs-delta " input-constant "))");;this is for absolute error: mode "a"
          "")))

;;
(define (subtract-lists l1 l2)
  (if (empty? l1)
      '()
      (if (member (first l1) l2)
          (subtract-lists (rest l1) l2)
          (cons (first l1) (member (rest l1) l2)))))

;;
(define (get-not-common l1 l2)
  (subtract-lists (append l1 l2) (union l1 l2)))

;;
(define (union l1 l2)
  (if (empty? l1)
      l2
      (if (member (first l1) l2)
          (union (rest l1) l2)
          (cons (first l1) (union (rest l1) l2)))))
;;
(define (in-first-not-in-second l1 l2)
  (if (empty? l1)
      '()
      (if (member (first l1) l2)
          (in-first-not-in-second (rest l1) l2)
          (cons (first l1) (in-first-not-in-second (rest l1) l2)))))
;; 
;;
(define (top-level-code-generator s-expr rnd-mode precision type-of-check lower higher var-list-file-name mode input-constant s-expr-formula mixed-mode?)
  (let* (
         (var-list (remove-duplicates (get-all-variables-in s-expr)))
         (var-list-formula (remove-duplicates (get-all-variables-in s-expr-formula)))
         (appended-var-list (union var-list var-list-formula))
         (s-expr-new (replace-constants-with-vars s-expr))
         (test-str (if (empty? var-list) "Empty var list" "Non-empty var list"))
         (var-list-as-string (convert-to-string appended-var-list))
         ;(test-str2 (with-output-to-file "jai.txt" (lambda () (display (string-append var-list-as-string "\ngood")))#:exists 'replace))
         (temp (with-output-to-file var-list-file-name (lambda () (display var-list-as-string))#:exists 'replace))
         (temp3 (if (equal? mode "p")  (with-output-to-file var-list-file-name (lambda () (display "ideal-sum exp-var delta abs-delta"))#:exists 'append) ""))
         (result-var (first (variables-not-in var-list (list 'result))))
         (lower-two-to-exp-p-minus-e-var (get-val-two-to-exp-p-minus-e-var precision lower))
         (initial-z3-exp (generate-initial-z3-code var-list precision lower higher rnd-mode mixed-mode?))
         (val-sat-check (sat-validity-constraints type-of-check var-list result-var))
         (result-tuple (generate-skeleton s-expr-new var-list
                                          rnd-mode lower-two-to-exp-p-minus-e-var
                                          lower higher var-list-file-name precision mixed-mode? "dummy-prop-name"))
         (rnd-fn-call (string-append RND-HEADER "(" (get-rounding-function-name rnd-mode) " x xr))\n\n"))
         (range-split-definition (string-append define-fun-preamble (generate-constraints-for-range-split "var" lower higher lower-two-to-exp-p-minus-e-var) "))\n"))
         (temp2 
          (first 
           (generate-z3-constraints-for-exp 'exp-var (replace-constants-with-vars s-expr-formula) 
                                            (remove-duplicates (append var-list (second result-tuple))) rnd-mode
                                            (expt 2.0 precision)
                                            lower higher var-list-file-name
                                            false mixed-mode?))
          ;))#:exists 'replace)
          )
         (new-vars (in-first-not-in-second (remove-duplicates (get-all-variables-in s-expr-formula))
                                           (remove-duplicates (append var-list (second result-tuple)))))
         (constraint-file-contents
          (if (equal? mode "n");;modified@NASA by Jaideep
              (string-append  ";; " (expr->string s-expr) "\n" SMT2-ROUNDING-FUNCTION-DEFINITIONS "\n" rnd-fn-call "\n"
                              range-split-definition
                              initial-z3-exp                      
                              (first result-tuple)
                              "\n;; Skeleton:\n"
                              (first val-sat-check)
                              (third result-tuple)
                              (second val-sat-check); get one or 2 closing parens depending on sat or validity check
                              NAMED-PROP-CONSTRAINTS
                              "\n(check-sat)\n(get-model)\n"
                              );end code for normal mode
              ;; for abs/rel error checking:
              (let* ((no-constraint (eof-object? s-expr)))
                
                (string-append  ";; " (expr->string s-expr) "\n" SMT2-ROUNDING-FUNCTION-DEFINITIONS "\n" initial-z3-exp                        
                                (first result-tuple)
                                (if no-constraint
                                    ""
                                    "(assert ")
                                (third result-tuple)
                                (if no-constraint
                                    ""
                                    ")")
                                "\n;;Comparison between Real and Floating-point\n"
                                ";;Start Test code\n"
                                (generate-initial-z3-code-var-list new-vars lower higher (get-val-two-to-exp-p-minus-e-var precision (get-power-of-two-lower lower)))
                                
                                "\n;;End test code\n"
                                (first (generate-z3-constraints-for-exp 'exp-var (replace-constants-with-vars s-expr-formula)
                                                                        (remove-duplicates (append var-list (second result-tuple))) rnd-mode
                                                                        (get-val-two-to-exp-p-minus-e-var precision lower)
                                                                        lower higher var-list-file-name
                                                                        false mixed-mode?))
                                "(declare-const ideal-sum Real)\n"
                                "(declare-const delta Real)\n"
                                "(declare-const abs-delta Real)\n"
                                "(assert (= ideal-sum " (expr->string s-expr-formula) "))\n" 
                                "(assert (= delta (- ideal-sum exp-var)))\n"
                                "(assert (=> (< delta 0.0) (= abs-delta (- delta))))\n"
                                "(assert (=> (>= delta 0.0) (= abs-delta delta)))\n"
                                (get-error-check-stmt mode input-constant)
                                "\n(check-sat)\n(get-model)\n"
                                )))
          )
         (check (display constraint-file-contents))
         )
    (custodian-shutdown-all (current-custodian))))

;;

(let* ((config (file->string (vector-ref (current-command-line-arguments) 0)))
       (var-list-file-name (vector-ref (current-command-line-arguments) 1))
       (l (string-split config "\n"))
       (precision (string->number (first l)))
       (rnd-mode (second l))
       (type-of-check (third l))
       (lower  (string->number (fourth l)))
       (higher (string->number (fifth l)))
       (mode (sixth l));;added@NASA by Jaideep for Deviation/Divergence check
       (input-constant (seventh l));;added@NASA by Jaideep for Deviation/Divergence check
       (mixed-mode? (if (<= 8 (length l))(equal? "mixed" (eighth l)) false))
       (s-expr (read-from-string (read-line)))
       (s-expr-formula (if (equal? mode "n") '(+ a b) (read-from-string (read-line))))
       (constraint-file-contents
        (top-level-code-generator s-expr rnd-mode precision type-of-check (get-power-of-two-lower (bf lower)) (get-power-of-two-higher (bf higher)) var-list-file-name mode input-constant s-expr-formula mixed-mode?)))
  (display constraint-file-contents))

