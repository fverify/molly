#lang racket
(require mzlib/string)
;; checks if an expression is of the form (not <exp>)
(define (not-exp? exp)
  (and (list? exp) (equal? 'not (first exp))))

(define (get-all-variables-in exp)
  (cond
    [(eof-object? exp) '()]
    [(empty? exp) '()]
    [(number? exp) '()]
    [(symbol? exp) (list exp)]
    [(not-exp? exp)
     (get-all-variables-in (second exp))]
    [else (append (get-all-variables-in (second exp)) (get-all-variables-in (third exp)))]))

;(remove-duplicates (get-all-variables-in '(< (+ x y) z)))
;(vector-ref (current-command-line-arguments) 0)

(define (list->string l)
  (if (empty? l)
      ""
      (string-append (symbol->string (first l)) " " (list->string (rest l)))))

(display (list->string (remove-duplicates (get-all-variables-in (read-from-string (read-line))))))