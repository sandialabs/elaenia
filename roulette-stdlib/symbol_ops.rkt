#lang roulette/example/disrupt

(provide (all-defined-out))

(require "util.rkt")

(define (number->symbol x)
  (string->symbol (number->string x)))

(define (symbol->number x)
  (string->number (symbol->string x)))

(define (boolean->symbol b)
  (string->symbol (if b "#t" "#f")))

(define (symbol->boolean b)
  (match (symbol->string b)
    ["#t" #t]
    ["#f" #f]))

(define (to-symbol x)
  (cond
    [(symbol? x) x]
    [(number? x) (number->symbol x)]
    [(boolean? x) (boolean->symbol x)]))

(define (symbol-num-unop x f)
  (for*/all ([x x])
    (to-symbol (f (symbol->number x)))))

(define (sym-abs x)
  (symbol-num-unop x abs))

(define (symbol-num-binop x y f)
  (for*/all ([x x] [y y])
    (to-symbol (f (symbol->number x) (symbol->number y)))))

(define (sym-add x y)
  (symbol-num-binop x y +))

(define (sym-sub x y)
  (symbol-num-binop x y -))

(define (sym-mul x y)
  (symbol-num-binop x y *))

(define (sym-div x y)
  (symbol-num-binop x y /))

(define (sym-lt x y)
  (symbol-num-binop x y <))

(define (sym-gt x y)
  (symbol-num-binop x y >))

(define (sym-lte x y)
  (symbol-num-binop x y <=))

(define (sym-gte x y)
  (symbol-num-binop x y >=))

(define (symbol-bool-binop x y f)
  (for*/all ([x x] [y y])
    (to-symbol (f (symbol->boolean x) (symbol->boolean y)))))

(define (sym-and x y)
  (symbol-bool-binop x y (lambda (a b) (and a b))))

(define (sym-or x y)
  (symbol-bool-binop x y (lambda (a b) (or a b))))


(define (pmf-list->symbol-pmf h)
  (define symbol-h (map (lambda (x) (cons (to-symbol (car x)) (cdr x))) h))
  (to-measure-backed-pmf symbol-h))

(define (pmf-hash->symbol-pmf h)
  (pmf-list->symbol-pmf (hash->list h)))

(define (symbol-pmf->list p)
  (for/list ([(val prob) (in-pmf (query p))])
    (cons val prob)))

(define (symbol-pmf->sorted-list p)
  (sort (symbol-pmf->list p)
        < #:key car))

(define (symbol-pmf->hash p)
  (make-hash (symbol-pmf->list p)))

(define (pmf->symbol-pmf h)
  (pmf-list->symbol-pmf (pmf->list h)))

(define (bool-support->num-support h)
  (define l (pmf->list h))
  (pmf-list->symbol-pmf (map (lambda (p)
                               (if (symbol->boolean (car p))
                                   (cons 1 (cdr p))
                                   (cons 0 (cdr p)))) l)))

(define (extract-true-case-prob p)
  (define l (symbol-pmf->list p))
  (match l
    [(list (cons '|#t| 1.0)) 1]
    [(list (cons '|#f| 1.0)) 0]
    [(list (cons '|#t| prob) _) prob]
    [(list _ (cons '|#t| prob)) prob]))
