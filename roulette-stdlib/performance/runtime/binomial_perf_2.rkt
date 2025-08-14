#lang roulette/example/disrupt

(define (add x y)
  (for*/all ([x x] [y y])
    (string->symbol
     (number->string
      (+ (string->number (symbol->string x))
         (string->number (symbol->string y)))))))

(define (binomial p n)
  (for/fold ([acc '|0|])
            ([_ (in-range n)])
    (add acc (if (flip p) '|1| '|0|))))

(define num-trials (string->number (vector-ref (current-command-line-arguments) 0)))

(equal? '|2| (binomial 1/2 num-trials))
