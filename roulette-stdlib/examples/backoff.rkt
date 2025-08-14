#lang roulette/example/disrupt
(require "../stdlib.rkt")

(define (symbol-num-unop x f)
  (for*/all ([x x])
    (to-symbol (f (symbol->number x)))))

; Two random variables. What is the probability they occur within
; 1 second of each other?
; May also want to (query (sym-gt (sym-abs (sym-sub x y)) '|1|))
; TODO: if <1 second, then keep trying (while loop)
(define (model)
  ; Using `match-define` to extract pmf
  (match-define (cons x _) (rlt-gamma 2 4))
  (match-define (cons y _) (rlt-gamma 2 4))
  (if (sym-gt (sym-abs (sym-sub x y)) '|1|)
      (sym-abs (sym-sub (car (rlt-normal 2 8)) (car (rlt-gamma 2 8))))
      (query (sym-abs (sym-abs (sym-sub x y)))))
)

(model)
