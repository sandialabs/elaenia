#lang roulette/example/disrupt

(require math/distributions)
(require math/flonum)

(require "../stdlib.rkt")

(define (model)
  ;;;; Roulette stdlib version
  (define max-errors '|3|)
  (match-define (cons nrm _) (rlt-normal 0 1 #:trials 300))
  (define g (rlt-geometric 1/2 50))
  (define nrm-gt-2 (sym-gt nrm '|2|))
  ; We need to coerce the boolean support to numeric support in order
  ; to add (nrm > 2) to g. The reason this works without any extra effort
  ; in WebPPL is because of the infamous JS coercion semantics.
  (define coerced-nrm-gt-2 (bool-support->num-support nrm-gt-2))
  (define g-add-nrm (sym-add g coerced-nrm-gt-2))
  ; Have to do the density/infer thing b/c by default roulette truncates the
  ; resulting floating point number to 6 decimal places when printing
  (define roulette-result ((density (infer (sym-gt g-add-nrm max-errors))) '|#t|))

  ;;;; Racket stdlib version
  (define rkt-max-error 3)
  (define rkt-nrm (normal-dist 0 1))
  (define rkt-geom (geometric-dist 1/2))
  (define rkt-nrm-gt-2 (cdf rkt-nrm 2 #f #t))
  (define rkt-geoms (sample rkt-geom 10000))

  (define (pr n samples epsilon)
    (* 1.0 (/ (count (lambda (x) (and (>= x (- n epsilon)) (<= x (+ n epsilon)))) samples)
           (length samples))))

  (define max-sample (apply max rkt-geoms))

  ; This is an implementation of adding distributions that is specific to this
  ; particular usecase.
  ;
  ; Expects bin-dist to be (cons Pr(0) Pr(1)) for some distribution with only two
  ; cases. n should be at least as big as the maximum sample in samples + 1.
  (define (add-dists bin-dist samples n)
    (define l (list))
    (for ([i (range (add1 n))])
      (set! l
        (append l
                (list (+ (* (car bin-dist) (pr i samples 0.0001))
                         (* (cdr bin-dist) (pr (sub1 i) samples 0.0001)))))))
    l)

  (define rkt-g-add-nrm (add-dists (cons (- 1 rkt-nrm-gt-2) rkt-nrm-gt-2)
                                   rkt-geoms
                                   (ceiling (add1 max-sample))))

  ; This result will not stay consistent between runs since it depends on sampling
  (define rkt-result (apply + (drop rkt-g-add-nrm (add1 rkt-max-error))))

  (cons roulette-result rkt-result))

(model)

