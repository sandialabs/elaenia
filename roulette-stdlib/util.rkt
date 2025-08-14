#lang roulette/example/disrupt

(provide to-measure-backed-pmf pmf->list dist-list-equal)

(define (pmf->list m [consing-fcn cons])
  (for/list ([(val prob) (in-pmf (query m))])
    (consing-fcn val prob)))

; Function that Cameron gave, turns a list of (val prob) pairs into a
; *measure backed* pmf. By "measure backed" I mean that we use flip which
; calls `define-measureable[*]` unlike the `pmf` constructor which does not.
; Not calling `define-measurable[*]` results in something that looks like a pmf
; but does not have any Rosette symbolic variables actually constructed, so it's
; not an actual pmf that can interact with the Roulette backend.
(define (to-measure-backed-pmf xs)
  (let go ([xs xs] [p 1])
    (match xs
      [(list (cons b _)) b]
      [(cons (cons b x) xt)
       (define p* (/ x p))
       (if (flip p*)
           b
           (go xt (* p (- 1 p*))))])))

(define (list-equal f l1 l2)
  (if (not (equal? (length l1) (length l2)))
      #f
      (foldl (lambda (b acc) (and b acc)) #t (map (lambda (a b) (f a b)) l1 l2))))

(define (dist-list-equal l1 l2 epsilon)
  ; Turning into a hash to "sort" the support values, there is no ordering on
  ; symbols so can't use < etc. Alternative could be turning into strings and
  ; then sorting lexicographically.
  (define sorted-l1 (hash->list (make-hash l1)))
  (define sorted-l2 (hash->list (make-hash l2)))
  (define (val-prob-pairs-equal a b)
    (match-define (cons a-val a-prob) a)
    (match-define (cons b-val b-prob) b)
    (and (equal? a-val b-val) (< (abs (- a-prob b-prob)) epsilon)))
  (list-equal val-prob-pairs-equal sorted-l1 sorted-l2))
