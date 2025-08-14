#lang roulette/example/disrupt

(provide plot-continuous plot-discrete)

(require "util.rkt")
(require "symbol_ops.rkt")
(require plot)

; NOTE: This doesn't show the slices within each trapezoid that we use to actually
; calculate the integral (defined by `trapezoid-intervals`) since by default we have
; this set to 1000 which would just result in too much information on the graph and
; make it unreadable.
;
; NOTE: Also, we draw rectangles, not trapezoids since we can't reconstruct the
; slopes of the lines between each of the points that we had originally without
; using the pdf.
(define (plot-continuous distribution closed-form-fcn [filename "plot.png"])
  (define sorted-dist-list
    (sort (map (lambda (x) (cons (symbol->number (car x)) (cdr x)))
               (pmf->list distribution list))
        < #:key car))

  (define x-min (car (first sorted-dist-list)))
  (define x-max (car (last sorted-dist-list)))

  (define bucket-width (/ (abs (- x-max x-min)) (length sorted-dist-list)))

  ; create ivl of each point +- 1/2 bucket width, height is also ivl w 0 and calculated area
  ; ivls used to create rectangles
  (define ivl-list (map
                    (lambda (p)
                      (match-define (list midpoint area) p)
                      (define x-left (- midpoint (/ bucket-width 2)))
                      (define x-right (+ midpoint (/ bucket-width 2)))
                      (define x-interval (ivl x-left x-right))
                      (define height (/ area bucket-width))
                      (define y-interval (ivl 0 height))
                      (list x-interval y-interval))
                    sorted-dist-list))

  (plot
   (list
    (rectangles ivl-list)
    (function closed-form-fcn x-min x-max #:color 3))
   #:x-min (sub1 x-min)
   #:y-min 0
   #:x-max (add1 x-max)
   #:y-max 1
   #:x-label "x"
   #:y-label "Pr(x)"
   #:out-file filename))

(define (plot-discrete distribution [filename "plot.png"])
  (define sorted-dist-list
    (sort (map (lambda (x) (cons (symbol->number (to-symbol (car x))) (cdr x)))
               (pmf->list distribution list))
        < #:key car))

  (define x-min (car (first sorted-dist-list)))
  (define x-max (car (last sorted-dist-list)))

  ; list of pairs of ((x, 0), (x, y)) used to create vertical lines
  (define vertical-lines (map (lambda (p) (list (list (car p) 0) p)) sorted-dist-list))
  (define vertical-lines-plots (map (lambda (p) (lines p #:width 2)) vertical-lines))
  (plot
   (append
    (list (points sorted-dist-list))
    vertical-lines-plots)
   #:x-min (sub1 x-min)
   #:y-min 0
   #:x-max (add1 x-max)
   #:y-max 1
   #:x-label "x"
   #:y-label "Pr(x)"
   #:out-file filename))

