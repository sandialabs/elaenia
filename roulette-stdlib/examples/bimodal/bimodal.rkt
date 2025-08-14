#lang roulette/example/disrupt

(require "../../stdlib.rkt")

(define (read-csv->list filename)
  (define l (list))
  (for ([line (in-lines (open-input-file filename))])
    (set! l (append l (list (string-split line ",")))))
  l)

(define data (read-csv->list "bimodal.csv"))
(define processed-data
  (map (lambda (datapoint) (cons (string->number (list-ref datapoint 0))
                                 (string-ref (list-ref datapoint 1) 1)))
       data))
(define numbers-only-data (map car processed-data))

; This gives back different result than the R example but still gets the point
; across
(define (histogram data num-bins)
  (define data-min (apply min data))
  (define data-max (apply max data))
  (define bin-width (/ (- data-max data-min) num-bins))

  (define bins (for/list ([i (in-range num-bins)])
                 (list (+ data-min (* i bin-width)) (+ data-min (* (add1 i) bin-width)))))

  (define counts (for/list ([bin bins])
                   (length (filter (lambda (x)
                                     (and (>= x (first bin))
                                          (< x (second bin))))
                                   data))))

  (define total (apply + counts))
  (define densities (map (lambda (count) (if (= total 0) 0 (* 1.0 (/ count total)))) counts))

  (define midpoints (map (lambda (bin) (/ (+ (first bin) (second bin)) 2)) bins))

  (list midpoints densities))

(define hist (histogram (drop numbers-only-data 1) 15))
(define hist-pmf-list (map cons (list-ref hist 0) (list-ref hist 1)))
(define hist-pmf (pmf-list->symbol-pmf hist-pmf-list))
(plot-discrete hist-pmf "result_plot.png")
