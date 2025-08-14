#lang roulette/example/disrupt

(require math/base)
(require math/special-functions)
(require math/number-theory)
(require "symbol_ops.rkt")
(require "util.rkt")

(provide rlt-degenerate rlt-geometric rlt-binomial rlt-uniform rlt-poisson
         rlt-normal rlt-chi-squared rlt-gamma rlt-beta rlt-exponential
         rlt-logistic rlt-cauchy rlt-softmax rlt-rademacher rlt-soliton
         rlt-hypergeometric)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Discrete Distributions

(define/contract (rlt-degenerate x)
  (-> any/c any)
  (if (flip 1) x #f))

(define/contract (rlt-uniform lst)
  (-> list? any)
  (define non-symbol-dist
    (match lst
      [(list) #f]
      [(list e) (if (flip 1) e #f)]
      [(list e1 e2) (if (flip 1/2) e1 e2)]
      [(cons e rest) (if (flip (/ 1 (length lst))) e (rlt-uniform rest))]))
  (pmf->symbol-pmf non-symbol-dist))

(define/contract (rlt-binomial n p)
  (-> exact-positive-integer? rational? any)
  (define non-symbol-dist
    (for/fold ([acc '|0|])
              ([_ (in-range n)])
      (sym-add acc (if (flip p) '|1| '|0|))))
  (pmf->symbol-pmf non-symbol-dist))

(define/contract (rlt-geometric p end)
  (-> rational? exact-positive-integer? any)
  (define (geom-aux p end)
    ; It's ok that we have the call to rlt-geometric within the flip conditional
    ; since performance only really tanks when you have it in both branches.
    (if (<= end 0) 0 (if (flip p) (+ 1 (geom-aux p (- end 1))) 0)))
  (pmf->symbol-pmf (geom-aux p end)))

(define/contract (rlt-poisson lam end)
  (-> real? exact-positive-integer? any)
  (define (rlt-poisson-pmf k)
    (/ (* (expt lam k) (expt (exp 1) (* -1 lam))) (factorial k)))
  (define pmf-list (build-list end (lambda (x) (cons x (rlt-poisson-pmf x)))))
  (pmf-list->symbol-pmf pmf-list))

(define (rlt-rademacher)
  (if (flip 0.5) '|1| '|-1|))

(define/contract (rlt-soliton k)
  (-> exact-positive-integer? any)
  (define (rlt-soliton-pmf x k)
    (if (equal? x 1)
        (/ 1 k)
        (/ 1 (* x (- x 1)))))
  (define pmf-list (map (lambda (x) (cons x (rlt-soliton-pmf x k))) (range 1 (+ 1 k))))
  (pmf-list->symbol-pmf pmf-list))

(define/contract (rlt-hypergeometric N K n)
  (-> exact-nonnegative-integer? exact-nonnegative-integer? exact-nonnegative-integer? any)
  (define (rlt-hypergeometric-pmf N K n k)
    (/ (* (binomial K k) (binomial (- N K) (- n k))) (binomial N n)))
  (define pmf-list (map (lambda (x) (cons x (rlt-hypergeometric-pmf N K n x)))
                        (range (max 0 (- (+ n K) N)) (min K n))))
  (pmf-list->symbol-pmf pmf-list))

(define (positive-real-or-zero? x)
  (and (real? x) (or (positive? x) (zero? x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Continuous Distribution Utility Fcns

(define trapezoid-intervals 1000)

(define (max-in-range f a b)
  (define step (/ (- b a) trapezoid-intervals))
  (define l (map (lambda (x) (+ a (* step x))) (range 0 trapezoid-intervals)))
  (apply max (map f l)))

(define (get-max-abs f a b)
  (max-in-range (lambda (x) (abs (f x))) a b))

; Trapezoid rule
(define (integrate f a b)
  (define h (/ (- b a) trapezoid-intervals))
  (define (trapezoidal-rule i)
    (+ (f (+ a (* i h))) (f (+ a (* (+ i 1) h)))))
  (* (/ h 2)
     (apply + (map trapezoidal-rule (range 0 trapezoid-intervals)))))

(define (create-lin-range start end num-points)
  (define step (/ (- end start) (sub1 num-points)))
  (map (lambda (i) (+ start (* i step))) (range num-points)))

(define (iter-on-pairs f lst acc)
  (match lst
    [(list) acc]
    [(cons x '()) acc]
    [(cons a (cons b rst))
     (iter-on-pairs f (cons b rst) (cons (f a b) acc))]))

(define (get-total-error snd-deriv-closure range)
  (apply + (iter-on-pairs
              (lambda (a b)
                ; Trapezoid rule error formula
                (define numer (expt (- b a) 3))
                (define denom (* 12 (sqr trapezoid-intervals)))
                (define max-deriv (get-max-abs snd-deriv-closure a b))
                (/ (* numer max-deriv) denom))
            range '())))

(define (create-val-prob-pairs pdf range)
  (define (create-val-prob-pair a b)
    (define midpoint (/ (+ a b) 2))
    (define prob (integrate (lambda (x) (pdf x)) a b))
    (cons midpoint prob))
  (define val-prob-pairs (iter-on-pairs create-val-prob-pair range '()))
  val-prob-pairs)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal

; variance = sqrt(stddev)
(define (normal-pdf x mean sd)
  (define coefficient (/ 1 (* sd (sqrt (* 2 pi)))))
  (define exponent (exp (- (/ (sqr (- x mean)) (* 2 (sqr sd))))))
  (* coefficient exponent))

(define (normal-pdf-snd-deriv x mean sd)
  (define denom (* (sqrt (* 2 pi)) (expt sd 5)))
  (define exponent (/ (* -1 (sqr (- x mean))) (* 2 (sqr sd))))
  (define exponent-term (expt euler.0 exponent))
  (define numer-term (- (sqr mean) (+ (sqr sd) (- (sqr x) (* 2 (* mean x))))))
  (define numer (* exponent-term numer-term))
  (/ numer denom))

(define (norm-list mean sd start end n)
  (define lin-range (create-lin-range start end n))
  (define total-error (get-total-error
                        (lambda (x) (normal-pdf-snd-deriv x 0 1)) ; std norm here
                        lin-range))

  ; We start with standard normal then scale it for more predictable bucketing
  ; NOTE: I'm not sure how scaling affects the error
  (define val-prob-pairs (create-val-prob-pairs (lambda (x) (normal-pdf x 0 1)) lin-range))
  (define scaled-pairs
    (map (lambda (p)
           (cons (+ (* (car p) sd) mean) (cdr p))) val-prob-pairs))

  (cons scaled-pairs total-error))

(define/contract (rlt-normal mean sd #:start [start -10] #:end [end 10] #:trials [trials 300])
  (->* (rational? rational?)
       (#:start exact-integer? #:end exact-integer? #:trials exact-positive-integer?)
       any)
  (define trials-prime (if (even? trials) (+ 1 trials) trials))
  (match-define (cons l err) (norm-list mean sd start end trials-prime))
  (define complete-pmf (pmf->symbol-pmf (to-measure-backed-pmf l)))
  (cons complete-pmf err))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Chi-squared

(define (chi-squared-pdf x k)
  (define k/2 (/ k 2))
  (define gamma-k/2 (gamma k/2))
  (define 2^k/2 (expt 2 k/2))
  (define left-term (/ 1 (* 2^k/2 gamma-k/2)))
  (define x^k/2-1 (expt x (- k/2 1)))
  (define e^-x/2 (expt euler.0 (* -1 (/ x 2))))
  (define right-term (* x^k/2-1 e^-x/2))
  (* left-term right-term))

(define (chi-squared-pdf-snd-deriv x k)
  (define 2^-k/2-2 (expt 2 (* -1 (- (/ k 2) 2))))
  (define e^-x/2 (expt euler.0 (* -1 (/ x 2))))
  (define x^k/2-3 (expt x (- (/ k 2) 3)))
  (define term1 (* 2^-k/2-2 e^-x/2 x^k/2-3))
  (define term2 (- (sqr k) (+ (* 2 (* k (+ x 3))) (sqr x) (* 4 x) 8)))
  (define numer (* term1 term2))
  (define denom (gamma (/ k 2)))
  (/ numer denom))

(define/contract (rlt-chi-squared k end #:trials [n 300])
  (->* (exact-positive-integer? exact-positive-integer?) (#:trials exact-positive-integer?) any)
  ; chi-squared is not defined on 0 so drop it from range
  (define lin-range (drop (create-lin-range 0 end n) 1))
  (define total-error (get-total-error
                        (lambda (x) (chi-squared-pdf-snd-deriv x k))
                        lin-range))
  (define val-prob-pairs (create-val-prob-pairs (lambda (x) (chi-squared-pdf x k)) lin-range))
  (define result-pmf (pmf->symbol-pmf (to-measure-backed-pmf val-prob-pairs)))
  (cons result-pmf total-error))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Gamma

(define (gamma-pdf x alpha theta)
  (define left-term (/ 1 (* (gamma alpha) (expt theta alpha))))
  (define x^a-1 (expt x (- alpha 1)))
  (define e^-x/t (expt euler.0 (* -1 (/ x theta))))
  (define right-term (* x^a-1 e^-x/t))
  (* left-term right-term))

(define (gamma-pdf-snd-deriv x alpha theta)
  (define t^-a-2 (expt theta (* -1 (- alpha 2))))
  (define x^a-3 (expt x (- alpha 3)))
  (define e^-x/t (expt euler.0 (* -1 (/ x theta))))
  (define left-numer-term (* t^-a-2 x^a-3 e^-x/t))
  (define a^2-3a+2 (- (sqr alpha) (+ (* alpha 3) 2)))
  (define right-numer-term-1 (* (sqr theta) a^2-3a+2))
  (define right-numer-term-2 (* 2 (- alpha 1) theta alpha))
  (define right-numer-term-3 (sqr x))
  (define right-numer-term (- right-numer-term-1 (+ right-numer-term-2 right-numer-term-3)))
  (define numer (* left-numer-term right-numer-term))
  (define denom (gamma alpha))
  (/ numer denom))

(define/contract (rlt-gamma alpha theta #:end [end 20] #:trials [n 300])
  (->* (real? real?) (#:end exact-positive-integer? #:trials exact-positive-integer?) any)
  ; We drop 0 from the range because it is not defined for all values of alpha and theta
  ; so getting rid of it is the easiest option
  (define lin-range (drop (create-lin-range 0 end n) 1))
  (define total-error (get-total-error
                        (lambda (x) (gamma-pdf-snd-deriv x alpha theta))
                        lin-range))
  (define val-prob-pairs (create-val-prob-pairs (lambda (x) (gamma-pdf x alpha theta)) lin-range))
  (define result-pmf (pmf->symbol-pmf (to-measure-backed-pmf val-prob-pairs)))
  (cons result-pmf total-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Beta

(define (beta-pdf x alpha beta)
  (define B (/ (* (gamma alpha) (gamma beta))
               (gamma (+ alpha beta))))
  (define x^a-1 (expt x (- alpha 1)))
  (define 1-x^b-1 (expt (- 1 x) (- beta 1)))
  (define numer (* x^a-1 1-x^b-1))
  (/ numer B))

(define (beta-pdf-snd-deriv x a b)
  (define x^a-3 (expt x (- a 3)))
  (define one-x^b-3 (expt (- 1 x) (- b 3)))
  (define gamma:a+b (gamma (+ a b)))
  (define big-term-left (+ (sqr a) (* (sqr x) (- (+ a b) 3) (- (+ a b) 2))))
  (define big-term-right (- (* 2 (- a 1) x (- (+ a b) 3)) (+ (* a 3) 2)))
  (define big-term (- big-term-left big-term-right))
  (define numer (* x^a-3 one-x^b-3 big-term gamma:a+b))
  (define denom (* (gamma a) (gamma b)))
  (/ numer denom))

(define/contract (rlt-beta alpha beta #:trials [n 300])
  (->* (real? real?) (#:trials exact-positive-integer?) any)
  ; We drop 0 and 1 from the range because they are not defined for all values
  ; of alpha and beta so getting rid of them is the easiest option.
  ; This causes some combinations of alpha and beta to have *really* bad results.
  ; (e.g. alpha=0.5, beta=0.5 and alpha=5, beta=1)
  (define reduce-range (lambda (r) (drop (take r (- (length r) 1)) 1)))
  (define lin-range (reduce-range (create-lin-range 0 1 n)))
  (define total-error (get-total-error
                        (lambda (x) (beta-pdf-snd-deriv x alpha beta))
                        lin-range))
  (define val-prob-pairs (create-val-prob-pairs (lambda (x) (beta-pdf x alpha beta)) lin-range))
  (define result-pmf (pmf->symbol-pmf (to-measure-backed-pmf val-prob-pairs)))
  (cons result-pmf (* 1.0 total-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Exponential

(define (exponential-pdf x lam)
  (* lam (expt euler.0 (* -1 (* lam x)))))

(define (exponential-snd-deriv x lam)
  (* (expt lam 3) (expt euler.0 (* -1 (* lam x)))))

(define/contract (rlt-exponential lam #:end [end 20] #:trials [n 300])
  (->* (real?) (#:end exact-positive-integer? #:trials exact-positive-integer?) any)
  (define lin-range (create-lin-range 0 end n))
  (define total-error (get-total-error
                        (lambda (x) (exponential-snd-deriv x lam))
                        lin-range))
  (define val-prob-pairs (create-val-prob-pairs (lambda (x) (exponential-pdf x lam)) lin-range))
  (define result-pmf (pmf->symbol-pmf (to-measure-backed-pmf val-prob-pairs)))
  (cons result-pmf total-error))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Logistic

(define (logistic-pdf x mu s)
  (define exp-term (exp (* -1 (/ (- x mu) s))))
  (define denom (* s (sqr (+ 1 exp-term))))
  (/ exp-term denom))

(define (logistic-snd-deriv x mu s)
  (define term1 (- (cosh (/ (- mu x) s)) 2))
  (define term2 (expt (/ 1 (cosh (/ (- mu x) (* 2 s)))) 4))
  (define numer (* term1 term2))
  (define denom (* 8 (expt s 3)))
  (/ numer denom))

(define/contract (rlt-logistic mu s #:start [start -10] #:end [end 10] #:trials [n 300])
  (->* (real? real?) (#:start exact-positive-integer? #:end exact-positive-integer? #:trials exact-positive-integer?) any)
  (define lin-range (create-lin-range start end n))
  (define total-error (get-total-error
                       (lambda (x) (logistic-snd-deriv x mu s))
                       lin-range))
  (define val-prob-pairs (create-val-prob-pairs (lambda (x) (logistic-pdf x mu s)) lin-range))
  (define result-pmf (pmf->symbol-pmf (to-measure-backed-pmf val-prob-pairs)))
  (cons result-pmf total-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cauchy

(define (cauchy-pdf x x0 gma)
  (define squared-term (sqr (/ (- x x0) gma)))
  (define denom (* pi gma (+ 1 squared-term)))
  (/ 1 denom))

(define (cauchy-snd-deriv x x0 gma)
  (define top-inner-term (* 3 (sqr (- x x0))))
  (define numer (* 2 gma (- (sqr gma) top-inner-term)))
  (define bottom-inner-term (+ (sqr gma) (sqr (- x x0))))
  (define denom (* pi (expt bottom-inner-term 3)))
  (* -1 (/ numer denom)))

(define/contract (rlt-cauchy x0 gma #:start [start -10] #:end [end 10] #:trials [n 300])
  (->* (real? real?) (#:start exact-positive-integer? #:end exact-positive-integer? #:trials exact-positive-integer?) any)
  (define lin-range (create-lin-range start end n))
  (define total-error (get-total-error
                       (lambda (x) (cauchy-snd-deriv x x0 gma))
                       lin-range))
  (define val-prob-pairs (create-val-prob-pairs (lambda (x) (cauchy-pdf x x0 gma)) lin-range))
  (define result-pmf (pmf->symbol-pmf (to-measure-backed-pmf val-prob-pairs)))
  (cons result-pmf total-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Miscellaneous Functions

(define (rlt-softmax scores)
  (define exps (map exp scores))
  (define sum-exps (apply + exps))
  (define probs (map (lambda (x) (/ x sum-exps)) exps))
  (pmf-list->symbol-pmf (map (lambda (val prob) (cons val prob)) scores probs)))
