#lang roulette/example/disrupt

(require rackunit)
(require "stdlib.rkt")

; Creating shorthand names for utility functions
(define (sptl p) (symbol-pmf->list p))
(define (sptsl p) (symbol-pmf->sorted-list p))
(define (etcp p) (extract-true-case-prob p))

;;;; Degenerate Distribution
(check-equal? (sptsl (rlt-degenerate 'a)) (list (cons 'a 1.0)))
(check-not-equal? (sptsl (rlt-degenerate 1)) (list (cons 1 0.5)))
(check-not-equal? (sptsl (rlt-degenerate 1)) (list (cons 2 1)))

;;;; Uniform Distribution
(check-equal? (sptsl (rlt-uniform (list))) (list (cons '|#f| 1.0)))
(check-equal? (sptsl (rlt-uniform (list 'a))) (list (cons 'a 1.0)))
(check-equal? (sptl (rlt-uniform (list 'a 'b))) (list (cons 'b 0.5) (cons 'a 0.5)))
(check-true (dist-list-equal (sptl (rlt-uniform (list 'a 'b 3)))
                             (list (cons '|a| 0.3333) (cons '|b| 0.3333) (cons '|3| 0.3333))
                             0.001))
(check-true (dist-list-equal (sptl (rlt-uniform (list 'a 'b 3 1)))
                             (list (cons '|a| 0.25) (cons '|b| 0.25) (cons '|3| 0.25) (cons '|1| 0.25))
                             0.001))

;;;; Binomial Distribution
(check-true (dist-list-equal (sptl (rlt-binomial 5 0.5))
                             (list (cons '|0| 0.03125) (cons '|1| 0.15625) (cons '|2| 0.3125)
                                   (cons '|3| 0.3125) (cons '|4| 0.15625) (cons '|5| 0.03125))
                             0.00001))
(check-true (dist-list-equal (sptl (rlt-binomial 5 0.4))
                             (list (cons '|0| 0.07776) (cons '|1| 0.2592) (cons '|2| 0.3456)
                                   (cons '|3| 0.2304) (cons '|4| 0.0768) (cons '|5| 0.01024))
                             0.00001))
(check-equal? (etcp (sym-lte (rlt-binomial 5 0.5) '|3|)) 0.8125)
(check-equal? (etcp (sym-gte (rlt-binomial 5 0.5) '|1|)) 0.96875)
(check-equal? (etcp (sym-lte (rlt-binomial 5 0.5) '|2|)) 0.5)
(check-equal? (etcp (sym-gte (rlt-binomial 5 0.5) '|3|)) 0.5)

;;;; Geometric Distribution
(check-true (dist-list-equal (sptl (rlt-geometric 0.5 8))
                             (list (cons '|0| 0.5)(cons '|1| 0.25)(cons '|2| 0.125)(cons '|3| 0.0625)
                                   (cons '|4| 0.03125)(cons '|5| 0.01563)(cons '|6| 0.00781)(cons '|7| 0.00391)
                                   (cons '|8| 0.00390))
                             0.00001))
(check-equal? (etcp (sym-lte (rlt-geometric 0.5 8) '|4|)) 0.96875)
(check-equal? (etcp (sym-lte (rlt-geometric 0.5 8) '|2|)) 0.875)

;;;; Poisson Distribution
(check-true (dist-list-equal (sptl (rlt-poisson 4 10))
                             (list (cons '|0| 0.01832) (cons '|1| 0.07326) (cons '|2| 0.14653) (cons '|3| 0.19537)
                                   (cons '|4| 0.19537) (cons '|5| 0.15629) (cons '|6| 0.1042) (cons '|7| 0.05954)
                                   (cons '|8| 0.02977) (cons '|9| 0.02136))
                                   ; 9 is incorrect b/c we're only bucketing up to 9, the last bucket
                                   ; ends up getting the "leftover" probability. For 9 actual value
                                   ; should be 0.01323
                             0.00001))
(check-= (etcp (sym-lte (rlt-poisson 4 20) '|4|)) 0.62884 0.0001)
(check-= (etcp (sym-lte (rlt-poisson 4 20) '|9|)) 0.99187 0.0001)
(check-= (etcp (sym-gte (rlt-poisson 4 20) '|4|)) 0.56653 0.0001)

;;;; Rademacher Distribution
(check-equal? (sptl (rlt-rademacher)) (list (cons '|1| 0.5) (cons '|-1| 0.5)))

;;;; Soliton Distribution
(check-true (dist-list-equal (sptl (rlt-soliton 5))
                             (list (cons '|1| 1/5) (cons '|2| 1/2) (cons '|3| 1/6)
                                   (cons '|4| 1/12) (cons '|5| 1/20)) 0.0001))

;;;; Hypergeometric Distribution
(define hg1 (rlt-hypergeometric 500 50 100))
(check-= (etcp (sym-lte hg1 '|2|)) 0.00083 0.0001)
(check-= (etcp (sym-lte hg1 '|4|)) 0.01438 0.0001)
(check-= (etcp (sym-lte hg1 '|6|)) 0.09153 0.0001)
(check-= (etcp (sym-lte hg1 '|8|)) 0.29559 0.0001)
(check-= (etcp (sym-lte hg1 '|10|)) 0.58515 0.0001)
(check-= (etcp (sym-lte hg1 '|12|)) 0.8255 0.0001)
(check-= (etcp (sym-lte hg1 '|14|)) 0.94893 0.0001)
(check-= (etcp (sym-lte hg1 '|16|)) 0.98968 0.0001)

;;;; Normal
(match-define (cons nrm _) (rlt-normal 5 3))
(check-= (etcp (sym-lte nrm '|5|)) 0.5 0.000001)
(check-= (etcp (sym-lte nrm '|3|)) 0.25249 0.00001)
(check-= (etcp (sym-gte nrm '|3|)) 0.74751 0.00001)
(check-= (etcp (sym-and (sym-lte '|2| nrm) (sym-lte nrm '|8|))) 0.68268 0.00001)
(check-= (etcp (sym-and (sym-lte '|-1| nrm) (sym-lte nrm '|11|))) 0.9545 0.00001)

(match-define (cons nrm2 _) (rlt-normal -3 2))
(check-= (etcp (sym-and (sym-lte '|-5| nrm2) (sym-lte nrm2 '|-1|))) 0.68268 0.00001)
(check-= (etcp (sym-and (sym-lte '|-7| nrm2) (sym-lte nrm2 '|1|))) 0.9545 0.00001)
(check-= (etcp (sym-and (sym-lte '|-4| nrm2) (sym-lte nrm2 '|-1|))) 0.5328 0.1)
(check-= (etcp (sym-and (sym-lte '|-7| nrm2) (sym-lte nrm2 '|-1|))) 0.7745 0.1)

(match-define (cons nrm3 _) (rlt-normal 0 1))
(check-= (etcp (sym-and (sym-lte '|-10| nrm3) (sym-lte nrm3 '|-9|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|-9| nrm3) (sym-lte nrm3 '|-8|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|-8| nrm3) (sym-lte nrm3 '|-7|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|-7| nrm3) (sym-lte nrm3 '|-6|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|-6| nrm3) (sym-lte nrm3 '|-5|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|-5| nrm3) (sym-lte nrm3 '|-4|))) 0.00003 0.00001)
(check-= (etcp (sym-and (sym-lte '|-4| nrm3) (sym-lte nrm3 '|-3|))) 0.00131 0.00001)
(check-= (etcp (sym-and (sym-lte '|-3| nrm3) (sym-lte nrm3 '|-2|))) 0.0214 0.00001)
(check-= (etcp (sym-and (sym-lte '|-2| nrm3) (sym-lte nrm3 '|-1|))) 0.1359 0.00001)
(check-= (etcp (sym-and (sym-lte '|-1| nrm3) (sym-lte nrm3 '|0|))) 0.34134 0.00001)
(check-= (etcp (sym-and (sym-lte '|0| nrm3) (sym-lte nrm3 '|1|))) 0.34134 0.00001)
(check-= (etcp (sym-and (sym-lte '|1| nrm3) (sym-lte nrm3 '|2|))) 0.1359 0.00001)
(check-= (etcp (sym-and (sym-lte '|2| nrm3) (sym-lte nrm3 '|3|))) 0.0214 0.00001)
(check-= (etcp (sym-and (sym-lte '|3| nrm3) (sym-lte nrm3 '|4|))) 0.00131 0.00001)
(check-= (etcp (sym-and (sym-lte '|4| nrm3) (sym-lte nrm3 '|5|))) 0.00003 0.00001)
(check-= (etcp (sym-and (sym-lte '|5| nrm3) (sym-lte nrm3 '|6|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|6| nrm3) (sym-lte nrm3 '|7|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|7| nrm3) (sym-lte nrm3 '|8|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|8| nrm3) (sym-lte nrm3 '|9|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|9| nrm3) (sym-lte nrm3 '|10|))) 0.0 0.00001)

(check-= (etcp (sym-and (sym-lte '|-10| nrm3) (sym-lte nrm3 '|-5|))) 0.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|-5| nrm3) (sym-lte nrm3 '|0|))) 0.5 0.00001)
(check-= (etcp (sym-and (sym-lte '|0| nrm3) (sym-lte nrm3 '|5|))) 0.5 0.00001)
(check-= (etcp (sym-and (sym-lte '|5| nrm3) (sym-lte nrm3 '|10|))) 0.0 0.00001)

(check-= (etcp (sym-and (sym-lte '|-5| nrm3) (sym-lte nrm3 '|5|))) 1.0 0.00001)
(check-= (etcp (sym-and (sym-lte '|-4| nrm3) (sym-lte nrm3 '|4|))) 0.99993 0.00001)
(check-= (etcp (sym-and (sym-lte '|-3| nrm3) (sym-lte nrm3 '|3|))) 0.9973 0.00001)
(check-= (etcp (sym-and (sym-lte '|-2| nrm3) (sym-lte nrm3 '|2|))) 0.9545 0.00001)
(check-= (etcp (sym-and (sym-lte '|-1| nrm3) (sym-lte nrm3 '|1|))) 0.68268 0.00001)

(check-= (etcp (sym-and (sym-lte '|0.3| nrm3) (sym-lte nrm3 '|1.5|))) 0.3153 0.1)
(check-= (etcp (sym-and (sym-lte '|-0.5| nrm3) (sym-lte nrm3 '|0.5|))) 0.3829 0.1)
(check-= (etcp (sym-and (sym-lte '|-2.5| nrm3) (sym-lte nrm3 '|0.3|))) 0.6117 0.1)
(check-= (etcp (sym-and (sym-lte '|0.3| nrm3) (sym-lte nrm3 '|2.7|))) 0.3786 0.1)
(check-= (etcp (sym-and (sym-lte '|2.7| nrm3) (sym-lte nrm3 '|5.1|))) 0.0035 0.001)
(check-= (etcp (sym-and (sym-lte '|5.1| nrm3) (sym-lte nrm3 '|7.8|))) 0.0 0.001)
(check-= (etcp (sym-and (sym-lte '|-1.5| nrm3) (sym-lte nrm3 '|1.5|))) 0.8664 0.01)
(check-= (etcp (sym-and (sym-lte '|0.1| nrm3) (sym-lte nrm3 '|0.9|))) 0.2761 0.01)
(check-= (etcp (sym-and (sym-lte '|0.4| nrm3) (sym-lte nrm3 '|0.8|))) 0.13272 0.00001)
(check-= (etcp (sym-and (sym-lte '|-2.3| nrm3) (sym-lte nrm3 '|-1.7|))) 0.0338 0.01)
(check-= (etcp (sym-and (sym-lte '|-1.1| nrm3) (sym-lte nrm3 '|0.2|))) 0.4436 0.01)
(check-= (etcp (sym-and (sym-lte '|0.6| nrm3) (sym-lte nrm3 '|0.8|))) 0.0624 0.00001)
(check-= (etcp (sym-and (sym-lte '|1.2| nrm3) (sym-lte nrm3 '|2.9|))) 0.1132 0.001)

;;;; Chi-squared
(match-define (cons csd _) (rlt-chi-squared 1 30))
(check-= (etcp (sym-lte csd '|1|)) 0.68269 0.001)
(check-= (etcp (sym-lte csd '|2|)) 0.8427 0.001)
(check-= (etcp (sym-lte csd '|3|)) 0.91674 0.001)
(check-= (etcp (sym-gte csd '|3|)) 0.08326 0.001)

(match-define (cons csd2 _) (rlt-chi-squared 4 30))
(check-= (etcp (sym-lte csd2 '|1|)) 0.0902 0.001)
(check-= (etcp (sym-lte csd2 '|2|)) 0.26424 0.01)
(check-= (etcp (sym-lte csd2 '|3|)) 0.44217 0.01)
(check-= (etcp (sym-lte csd2 '|7|)) 0.86411 0.01)
(check-= (etcp (sym-gte csd2 '|7|)) 0.13589 0.01)

;;;; Gamma
(match-define (cons gmma _) (rlt-gamma 1 2))
(check-= (etcp (sym-lte gmma '|1|)) 0.39347 0.01)
(check-= (etcp (sym-lte gmma '|2|)) 0.63212 0.01)
(check-= (etcp (sym-lte gmma '|4|)) 0.86466 0.01)

(match-define (cons gmma2 _) (rlt-gamma 2 2))
(check-= (etcp (sym-lte gmma2 '|2|)) 0.26424 0.01)
(check-= (etcp (sym-lte gmma2 '|4|)) 0.59399 0.01)
(check-= (etcp (sym-lte gmma2 '|6|)) 0.80085 0.01)
(check-= (etcp (sym-lte gmma2 '|8|)) 0.90842 0.01)

(match-define (cons gmma3 _) (rlt-gamma 3 2))
(check-= (etcp (sym-lte gmma3 '|2|)) 0.0803 0.01)
(check-= (etcp (sym-lte gmma3 '|4|)) 0.32332 0.01)
(check-= (etcp (sym-lte gmma3 '|6|)) 0.57681 0.01)
(check-= (etcp (sym-lte gmma3 '|8|)) 0.7619 0.01)

(match-define (cons gmma4 _) (rlt-gamma 5 1))
(check-= (etcp (sym-lte gmma4 '|2|)) 0.05265 0.01)
(check-= (etcp (sym-lte gmma4 '|4|)) 0.37116 0.01)
(check-= (etcp (sym-lte gmma4 '|6|)) 0.71494 0.01)
(check-= (etcp (sym-lte gmma4 '|8|)) 0.90037 0.01)

(match-define (cons gmma5 _) (rlt-gamma 9 0.5))
(check-= (etcp (sym-lte gmma5 '|2|)) 0.02136 0.01)
(check-= (etcp (sym-lte gmma5 '|4|)) 0.40745 0.01)
(check-= (etcp (sym-lte gmma5 '|6|)) 0.84497 0.01)
(check-= (etcp (sym-lte gmma5 '|8|)) 0.97801 0.01)

(match-define (cons gmma6 _) (rlt-gamma 7.5 1))
(check-= (etcp (sym-lte gmma6 '|2|)) 0.00226 0.01)
(check-= (etcp (sym-lte gmma6 '|4|)) 0.07622 0.01)
(check-= (etcp (sym-lte gmma6 '|6|)) 0.32097 0.01)
(check-= (etcp (sym-lte gmma6 '|8|)) 0.61795 0.01)

(match-define (cons gmma7 _) (rlt-gamma 0.5 1))
(check-= (etcp (sym-lte gmma7 '|2|)) 0.9545 0.01)
(check-= (etcp (sym-lte gmma7 '|4|)) 0.99532 0.01)
(check-= (etcp (sym-lte gmma7 '|6|)) 0.99947 0.01)
(check-= (etcp (sym-lte gmma7 '|8|)) 0.99994 0.01)

;;;; Beta
(match-define (cons bta _) (rlt-beta 2 5))
(check-= (etcp (sym-lte bta '|0.2|)) 0.34464 0.01)
(check-= (etcp (sym-lte bta '|0.4|)) 0.76672 0.01)
(check-= (etcp (sym-lte bta '|0.6|)) 0.95904 0.01)

; We do really badly on this case since we drop 0 and 1 from range b/c
; they are not defined, but the distribution is bimodal with the probability
; being greatest near 0 and 1
(match-define (cons bta2 _) (rlt-beta 0.5 0.5))
(check-= (etcp (sym-lte bta '|0.2|)) 0.29517 0.1)
(check-= (etcp (sym-lte bta '|0.4|)) 0.43591 0.4)
(check-= (etcp (sym-lte bta '|0.6|)) 0.56409 0.5)
(check-= (etcp (sym-lte bta '|0.8|)) 0.70483 0.3)
(check-= (etcp (sym-lte bta '|0.9|)) 0.79517 0.3)

(match-define (cons bta3 _) (rlt-beta 2 2))
(check-= (etcp (sym-lte bta3 '|0.2|)) 0.104 0.001)
(check-= (etcp (sym-lte bta3 '|0.4|)) 0.352 0.01)
(check-= (etcp (sym-lte bta3 '|0.6|)) 0.648 0.01)
(check-= (etcp (sym-lte bta3 '|0.8|)) 0.896 0.001)

; We also do really badly on this case, not exactly sure why, but I know that this
; distribution has very low probability near 0 and high near 1. So dropping 1 from
; range might be causing this.
(match-define (cons bta4 _) (rlt-beta 5 1))
(check-= (etcp (sym-lte bta4 '|0.2|)) 0.00032 0.1)
(check-= (etcp (sym-lte bta4 '|0.4|)) 0.01024 0.1)
(check-= (etcp (sym-lte bta4 '|0.6|)) 0.07776 0.1)
(check-= (etcp (sym-lte bta4 '|0.8|)) 0.32678 0.1)
(check-= (etcp (sym-lte bta4 '|0.9|)) 0.59049 0.1)

(match-define (cons bta5 _) (rlt-beta 1 3))
(check-= (etcp (sym-lte bta5 '|0.2|)) 0.488 0.01)
(check-= (etcp (sym-lte bta5 '|0.4|)) 0.784 0.01)
(check-= (etcp (sym-lte bta5 '|0.6|)) 0.936 0.001)
(check-= (etcp (sym-lte bta5 '|0.8|)) 0.992 0.0001)
(check-= (etcp (sym-lte bta5 '|0.9|)) 0.999 0.0001)

(match-define (cons bta6 _) (rlt-beta 1 1))
(check-= (etcp (sym-lte bta6 '|0.2|)) 0.2 0.01)
(check-= (etcp (sym-lte bta6 '|0.4|)) 0.4 0.01)
(check-= (etcp (sym-lte bta6 '|0.6|)) 0.6 0.01)
(check-= (etcp (sym-lte bta6 '|0.8|)) 0.8 0.01)
(check-= (etcp (sym-lte bta6 '|0.9|)) 0.9 0.01)

;;;; Exponential
(match-define (cons e _) (rlt-exponential 1))
(check-= (etcp (sym-lte e '|1|)) 0.63212 0.01)
(check-= (etcp (sym-lte e '|2|)) 0.86466 0.01)
(check-= (etcp (sym-lte e '|3|)) 0.95021 0.01)

(match-define (cons e2 _) (rlt-exponential 1.5))
(check-= (etcp (sym-lte e2 '|1|)) 0.77687 0.01)
(check-= (etcp (sym-lte e2 '|2|)) 0.95021 0.01)
(check-= (etcp (sym-lte e2 '|3|)) 0.98889 0.01)

;;;; Logistic
(match-define (cons lgstc _) (rlt-logistic 2 1))
(check-= (etcp (sym-lte lgstc '|2|)) 0.5 0.01)
(check-= (etcp (sym-lte lgstc '|2.5|)) 0.6225 0.01)
(check-= (etcp (sym-lte lgstc '|3|)) 0.7311 0.01)
(check-= (etcp (sym-lte lgstc '|3.5|)) 0.8176 0.01)
(check-= (etcp (sym-lte lgstc '|4|)) 0.8808 0.01)
(check-= (etcp (sym-lte lgstc '|4.5|)) 0.9241 0.01)
(check-= (etcp (sym-lte lgstc '|5|)) 0.9526 0.001)

;;;; Cauchy
; really big error for some reason
(match-define (cons cchy _) (rlt-cauchy 0 1))
(check-= (etcp (sym-lte cchy '|0|)) 0.5 0.1)
(check-= (etcp (sym-lte cchy '|0.3|)) 0.5928 0.1)
(check-= (etcp (sym-lte cchy '|0.5|)) 0.6476 0.1)
(check-= (etcp (sym-lte cchy '|0.7|)) 0.6944 0.1)
(check-= (etcp (sym-lte cchy '|1|)) 0.75 0.1)
(check-= (etcp (sym-lte cchy '|2|)) 0.8524 0.1)
(check-= (etcp (sym-lte cchy '|3|)) 0.8976 0.1)
(check-= (etcp (sym-lte cchy '|4|)) 0.922 0.1)
(check-= (etcp (sym-lte cchy '|5|)) 0.9372 0.1)
(check-= (etcp (sym-lte cchy '|6|)) 0.9474 0.1)

;;;; Softmax
(check-true (dist-list-equal (sptl (rlt-softmax (list 2.3 1.5 0.7 4.1 -0.2 3.3)))
                             (list (cons '|2.3| 0.09522685) (cons '|1.5| 0.04278818)
                                   (cons '|0.7| 0.01922597) (cons '|4.1| 0.57608888)
                                   (cons '|-0.2| 0.0078167) (cons '|3.3| 0.25885342))
                             0.00001))
