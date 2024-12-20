; x(n) = 3 * x(n-1) + 2
; Solution: x(n) = 3^n * x(0) + 3^n - 1

(set-logic ALL)
(set-option :produce-models true)
(declare-fun x0 () Int)
(declare-fun n () Int)

(declare-fun iexp (Int Int) Int)
(assert (forall ((b Int)) (= (iexp b 0) 1)))
(assert (forall ((b Int) (e Int)) (=> (> e 0) (= (iexp b e) (* b (iexp b (- e 1)))))))
(assert (forall ((b Int) (e Int)) (=> (< e 0) (= (iexp b e) (* b (iexp b (+ e 1)))))))

(assert (> n 0))
(assert (distinct
  (+ (* (iexp 3 n) x0) (iexp 3 n) (- 1))
  (+ (* 3 (+ (* (iexp 3 (- n 1)) x0) (iexp 3 (- n 1)) (- 1))) 2)
))

(check-sat)