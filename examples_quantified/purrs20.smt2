; parametric
; Here a != 0
; x(n) = a * x(n-1)
; Solution: x(n) = a^n * x(0)

(set-logic ALL)
(set-option :produce-models true)
(declare-fun x0 () Int)
(declare-fun n () Int)
(declare-fun a () Int)

(declare-fun iexp (Int Int) Int)
(assert (forall ((b Int)) (= (iexp b 0) 1)))
(assert (forall ((b Int) (e Int)) (=> (> e 0) (= (iexp b e) (* b (iexp b (- e 1)))))))
(assert (forall ((b Int) (e Int)) (=> (< e 0) (= (iexp b e) (iexp b (- e))))))

(assert (> n 0))
(assert (distinct a 0))
(assert (distinct
  (* (iexp a n) x0)
  (* a (* (iexp a (- n 1)) x0))
))

(check-sat)