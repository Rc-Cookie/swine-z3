(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (not (= x y)))
(assert (not (= x (- y))))
(assert (= (exp 2 x) (exp 2 y)))
; |x| != |y| /\ 2^|x| = 2^|y|
; unsat

(check-sat)
(get-model)
