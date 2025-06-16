(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (not (= x y)))
(assert (= (exp 2 x) (exp 2 y)))
; x != y /\ 2^|x| = 2^|y|
; sat, x = -y != 0

(check-sat)
(get-model)
