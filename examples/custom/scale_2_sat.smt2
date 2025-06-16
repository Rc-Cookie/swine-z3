(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 2 x) (* 2 (exp 2 y))))
; 2^x = 2 * 2^y
; sat, x = y + 1

(check-sat)
(get-model)
