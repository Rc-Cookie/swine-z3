(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 3 x) (* 3 (exp 3 y))))
; 3^x = 3 * 3^y
; sat, x = y + 1

(check-sat)
(get-model)
