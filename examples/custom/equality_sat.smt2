(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)

(assert (= (exp 2 x) 4))
; 2^x = 4
; sat, x = 2 or x = -2

(check-sat)
(get-model)
