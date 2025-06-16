(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)

(assert (= (exp 2 x) 3))
; 2^x = 3
; unsat

(check-sat)
(get-model)
