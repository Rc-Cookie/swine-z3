(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 2 x) (+ 5 (exp 2 y))))
; 2^x = 5 + 2^y
; unsat

(check-sat)
(get-model)
