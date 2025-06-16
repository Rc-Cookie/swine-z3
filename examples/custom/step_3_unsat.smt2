(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 3 x) (+ 1 (exp 3 y))))
; 3^x = 1 + 3^y
; unsat

(check-sat)
(get-model)
