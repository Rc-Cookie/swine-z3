(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 3 x) (+ (exp 3 50) (exp 3 y))))
; 3^x = 3^50 + 3^y
; unsat

(check-sat)
(get-model)
