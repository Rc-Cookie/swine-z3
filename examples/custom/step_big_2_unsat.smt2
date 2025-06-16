(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 2 x) (+ (exp 2 50) 1 (exp 2 y))))
; 2^x = 2^50 + 1 + 2^y
; unsat

(check-sat)
(get-model)
