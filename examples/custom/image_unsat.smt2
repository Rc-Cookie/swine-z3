(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (<=
    (exp 2 x)
    0
))
; 2^x <= 0
; unsat

(check-sat)
(get-model)
