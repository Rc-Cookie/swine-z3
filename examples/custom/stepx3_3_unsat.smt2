(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (=
    (+ (exp 3 x) (exp 3 y) (exp 3 z))
    (+ (exp 3 1) (exp 3 2) (exp 3 3) 1)
))
; 3^x + 3^y + 3^z = 3^1 + 3^2 + 3^3 + 5
; unsat

(check-sat)
(get-model)
