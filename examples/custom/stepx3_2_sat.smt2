(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (=
    (+ (exp 2 x) (exp 2 y) (exp 2 z))
    (+ (exp 2 1) (exp 2 2) (exp 2 3))
))
; 2^x + 2^y + 2^z = 2^1 + 2^2 + 2^3
; sat, e.g. x=1, y=2, z=3

(check-sat)
(get-model)
