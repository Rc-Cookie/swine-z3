(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 2 x) (+ (exp 2 50) (exp 2 y))))
; 2^x = 2^50 + 2^y
; sat, e.g. x = 2^51, y = 2^50

(check-sat)
(get-model)
