(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 3 x) (+ (* 2 (exp 3 50)) (exp 3 y))))
; 3^x = 2 * 3^50 + 3^y
; sat, e.g. x = 3^51, y = 3^50

(check-sat)
(get-model)
