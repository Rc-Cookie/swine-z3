(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (exp 2 x) (+ 1 (exp 2 y))))
; 2^x = 1 + 2^y
; sat, x=1, y=0 or x=-1, y=0

(check-sat)
(get-model)
