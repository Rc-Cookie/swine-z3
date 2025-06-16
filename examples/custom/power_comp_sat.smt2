(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (< (- (exp 2 x) (exp 2 y)) 0))
; 2^x - 2^y < 0
; sat

(check-sat)
(get-model)
