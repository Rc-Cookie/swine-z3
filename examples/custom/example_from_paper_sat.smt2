(set-logic ALL)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (< (- (- (* 3 (exp 2 x)) (* 5 (exp 2 y))) z) 0))
(assert (> (exp 2 z) 10))
; (assert (< (+ (exp 2 x) (exp 2 y) z) 0))
; 3*2^x - 5*2^y - z < 0
; sat

(check-sat)
(get-model)
