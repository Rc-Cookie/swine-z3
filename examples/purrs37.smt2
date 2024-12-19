; x(n) = x(n-1)+4*x(n-2)-4*x(n-3)+6
; Solution: x(n) = -4/3 + 3/2*2^n - 1/6*(-2)^n + (4/3-1/2*2^n+1/6*(-2)^n)*x(0) + (1/4*2^n-1/4*(-2)^n)*x(1) + (-1/3+1/4*2^n+1/12*(-2)^n)*x(2) - 2*n

(set-logic ALL)
(set-option :produce-models true)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun n () Int)

(assert (> n 2))
(assert (distinct
  (+
    (- (/ 4 3))
    (* (/ 3 2) (exp 2 n))
    (- (* (/ 1 6) (exp (- 2) n)))
    (*
      (+ (/ 4 3) (- (* (/ 1 2) (exp 2 n))) (* (/ 1 6) (exp (- 2) n)))
      x0
    )
    (*
      (- (* (/ 1 4) (exp 2 n)) (* (/ 1 4) (exp (- 2) n)))
      x1
    )
    (*
      (+ (- (/ 1 3)) (* (/ 1 4) (exp 2 n)) (* (/ 1 12) (exp (- 2) n)))
      x2
    )
    (- (* 2 n))
  )
  (+
      (+
      (- (/ 4 3))
      (* (/ 3 2) (exp 2 (- n 1)))
      (- (* (/ 1 6) (exp (- 2) (- n 1))))
      (*
        (+ (/ 4 3) (- (* (/ 1 2) (exp 2 (- n 1)))) (* (/ 1 6) (exp (- 2) (- n 1))))
        x0
      )
      (*
        (- (* (/ 1 4) (exp 2 (- n 1))) (* (/ 1 4) (exp (- 2) (- n 1))))
        x1
      )
      (*
        (+ (- (/ 1 3)) (* (/ 1 4) (exp 2 (- n 1))) (* (/ 1 12) (exp (- 2) (- n 1))))
        x2
      )
      (- (* 2 (- n 1)))
    )
    (* 4 (+
      (- (/ 4 3))
      (* (/ 3 2) (exp 2 (- n 2)))
      (- (* (/ 1 6) (exp (- 2) (- n 2))))
      (*
        (+ (/ 4 3) (- (* (/ 1 2) (exp 2 (- n 2)))) (* (/ 1 6) (exp (- 2) (- n 2))))
        x0
      )
      (*
        (- (* (/ 1 4) (exp 2 (- n 2))) (* (/ 1 4) (exp (- 2) (- n 2))))
        x1
      )
      (*
        (+ (- (/ 1 3)) (* (/ 1 4) (exp 2 (- n 2))) (* (/ 1 12) (exp (- 2) (- n 2))))
        x2
      )
      (- (* 2 (- n 2)))
    ))
    (- (* 4 (+
      (- (/ 4 3))
      (* (/ 3 2) (exp 2 (- n 3)))
      (- (* (/ 1 6) (exp (- 2) (- n 3))))
      (*
        (+ (/ 4 3) (- (* (/ 1 2) (exp 2 (- n 3)))) (* (/ 1 6) (exp (- 2) (- n 3))))
        x0
      )
      (*
        (- (* (/ 1 4) (exp 2 (- n 3))) (* (/ 1 4) (exp (- 2) (- n 3))))
        x1
      )
      (*
        (+ (- (/ 1 3)) (* (/ 1 4) (exp 2 (- n 3))) (* (/ 1 12) (exp (- 2) (- n 3))))
        x2
      )
      (- (* 2 (- n 3)))
    )))
    6
  )
))

(check-sat)