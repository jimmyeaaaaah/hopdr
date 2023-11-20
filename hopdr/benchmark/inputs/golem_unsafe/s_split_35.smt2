(set-logic HORN)
(declare-fun inv (Int Int Int Int) Bool)
(assert (forall ((w0 Int) (z0 Int) (y0 Int) (x0 Int))
  (=> (and (= x0 0) (> y0 z0) (= w0 0)) (inv x0 y0 z0 w0))))
(assert (forall ((w1 Int)
         (z1 Int)
         (y1 Int)
         (x1 Int)
         (w0 Int)
         (z0 Int)
         (x0 Int)
         (y0 Int))
  (let ((a!1 (and (inv x0 y0 z0 w0)
                  (= x1 (+ 5 x0))
                  (= y1 (+ 3 y0))
                  (= z1 (+ 1 z0))
                  (= w1 (ite (< x0 z0) (+ w0 1) (- w0 1))))))
    (=> a!1 (inv x1 y1 z1 w1)))))
(assert (forall ((w0 Int) (y0 Int) (x0 Int) (z0 Int))
  (=> (and (inv x0 y0 z0 w0) (> x0 y0) (<= w0 0)) false)))
(check-sat)
