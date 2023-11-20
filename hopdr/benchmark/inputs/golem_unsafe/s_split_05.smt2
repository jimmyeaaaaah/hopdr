(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(assert (forall ((z0 Int) (y0 Int) (x0 Int))
  (=> (and (> x0 0) (< y0 0) (= z0 1)) (inv x0 y0 z0))))
(assert (forall ((z1 Int) (y1 Int) (x1 Int) (z0 Int) (y0 Int) (x0 Int))
  (let ((a!1 (and (inv x0 y0 z0)
                  (= x1 (+ x0 1))
                  (= y1 (+ y0 2))
                  (= z1 (ite (>= y0 0) (* z0 2) z0)))))
    (=> a!1 (inv x1 y1 z1)))))
(assert (forall ((z0 Int) (x0 Int) (y0 Int))
  (=> (and (inv x0 y0 z0) (>= y0 x0) (> z0 1)) false)))
(check-sat)