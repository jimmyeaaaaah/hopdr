(set-logic HORN)
(declare-fun inv (Int Int Int) Bool)
(assert (forall ((z0 Int) (y0 Int) (x0 Int))
  (=> (and (= x0 0) (= y0 200) (= z0 400)) (inv x0 y0 z0))))
(assert (forall ((z1 Int) (y1 Int) (x1 Int) (z0 Int) (x0 Int) (y0 Int))
  (let ((a!1 (and (inv x0 y0 z0)
                  (= x1 (+ 1 x0))
                  (= y1 (ite (< x0 200) (+ y0 1) y0))
                  (= z1 (ite (< x0 200) z0 (+ z0 2))))))
    (=> a!1 (inv x1 y1 z1)))))
(assert (forall ((x0 Int) (z0 Int) (y0 Int))
  (let ((a!1 (and (inv x0 y0 z0) (>= y0 400) (not (= z0 (* 2 x0))))))
    (=> a!1 false))))
(check-sat)
