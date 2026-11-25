(in-package "ACL2")

(include-book "mellin-partitions")
(include-book "mellin-tail-bounds")

; An explicit cutoff and bounded quadrature for the improper transform.
; The tail coefficient is derived from quadratic Gz growth and the shifted
; rate sigma-2. Lean proves their analytic interpretation; the arithmetic
; coefficient/window and pole estimates still have to be composed.
(defun lw-mellin-integral-cutoff (sigma index error)
  (lw-mellin-tail-cutoff (- sigma 2) index 4 error))
(defun lw-mellin-integral (sigma height index error)
  (lw-mellin-bounded-integral (lw-mellin-integral-cutoff sigma index error)
                             sigma height index (/ error 2)))
(defun lw-mellin-integral-check (sigma height index error)
  (let ((cutoff (lw-mellin-integral-cutoff sigma index error)))
    (and (< 0 cutoff)
         (<= (lw-mellin-tail-radius (- sigma 2) index 4 cutoff) (/ error 2))
         (lw-mellin-dyadic-check 0 cutoff (lw-mellin-integral-depth cutoff sigma height (/ error 2))
                                 sigma index (lw-mellin-integral-precision cutoff (/ error 2))))))

(local (in-theory
        (disable lw-mellin-tail-cutoff lw-mellin-tail-radius lw-mellin-tail-coefficient
                 lw-mellin-tail-cutoff-adequate lw-mellin-tail-radius-budget
                 lw-mellin-bounded-integral lw-mellin-bounded-integral-rational
                 lw-mellin-dyadic-check lw-mellin-integral-depth lw-mellin-integral-precision
                 lw-mellin-bounded-integral-constructor-check)))

(defthm lw-mellin-integral-cutoff-valid
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-integral-cutoff sigma index error))
                (< 0 (lw-mellin-integral-cutoff sigma index error))
                (<= (+ 2 (nfix index)) (* (- sigma 2) (lw-mellin-integral-cutoff sigma index error)))))
  :hints (("Goal" :use ((:instance lw-mellin-tail-cutoff-adequate (rate (- sigma 2)) (mass 4))))))

(defthm lw-mellin-integral-tail-budget
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp error) (< 0 error))
           (<= (lw-mellin-tail-radius (- sigma 2) index 4 (lw-mellin-integral-cutoff sigma index error)) (/ error 2)))
  :hints (("Goal" :use ((:instance lw-mellin-tail-radius-budget (rate (- sigma 2)) (mass 4))))))

(defthm lw-mellin-integral-constructor-check
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (rationalp error) (< 0 error))
           (lw-mellin-integral-check sigma height index error))
  :hints (("Goal" :use (lw-mellin-integral-cutoff-valid lw-mellin-integral-tail-budget
                        (:instance lw-mellin-bounded-integral-constructor-check
                          (cap (lw-mellin-integral-cutoff sigma index error)) (error (/ error 2))))
                  :in-theory (disable lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid
                                      lw-mellin-integral-tail-budget))))

(defthm lw-mellin-integral-rational
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-integral sigma height index error)))
  :hints (("Goal" :use (lw-mellin-integral-cutoff-valid
                        (:instance lw-mellin-bounded-integral-rational
                          (cap (lw-mellin-integral-cutoff sigma index error)) (error (/ error 2))))
                  :in-theory (disable lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid lw-complexp))))

(defthm lw-mellin-integral-error-budget
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (rationalp error) (< 0 error))
           (let ((cutoff (lw-mellin-integral-cutoff sigma index error)))
             (<= (+ (lw-mellin-tail-radius (- sigma 2) index 4 cutoff)
                    (* cutoff (lw-mellin-spatial-slope cutoff sigma height 1)
                       (lw-halved-width cutoff (lw-mellin-integral-depth cutoff sigma height (/ error 2))))
                    (* cutoff (lw-mellin-spatial-error-factor cutoff 1)
                       (lw-mellin-integral-precision cutoff (/ error 2)))) error)))
  :hints (("Goal" :use (lw-mellin-integral-cutoff-valid lw-mellin-integral-tail-budget
                        (:instance lw-mellin-integral-depth-adequate
                          (cap (lw-mellin-integral-cutoff sigma index error)) (error (/ error 2)))
                        (:instance lw-mellin-integral-precision-valid
                          (cap (lw-mellin-integral-cutoff sigma index error)) (error (/ error 2))))
                  :in-theory (disable lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid
                                      lw-mellin-integral-tail-budget lw-mellin-integral-depth-adequate
                                      lw-mellin-integral-precision-valid lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                                      lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope lw-halved-width))))
