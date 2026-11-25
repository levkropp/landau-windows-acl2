(in-package "ACL2")

(include-book "mellin-shift-coefficients")
(include-book "mellin-dyadic-cells")
(include-book "mellin-integral")

; Use precisely the cutoff and depth of the default improper evaluator.
; A finite polynomial boundary check then controls its computed moment.
; The uniform comparison at shifted improper arguments is a separate step.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-mellin-sample lw-mellin-sample-kernel-form lw-log-signal-bounds
                 lw-mellin-integral lw-mellin-integral-cutoff lw-mellin-bounded-integral
                 lw-mellin-integral-depth lw-mellin-integral-precision lw-mellin-dyadic-cells
                 lw-mellin-cell-mass lw-mellin-weighted-sum-raw lw-halved-width
                 lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                 lw-mellin-signal-spatial-slope lw-mellin-signal-spatial-cap
                 lw-kernel-spatial-slope lw-kernel-spatial-cap lw-exp-lipschitz-cap
                 lw-mellin-sum lw-mellin-sum-raw lw-mellin-sum-error
                 lw-mellin-shift-polynomial lw-mellin-shift-polynomial-degree
                 lw-mellin-shift-polynomial-nodes lw-mellin-shift-mixture-nodes
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-orbit-rotation
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mip-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mip-half-quarter
         (implies (rationalp value) (equal (* 1/2 1/4 value) (* 1/8 value)))
         :hints (("Goal" :use ((:instance associativity-of-* (x 1/2) (y 1/4) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mip-left-commutes)))))
(local (defthm lw-mip-quarter-eighth
         (implies (rationalp value) (equal (* 1/4 1/8 value) (* 1/32 value)))
         :hints (("Goal" :use ((:instance associativity-of-* (x 1/4) (y 1/8) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mip-left-commutes)))))

(defun lw-mellin-integral-cells (sigma height target error)
  (let ((cutoff (lw-mellin-integral-cutoff sigma target error)))
    (lw-mellin-dyadic-cells 0 cutoff
                           (lw-mellin-integral-depth cutoff sigma height (* 1/2 error)))))

(defthm lw-mellin-integral-cells-valid
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp target)
                (rationalp error) (< 0 error))
           (lw-mellin-cellsp (lw-mellin-integral-cells sigma height target error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-integral-cutoff-valid (index target))
    (:instance lw-mellin-integral-depth-adequate
      (cap (lw-mellin-integral-cutoff sigma target error))
      (error (* 1/2 error)))
    (:instance lw-mellin-dyadic-cells-valid
      (start 0)
      (end (lw-mellin-integral-cutoff sigma target error))
      (depth
        (lw-mellin-integral-depth (lw-mellin-integral-cutoff sigma target error) sigma height (* 1/2 error)))))
    :in-theory (disable lw-mellin-integral-cutoff-valid lw-mellin-integral-depth-adequate))))

(local (in-theory (disable lw-mellin-integral-cells)))

(defthm lw-mellin-integral-cell-comparison
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp target)
                (rationalp error) (< 0 error) (rationalp grid-error) (< 0 grid-error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-mellin-sum (lw-mellin-integral-cells sigma height target error) sigma height target grid-error)
             (lw-mellin-integral sigma height target error))
            (+ grid-error (* 1/8 error))))
  :hints (("Goal" :use (
    (:instance lw-mellin-integral-cutoff-valid (index target))
    (:instance lw-mellin-canonical-cell-bounded-comparison
      (cap (lw-mellin-integral-cutoff sigma target error))
      (index target)
      (left-error grid-error)
      (right-error (* 1/2 error))))
    :in-theory (e/d (lw-mellin-integral-cells lw-mellin-integral)
                    (lw-mellin-integral-cutoff-valid lw-mellin-canonical-cell-bounded-comparison)))))

(defun lw-mellin-integral-polynomial (sigma height target radius error)
  (lw-mellin-shift-polynomial (lw-mellin-integral-cells sigma height target error)
                              sigma height target radius (* 1/4 error)))
(defun lw-mellin-integral-polynomial-degree (sigma height target radius error)
  (lw-mellin-shift-polynomial-degree (lw-mellin-integral-cells sigma height target error)
                                     sigma height target radius (* 1/4 error)))

(defthm lw-mellin-integral-polynomial-valid
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp target)
                (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (and (lw-complex-coefficientsp (lw-mellin-integral-polynomial sigma height target radius error))
                (< target (len (lw-mellin-integral-polynomial sigma height target radius error)))
                (natp (lw-mellin-integral-polynomial-degree sigma height target radius error))
                (<= target (lw-mellin-integral-polynomial-degree sigma height target radius error))))
  :hints (("Goal" :use (
    (:instance lw-mellin-shift-polynomial-valid
      (cells (lw-mellin-integral-cells sigma height target error))
      (error (* 1/4 error)))
    (:instance lw-mellin-shift-polynomial-degree-data
      (cells (lw-mellin-integral-cells sigma height target error))
      (error (* 1/4 error))))
    :in-theory (disable lw-mellin-shift-polynomial-valid lw-mellin-shift-polynomial-degree-data))))

(local (in-theory (disable lw-mellin-integral-polynomial lw-mellin-integral-polynomial-degree)))

(defthm lw-mellin-integral-polynomial-cauchy-bound
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp target)
                (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error)
                (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check (lw-mellin-integral-polynomial sigma height target radius error) (lw-cauchy-orbit-rotation (lw-mellin-integral-polynomial-degree sigma height target radius error)) 0
                  (lw-cauchy-coefficient-count (lw-mellin-integral-polynomial sigma height target radius error) (lw-mellin-integral-polynomial-degree sigma height target radius error) (* 1/8 error)) cap))
           (lw-complex-diskp (lw-mellin-integral sigma height target error) (+ cap error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-shift-polynomial-cauchy-bound
      (cells (lw-mellin-integral-cells sigma height target error))
      (error (* 1/4 error)))
    (:instance lw-mellin-integral-cell-comparison (grid-error (* 1/32 error)))
    (:instance lw-complex-difference-symmetric
      (left
        (lw-mellin-sum
          (lw-mellin-integral-cells sigma height target error)
          sigma
          height
          target
          (* 1/32 error)))
      (right (lw-mellin-integral sigma height target error))
      (radius (+ (* 1/32 error) (* 1/8 error))))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-integral sigma height target error))
      (middle
        (lw-mellin-sum
          (lw-mellin-integral-cells sigma height target error)
          sigma
          height
          target
          (* 1/32 error)))
      (right (cons 0 0))
      (radius (+ (* 1/32 error) (* 1/8 error)))
      (other-radius (+ cap (* 1/4 error))))
    (:instance lw-complex-disk-enlarge
      (point (lw-mellin-integral sigma height target error))
      (radius (+ (* 1/32 error) (* 1/8 error) cap (* 1/4 error)))
      (cap (+ cap error))))
    :in-theory (e/d (lw-mellin-integral-polynomial lw-mellin-integral-polynomial-degree)
                    (lw-mellin-shift-polynomial-cauchy-bound lw-mellin-integral-cell-comparison
                     lw-complex-difference-triangle)))))

