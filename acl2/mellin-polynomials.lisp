(in-package "ACL2")

(include-book "exp-mixture-bounds")
(include-book "cauchy-extraction")
(include-book "mellin-taylor-grid")

; Freeze the target moment's node precision, then build every coefficient
; of one genuine polynomial from those same zeroth-moment samples.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-mellin-sample lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-error-budgets lw-log-signal-bounds lw-kernel-weight-bounds
                 lw-phase-value lw-kernel-weight-scale lw-exp-term
                 lw-mellin-moment-precision lw-mellin-moment-error-factor lw-mellin-moment-pair-error
                 lw-mellin-sum-raw lw-mellin-sum lw-mellin-sum-error
                 lw-mellin-node-taylor-coefficient lw-mellin-taylor-sum-raw lw-mellin-taylor-coefficient
                 lw-exp-mixture-coefficient lw-exp-mixture-coefficients lw-exp-mixture-taylor-value
                 lw-complex-exp-sum lw-complex-exp-term lw-complex-polynomial
                 lw-cauchy-coefficient-count lw-cauchy-coefficient-precision lw-cauchy-boundary-check
                 lw-cauchy-orbit-rotation lw-phase-rotation lw-phase-denominator
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(defun lw-mellin-taylor-nodes (cells sigma height target budget)
  (if (consp cells)
      (cons (cons (caar cells)
                  (lw-mellin-sample
                   (caar cells) sigma height 0 (cdar cells)
                   (lw-mellin-moment-precision (caar cells) target (cdar cells) budget)))
            (lw-mellin-taylor-nodes (cdr cells) sigma height target budget))
    nil))

(defthm lw-mellin-taylor-nodes-valid
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp budget) (< 0 budget))
           (and (lw-exp-mixturep (lw-mellin-taylor-nodes cells sigma height target budget))
                (equal (len (lw-mellin-taylor-nodes cells sigma height target budget)) (len cells))))
  :hints (("Goal" :induct (lw-mellin-cellsp cells))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-moment-precision-adequate
                          (value (caar cells)) (index target) (step (cdar cells)) (error budget)))
                 :in-theory (disable lw-mellin-moment-precision-adequate)))))

(defthm lw-mellin-taylor-nodes-target-coefficient
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp budget) (< 0 budget))
           (equal (lw-exp-mixture-coefficient (lw-mellin-taylor-nodes cells sigma height target budget) target)
                  (lw-mellin-taylor-sum-raw cells sigma height target budget)))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (enable lw-exp-mixture-coefficient lw-mellin-taylor-sum-raw
                                     lw-mellin-node-taylor-coefficient))))

(defun lw-mellin-taylor-bases (cells sigma height target error)
  (lw-mellin-taylor-nodes cells sigma height target (lw-mellin-sum-error cells (/ error 4))))

(defthm lw-mellin-taylor-bases-valid
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp error) (< 0 error))
           (and (lw-exp-mixturep (lw-mellin-taylor-bases cells sigma height target error))
                (equal (len (lw-mellin-taylor-bases cells sigma height target error)) (len cells))))
  :hints (("Goal" :use ((:instance lw-mellin-sum-error-positive (error (/ error 4))))
                  :in-theory (disable lw-mellin-sum-error-positive))))

(defun lw-mellin-taylor-polynomial (cells sigma height target degree error)
  (lw-exp-mixture-coefficients (lw-mellin-taylor-bases cells sigma height target error) 0 (+ 1 (nfix degree))))

(defthm lw-mellin-taylor-polynomial-valid
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (natp degree) (rationalp error) (< 0 error))
           (and (lw-complex-coefficientsp (lw-mellin-taylor-polynomial cells sigma height target degree error))
                (equal (len (lw-mellin-taylor-polynomial cells sigma height target degree error)) (+ 1 degree))))
  :hints (("Goal" :use ((:instance lw-mellin-sum-error-positive (error (/ error 4))))
                  :in-theory (disable lw-mellin-sum-error-positive))))

(defthm lw-mellin-taylor-polynomial-target
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (natp degree) (<= target degree) (rationalp error) (< 0 error))
           (equal (nth target (lw-mellin-taylor-polynomial cells sigma height target degree error))
                  (lw-mellin-taylor-coefficient cells sigma height target error)))
  :hints (("Goal" :use ((:instance lw-mellin-sum-error-positive (error (/ error 4))))
                  :in-theory (e/d (lw-mellin-taylor-coefficient)
                                  (lw-mellin-sum-error-positive)))))

(defthm lw-mellin-taylor-polynomial-evaluation
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (natp degree) (rationalp error) (< 0 error) (lw-complexp point))
           (equal (lw-complex-polynomial
                   (lw-mellin-taylor-polynomial cells sigma height target degree error) point 0)
                  (lw-exp-mixture-taylor-value
                   (lw-mellin-taylor-nodes cells sigma height target (lw-mellin-sum-error cells (/ error 4)))
                   point degree)))
  :hints (("Goal" :use ((:instance lw-mellin-sum-error-positive (error (/ error 4))))
                  :in-theory (disable lw-mellin-sum-error-positive))))

(local (in-theory (disable lw-mellin-taylor-polynomial lw-mellin-taylor-nodes)))

(defthm lw-mellin-finite-polynomial-cauchy-bound
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (natp degree) (<= target degree)
                (rationalp error) (< 0 error) (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check
                 (lw-mellin-taylor-polynomial cells sigma height target degree (/ error 2))
                 (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count
                  (lw-mellin-taylor-polynomial cells sigma height target degree (/ error 2))
                  degree (/ error 2)) cap))
           (lw-complex-diskp (lw-mellin-sum cells sigma height target (/ error 4)) (+ cap error)))
  :hints (("Goal" :use ((:instance lw-mellin-taylor-polynomial-valid (error (/ error 2)))
                        (:instance lw-mellin-taylor-polynomial-target (error (/ error 2)))
                        (:instance lw-cauchy-finite-coefficient-bound
                          (coefficients (lw-mellin-taylor-polynomial cells sigma height target degree (/ error 2)))
                          (error (/ error 2)))
                        (:instance lw-mellin-computed-quadrature-taylor-coefficient (index target) (error (/ error 2)))
                        (:instance lw-complex-difference-triangle
                          (left (lw-mellin-sum cells sigma height target (/ error 4)))
                          (middle (lw-mellin-taylor-coefficient cells sigma height target (/ error 2)))
                          (right (cons 0 0)) (radius (/ error 2)) (other-radius (+ cap (/ error 2))))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-mellin-sum cells sigma height target (/ error 4)))
                          (radius (+ (/ error 2) cap (/ error 2))) (cap (+ cap error))))
                  :in-theory (disable lw-mellin-taylor-polynomial-valid lw-mellin-taylor-polynomial-target
                                      lw-cauchy-finite-coefficient-bound
                                      lw-mellin-computed-quadrature-taylor-coefficient
                                      lw-complex-difference-triangle))))

(defun lw-mellin-taylor-degree (cells sigma height target radius error)
  (lw-exp-mixture-degree (lw-mellin-taylor-bases cells sigma height target error) radius target error))

(defun lw-mellin-taylor-mixture-value (cells sigma height target point error)
  (let ((nodes (lw-mellin-taylor-bases cells sigma height target error)))
    (lw-exp-mixture-value nodes point (lw-exp-mixture-budget nodes error))))

(local (in-theory (disable lw-mellin-taylor-bases)))

(defthm lw-mellin-taylor-degree-data
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (and (natp (lw-mellin-taylor-degree cells sigma height target radius error))
                (<= target (lw-mellin-taylor-degree cells sigma height target radius error))))
  :hints (("Goal" :use ((:instance lw-exp-mixture-degree-data
                          (nodes (lw-mellin-taylor-bases cells sigma height target error))))
                  :in-theory (disable lw-exp-mixture-degree-data))))

(defthm lw-mellin-taylor-mixture-value-rational
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (lw-complexp point) (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-taylor-mixture-value cells sigma height target point error))))

(defthm lw-mellin-computed-uniform-taylor-polynomial
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (lw-complex-diskp point radius) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-polynomial
              (lw-mellin-taylor-polynomial
               cells sigma height target (lw-mellin-taylor-degree cells sigma height target radius error) error)
              point 0)
             (lw-mellin-taylor-mixture-value cells sigma height target point error))
            error))
  :hints (("Goal" :use ((:instance lw-exp-mixture-computed-uniform-polynomial
                          (nodes (lw-mellin-taylor-bases cells sigma height target error))))
                  :in-theory (e/d (lw-mellin-taylor-polynomial)
                                  (lw-exp-mixture-computed-uniform-polynomial
                                   lw-mellin-taylor-polynomial-evaluation
                                   lw-exp-mixture-degree lw-exp-mixture-degree-raw
                                   lw-exp-mixture-budget lw-exp-mixture-value))
                  :do-not-induct t)))

; The mixture value above still needs to be identified with the existing
; Mellin evaluator at shifted sigma/height. This theorem is a finite
; polynomial approximation to computed node amplitudes, not that identity.
