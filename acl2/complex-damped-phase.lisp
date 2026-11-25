(in-package "ACL2")

(include-book "complex-phase-agreement")

; Identify the damped phase used in Mellin kernels with one complex
; exponential. All three Taylor evaluations and both primitive samples
; have computed positive rational precisions.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-phase-rotation lw-phase-grid lw-phase-value lw-phase-steps
                 lw-complex-phase-cap lw-complex-phase-comparison-steps
                 lw-complex-phase-comparison-amplifier lw-complex-phase-comparison-precision
                 lw-complex-exp-negative-precision lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cdp-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-cdp-real-product
         (implies (and (rationalp factor) (lw-complexp point))
                  (equal (lw-complex-mul (cons factor 0) point) (lw-complex-scale factor point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))))
(local (defthm lw-cdp-orthogonal-add
         (implies (and (rationalp a) (rationalp b))
                  (equal (lw-complex-add (cons a 0) (cons 0 b)) (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complex-add)))))
(local (defthm lw-cdp-double-negative
         (implies (rationalp value) (equal (- (- value)) value))))
(local (defthm lw-cdp-negative-cap
         (implies (and (rationalp value) (<= 0 value))
                  (equal (lw-complex-exp-cap (cons (- value) 0)) (lw-complex-exp-cap (cons value 0))))
         :hints (("Goal" :in-theory (enable lw-complex-exp-cap lw-complex-l1)))))
(local (defthm lw-cdp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cdp-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(defun lw-complex-damped-phase-budget (value angle error)
  (/ error (* 4 (+ 1 (lw-complex-exp-cap (cons value 0))
                     (lw-complex-exp-cap (cons 0 angle))))))

(defthm lw-complex-damped-phase-budget-adequate
  (implies (and (rationalp value) (<= 0 value) (rationalp angle) (rationalp error) (< 0 error))
           (and (rationalp (lw-complex-damped-phase-budget value angle error))
                (< 0 (lw-complex-damped-phase-budget value angle error))
                (<= (* (+ 3 (* 2 (lw-complex-exp-cap (cons value 0)))
                            (lw-complex-exp-cap (cons 0 angle)))
                       (lw-complex-damped-phase-budget value angle error)) error)))
  :hints (("Goal" :use ((:instance lw-complex-exp-cap-valid (point (cons value 0)))
                        (:instance lw-complex-exp-cap-valid (point (cons 0 angle)))
                        (:instance lw-positive-division-bound
                          (numerator (* (+ 3 (* 2 (lw-complex-exp-cap (cons value 0)))
                                            (lw-complex-exp-cap (cons 0 angle))) error))
                          (divisor (* 4 (+ 1 (lw-complex-exp-cap (cons value 0))
                                             (lw-complex-exp-cap (cons 0 angle))))) (bound error)))
                  :in-theory (disable lw-complex-exp-cap-valid) :nonlinearp t)))

(local (in-theory (disable lw-complex-damped-phase-budget)))

(local (defthm lw-cdp-negative-precision-bounded
         (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
                  (<= (lw-complex-exp-negative-precision value error) error))
         :hints (("Goal" :use (lw-complex-exp-negative-precision-adequate
                               (:instance lw-complex-exp-cap-valid (point (cons value 0))))
                         :in-theory (disable lw-complex-exp-negative-precision-adequate lw-complex-exp-cap-valid)
                         :nonlinearp t))))
(local (defthm lw-cdp-phase-precision-bounded
         (implies (and (rationalp value) (rationalp error) (< 0 error))
                  (<= (lw-complex-phase-comparison-precision value error) error))
         :hints (("Goal" :use (lw-complex-phase-comparison-precision-adequate
                               lw-complex-phase-comparison-amplifier-valid)
                         :in-theory (disable lw-complex-phase-comparison-precision-adequate
                                             lw-complex-phase-comparison-amplifier-valid)
                         :nonlinearp t))))


(local (defthm lw-cdp-multiply-order
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-exp-damped-phase-error
  (implies (and (rationalp value) (<= 0 value) (rationalp angle) (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-scale
                 (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value error)))
                 (lw-phase-value angle (lw-complex-phase-comparison-precision angle error)))
               (lw-complex-exp-value (cons (- value) angle) error))
             (* (+ 3 (* 2 (lw-complex-exp-cap (cons value 0))) (lw-complex-exp-cap (cons 0 angle))) error)))
  :hints (("Goal" :use (
    (:instance lw-complex-exp-cap-valid (point (cons value 0)))
    (:instance lw-complex-exp-cap-valid (point (cons 0 angle)))
    (:instance lw-complex-exp-value-cap
      (point (cons (- value) 0))
      (error (lw-complex-exp-negative-precision value error)))
    lw-complex-exp-negative-precision-adequate
    (:instance lw-complex-phase-comparison-precision-adequate (value angle))
    lw-cdp-negative-precision-bounded
    (:instance lw-cdp-phase-precision-bounded (value angle))
    (:instance lw-cdp-multiply-order
      (left (lw-complex-exp-negative-precision value error))
      (right error)
      (factor (lw-complex-exp-cap (cons 0 angle))))
    (:instance lw-cdp-multiply-order
      (left (lw-complex-phase-comparison-precision angle error))
      (right error)
      (factor (lw-complex-exp-cap (cons value 0))))
    (:instance lw-exp-neg-bounds-valid (epsilon (lw-complex-exp-negative-precision value error)))
    lw-complex-exp-computed-negative-agreement
    (:instance lw-complex-exp-computed-phase-agreement (value angle))
    (:instance lw-complex-difference-symmetric
      (left (lw-complex-exp-value (cons (- value) 0) (lw-complex-exp-negative-precision value error)))
      (right (cons (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value error))) 0))
      (radius error))
    (:instance lw-complex-difference-symmetric
      (left (lw-complex-exp-value (cons 0 angle) (lw-complex-phase-comparison-precision angle error)))
      (right (lw-phase-value angle (lw-complex-phase-comparison-precision angle error)))
      (radius error))
    (:instance lw-complex-mul-difference-bound
      (a (cons (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value error))) 0))
      (b (lw-phase-value angle (lw-complex-phase-comparison-precision angle error)))
      (c (lw-complex-exp-value (cons (- value) 0) (lw-complex-exp-negative-precision value error)))
      (d (lw-complex-exp-value (cons 0 angle) (lw-complex-phase-comparison-precision angle error)))
      (left-cap (lw-complex-exp-cap (cons value 0)))
      (right-cap 1)
      (left-error error)
      (right-error error))
    (:instance lw-complex-exp-value-multiplication
      (left (cons (- value) 0))
      (right (cons 0 angle))
      (left-error (lw-complex-exp-negative-precision value error))
      (right-error (lw-complex-phase-comparison-precision angle error))
      (sum-error error))
    (:instance lw-complex-difference-triangle
      (left
        (lw-complex-scale
          (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value error)))
          (lw-phase-value angle (lw-complex-phase-comparison-precision angle error))))
      (middle
        (lw-complex-mul
          (lw-complex-exp-value (cons (- value) 0) (lw-complex-exp-negative-precision value error))
          (lw-complex-exp-value (cons 0 angle) (lw-complex-phase-comparison-precision angle error))))
      (right (lw-complex-exp-value (cons (- value) angle) error))
      (radius (+ error (* (lw-complex-exp-cap (cons value 0)) error)))
      (other-radius
        (+
          (* (lw-complex-exp-cap (cons 0 angle)) (lw-complex-exp-negative-precision value error))
          (* (lw-complex-exp-cap (cons value 0)) (lw-complex-phase-comparison-precision angle error))
          (* 2 error))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-scale
            (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value error)))
            (lw-phase-value angle (lw-complex-phase-comparison-precision angle error)))
          (lw-complex-exp-value (cons (- value) angle) error)))
      (radius
        (+
          (+ error (* (lw-complex-exp-cap (cons value 0)) error))
          (+
            (* (lw-complex-exp-cap (cons 0 angle)) (lw-complex-exp-negative-precision value error))
            (* (lw-complex-exp-cap (cons value 0)) (lw-complex-phase-comparison-precision angle error))
            (* 2 error))))
      (cap (* (+ 3 (* 2 (lw-complex-exp-cap (cons value 0))) (lw-complex-exp-cap (cons 0 angle))) error))))
    :in-theory (e/d (lw-intervalp)
                    (lw-complex-exp-cap-valid lw-complex-exp-negative-precision-adequate
                     lw-complex-phase-comparison-precision-adequate lw-cdp-negative-precision-bounded
                     lw-cdp-phase-precision-bounded lw-exp-neg-bounds-valid
                     lw-complex-exp-computed-negative-agreement lw-complex-exp-computed-phase-agreement
                     lw-complex-mul-difference-bound lw-complex-exp-value-multiplication
                     lw-complex-difference-triangle))
    :nonlinearp t)))

(defun lw-complex-damped-phase-value (value angle error)
  (let ((budget (lw-complex-damped-phase-budget value angle error)))
    (lw-complex-scale
     (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value budget)))
     (lw-phase-value angle (lw-complex-phase-comparison-precision angle budget)))))

(defthm lw-complex-damped-phase-value-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp angle) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-damped-phase-value value angle error)))
  :hints (("Goal" :use (lw-complex-damped-phase-budget-adequate
                        (:instance lw-complex-exp-negative-precision-adequate
                          (error (lw-complex-damped-phase-budget value angle error)))
                        (:instance lw-exp-neg-bounds-valid
                          (epsilon
                            (lw-complex-exp-negative-precision
                              value
                              (lw-complex-damped-phase-budget value angle error)))))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-complex-damped-phase-budget-adequate
                                   lw-complex-exp-negative-precision-adequate lw-exp-neg-bounds-valid)))))

(defthm lw-complex-exp-computed-damped-phase-agreement
  (implies (and (rationalp value) (<= 0 value) (rationalp angle) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-damped-phase-value value angle error)
                            (lw-complex-exp-value (cons (- value) angle)
                                                 (lw-complex-damped-phase-budget value angle error)))
            error))
  :hints (("Goal" :use (lw-complex-damped-phase-budget-adequate
                        (:instance lw-complex-exp-damped-phase-error
                          (error (lw-complex-damped-phase-budget value angle error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-complex-damped-phase-value value angle error)
                                                (lw-complex-exp-value (cons (- value) angle)
                                                                     (lw-complex-damped-phase-budget
                                                                       value
                                                                       angle
                                                                       error))))
                          (radius
                            (*
                              (+
                                3
                                (* 2 (lw-complex-exp-cap (cons value 0)))
                                (lw-complex-exp-cap (cons 0 angle)))
                              (lw-complex-damped-phase-budget value angle error)))
                          (cap error)))
                  :in-theory (disable lw-complex-damped-phase-budget-adequate
                                      lw-complex-exp-damped-phase-error))))

