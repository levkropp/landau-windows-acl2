(in-package "ACL2")

(include-book "complex-damped-phase")
(include-book "complex-disk-gap")
(include-book "exp-continuity")

; Independent precisions for the actual reciprocal and phase primitives.
; The auxiliary comparison precision is explicit and will be eliminated
; by a rational disk-gap argument, not by an analytic limit assumption.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-neg-bounds-overlap
                 lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-phase-rotation lw-phase-grid lw-phase-value lw-phase-steps
                 lw-complex-phase-cap lw-complex-phase-comparison-steps
                 lw-complex-phase-comparison-amplifier lw-complex-phase-comparison-precision
                 lw-complex-exp-negative-precision lw-complex-damped-phase-budget
                 lw-complex-norm-square lw-disk-gap-error
                 lw-complex-damped-phase-value lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cka-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-cka-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cka-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cka-double-negative
         (implies (rationalp value) (equal (- (- value)) value))))
(local (defthm lw-cka-real-product
         (implies (and (rationalp factor) (lw-complexp point))
                  (equal (lw-complex-mul (cons factor 0) point) (lw-complex-scale factor point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))))
(local (defthm lw-cka-real-difference-disk
         (implies (and (rationalp a) (rationalp b) (rationalp error) (<= (abs (- a b)) error))
                  (lw-complex-diskp (lw-complex-sub (cons a 0) (cons b 0)) error))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complex-sub lw-complexp lw-diskp)
                         :cases ((<= a b)) :nonlinearp t))
         :rule-classes nil))
(local (defthm lw-cka-real-unit
         (implies (and (rationalp value) (<= 0 value) (<= value 1))
                  (lw-complex-diskp (cons value 0) 1))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp) :nonlinearp t))))
(local (defthm lw-cka-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(defthm lw-exp-neg-lower-cauchy
  (implies (and (rationalp value) (<= 0 value) (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-exp-neg-bounds value left-error))
                       (car (lw-exp-neg-bounds value right-error))))
               (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-exp-neg-bounds-spatial-cauchy
                          (left value) (right value) (cap value)))
                  :in-theory (disable lw-exp-neg-bounds-spatial-cauchy lw-exp-lipschitz-cap))))

(defun lw-damped-phase-sample (value angle negative-error phase-error)
  (lw-complex-scale (car (lw-exp-neg-bounds value negative-error))
                    (lw-phase-value angle phase-error)))

(defthm lw-damped-phase-sample-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp angle))
           (lw-complexp (lw-damped-phase-sample value angle negative-error phase-error)))
  :hints (("Goal" :use ((:instance lw-exp-neg-bounds-valid (epsilon negative-error)))
                  :in-theory (e/d (lw-intervalp) (lw-exp-neg-bounds-valid)))))

(defthm lw-damped-phase-sample-unit
  (implies (and (rationalp value) (<= 0 value) (rationalp angle))
           (lw-complex-diskp (lw-damped-phase-sample value angle negative-error phase-error) 1))
  :hints (("Goal" :use ((:instance lw-exp-neg-bounds-valid (epsilon negative-error))
                        (:instance lw-complex-scale-disk
                          (factor (car (lw-exp-neg-bounds value negative-error)))
                          (point (lw-phase-value angle phase-error)) (radius 1))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-damped-phase-sample value angle negative-error phase-error))
                          (radius (abs (car (lw-exp-neg-bounds value negative-error)))) (cap 1)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-exp-neg-bounds-valid lw-complex-scale-disk))
                  :nonlinearp t)))

(defthm lw-damped-phase-sample-cauchy
  (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp left-negative) (< 0 left-negative) (rationalp left-phase) (< 0 left-phase)
                (rationalp right-negative) (< 0 right-negative) (rationalp right-phase) (< 0 right-phase))
           (lw-complex-diskp
            (lw-complex-sub (lw-damped-phase-sample value angle left-negative left-phase)
                            (lw-damped-phase-sample value angle right-negative right-phase))
            (+ left-negative right-negative left-phase right-phase)))
  :hints (("Goal" :use (
    (:instance lw-exp-neg-bounds-valid (epsilon left-negative))
    (:instance lw-exp-neg-bounds-valid (epsilon right-negative))
    (:instance lw-exp-neg-lower-cauchy (left-error left-negative) (right-error right-negative))
    (:instance lw-cka-real-difference-disk
      (a (car (lw-exp-neg-bounds value left-negative)))
      (b (car (lw-exp-neg-bounds value right-negative))) (error (+ left-negative right-negative)))
    (:instance lw-phase-value-cauchy (value angle) (left-error left-phase) (right-error right-phase))
    (:instance lw-complex-mul-difference-bound
      (a (cons (car (lw-exp-neg-bounds value left-negative)) 0))
      (b (lw-phase-value angle left-phase))
      (c (cons (car (lw-exp-neg-bounds value right-negative)) 0))
      (d (lw-phase-value angle right-phase))
      (left-cap 1) (right-cap 1)
      (left-error (+ left-negative right-negative)) (right-error (+ left-phase right-phase))))
    :in-theory (e/d (lw-intervalp)
                    (lw-exp-neg-bounds-valid lw-exp-neg-lower-cauchy lw-phase-value-cauchy
                     lw-complex-mul-difference-bound)))))

(local (in-theory (disable lw-damped-phase-sample)))


(local (defthm lw-cka-multiply-at-least-one
         (implies (and (rationalp factor) (<= 1 factor) (rationalp value) (<= 0 value))
                  (<= value (* factor value)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-damped-phase-precision-bounds
  (implies (and (rationalp value) (<= 0 value) (rationalp angle) (rationalp error) (< 0 error))
           (and (rationalp (lw-complex-damped-phase-budget value angle error)) (< 0 (lw-complex-damped-phase-budget value angle error)) (<= (lw-complex-damped-phase-budget value angle error) error)
                (rationalp (lw-complex-exp-negative-precision value (lw-complex-damped-phase-budget value angle error))) (< 0 (lw-complex-exp-negative-precision value (lw-complex-damped-phase-budget value angle error))) (<= (lw-complex-exp-negative-precision value (lw-complex-damped-phase-budget value angle error)) error)
                (rationalp (lw-complex-phase-comparison-precision angle (lw-complex-damped-phase-budget value angle error))) (< 0 (lw-complex-phase-comparison-precision angle (lw-complex-damped-phase-budget value angle error))) (<= (lw-complex-phase-comparison-precision angle (lw-complex-damped-phase-budget value angle error)) error)))
  :hints (("Goal" :use (lw-complex-damped-phase-budget-adequate
                        (:instance lw-cka-multiply-at-least-one
                          (factor (+ 3 (* 2 (lw-complex-exp-cap (cons value 0)))
                                       (lw-complex-exp-cap (cons 0 angle))))
                          (value (lw-complex-damped-phase-budget value angle error)))
                        (:instance lw-cka-multiply-at-least-one
                          (factor (+ 4 (* 2 (lw-complex-exp-cap (cons value 0)))))
                          (value
                            (lw-complex-exp-negative-precision
                              value
                              (lw-complex-damped-phase-budget value angle error))))
                        (:instance lw-cka-multiply-at-least-one
                          (factor
                            (lw-complex-phase-comparison-amplifier
                              angle
                              (lw-complex-damped-phase-budget value angle error)))
                          (value
                            (lw-complex-phase-comparison-precision
                              angle
                              (lw-complex-damped-phase-budget value angle error))))
                        (:instance lw-complex-exp-cap-valid (point (cons value 0)))
                        (:instance lw-complex-exp-cap-valid (point (cons 0 angle)))
                        (:instance lw-complex-exp-negative-precision-adequate
                          (error (lw-complex-damped-phase-budget value angle error)))
                        (:instance lw-complex-phase-comparison-precision-adequate
                          (value angle)
                          (error (lw-complex-damped-phase-budget value angle error)))
                        (:instance lw-complex-phase-comparison-amplifier-valid
                          (value angle)
                          (error (lw-complex-damped-phase-budget value angle error))))
                  :in-theory (disable lw-complex-damped-phase-budget-adequate lw-complex-exp-cap-valid
                                      lw-complex-exp-negative-precision-adequate
                                      lw-complex-phase-comparison-precision-adequate
                                      lw-complex-phase-comparison-amplifier-valid)
                  :nonlinearp t)))


(local (defthm lw-cka-value-form
         (equal (lw-complex-damped-phase-value value angle error)
                (lw-damped-phase-sample
                 value angle
                 (lw-complex-exp-negative-precision
                  value (lw-complex-damped-phase-budget value angle error))
                 (lw-complex-phase-comparison-precision
                  angle (lw-complex-damped-phase-budget value angle error))))
         :hints (("Goal" :in-theory (enable lw-damped-phase-sample lw-complex-damped-phase-value)))))

(defthm lw-complex-exp-kernel-agreement-with-margin
  (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp negative-error) (< 0 negative-error)
                (rationalp phase-error) (< 0 phase-error)
                (rationalp complex-error) (< 0 complex-error) (rationalp margin) (< 0 margin))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-damped-phase-sample value angle negative-error phase-error)
               (lw-complex-exp-value (cons (- value) angle) complex-error))
             (+ negative-error phase-error complex-error margin)))
  :hints (("Goal" :use (
    (:instance lw-complex-damped-phase-precision-bounds (error (* 1/4 margin)))
    (:instance lw-damped-phase-sample-cauchy
      (left-negative negative-error)
      (left-phase phase-error)
      (right-negative
        (lw-complex-exp-negative-precision value (lw-complex-damped-phase-budget value angle (* 1/4 margin))))
      (right-phase
        (lw-complex-phase-comparison-precision
          angle
          (lw-complex-damped-phase-budget value angle (* 1/4 margin)))))
    (:instance lw-complex-exp-computed-damped-phase-agreement (error (* 1/4 margin)))
(:instance lw-complex-exp-value-cauchy
  (point (cons (- value) angle))
  (left-error (lw-complex-damped-phase-budget value angle (* 1/4 margin)))
  (right-error complex-error))
    (:instance lw-complex-difference-triangle
      (left (lw-damped-phase-sample value angle negative-error phase-error))
      (middle (lw-complex-damped-phase-value value angle (* 1/4 margin)))
      (right
        (lw-complex-exp-value
          (cons (- value) angle)
          (lw-complex-damped-phase-budget value angle (* 1/4 margin))))
      (radius
        (+
          negative-error
          (lw-complex-exp-negative-precision
            value
            (lw-complex-damped-phase-budget value angle (* 1/4 margin)))
          phase-error
          (lw-complex-phase-comparison-precision
            angle
            (lw-complex-damped-phase-budget value angle (* 1/4 margin)))))
      (other-radius (* 1/4 margin)))
    (:instance lw-complex-difference-triangle
      (left (lw-damped-phase-sample value angle negative-error phase-error))
      (middle
        (lw-complex-exp-value
          (cons (- value) angle)
          (lw-complex-damped-phase-budget value angle (* 1/4 margin))))
      (right (lw-complex-exp-value (cons (- value) angle) complex-error))
      (radius
        (+
          (+
            negative-error
            (lw-complex-exp-negative-precision
              value
              (lw-complex-damped-phase-budget value angle (* 1/4 margin)))
            phase-error
            (lw-complex-phase-comparison-precision
              angle
              (lw-complex-damped-phase-budget value angle (* 1/4 margin))))
          (* 1/4 margin)))
      (other-radius (+ (lw-complex-damped-phase-budget value angle (* 1/4 margin)) complex-error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-damped-phase-sample value angle negative-error phase-error)
          (lw-complex-exp-value (cons (- value) angle) complex-error)))
      (radius
        (+
          (+
            negative-error
            (lw-complex-exp-negative-precision
              value
              (lw-complex-damped-phase-budget value angle (* 1/4 margin)))
            phase-error
            (lw-complex-phase-comparison-precision
              angle
              (lw-complex-damped-phase-budget value angle (* 1/4 margin))))
          (* 1/4 margin)
          (+ (lw-complex-damped-phase-budget value angle (* 1/4 margin)) complex-error)))
      (cap (+ negative-error phase-error complex-error margin))))
    :in-theory (disable lw-complex-damped-phase-precision-bounds lw-damped-phase-sample-cauchy
                     lw-complex-exp-computed-damped-phase-agreement lw-complex-exp-value-cauchy
                     lw-complex-difference-triangle)
    :nonlinearp t)))


(defthm lw-complex-exp-kernel-agreement
  (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp negative-error) (< 0 negative-error) (rationalp phase-error) (< 0 phase-error)
                (rationalp complex-error) (< 0 complex-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-damped-phase-sample value angle negative-error phase-error)
               (lw-complex-exp-value (cons (- value) angle) complex-error))
             (+ negative-error phase-error complex-error)))
  :hints (("Goal" :cases ((lw-complex-diskp (lw-complex-sub (lw-damped-phase-sample value angle negative-error phase-error) (lw-complex-exp-value (cons (- value) angle) complex-error)) (+ negative-error phase-error complex-error)))
                  :use ((:instance lw-complex-disk-gap-excludes (point (lw-complex-sub (lw-damped-phase-sample value angle negative-error phase-error) (lw-complex-exp-value (cons (- value) angle) complex-error))) (radius (+ negative-error phase-error complex-error)))
                        (:instance lw-complex-exp-kernel-agreement-with-margin
                          (margin
                            (lw-disk-gap-error
                              (lw-complex-norm-square
                                (lw-complex-sub
                                  (lw-damped-phase-sample value angle negative-error phase-error)
                                  (lw-complex-exp-value (cons (- value) angle) complex-error)))
                              (+ negative-error phase-error complex-error)))))
                  :in-theory (disable lw-complex-disk-gap-excludes lw-complex-exp-kernel-agreement-with-margin))))

(local (defthm lw-cka-cap-with-margin
         (implies (and (rationalp value) (<= 0 value) (rationalp angle)
                       (rationalp error) (< 0 error) (rationalp margin) (< 0 margin))
                  (lw-complex-diskp (lw-complex-exp-value (cons (- value) angle) error) (+ 1 error margin)))
         :hints (("Goal" :use (
           (:instance lw-complex-exp-kernel-agreement
             (negative-error (* 1/2 margin))
             (phase-error (* 1/2 margin))
             (complex-error error))
           (:instance lw-complex-disk-enlarge
             (point (lw-complex-sub
                     (lw-damped-phase-sample value angle (* 1/2 margin) (* 1/2 margin))
                     (lw-complex-exp-value (cons (- value) angle) error)))
             (radius (+ error (* 1/2 margin) (* 1/2 margin))) (cap (+ error margin)))
           (:instance lw-complex-difference-symmetric
             (left (lw-damped-phase-sample value angle (* 1/2 margin) (* 1/2 margin)))
             (right (lw-complex-exp-value (cons (- value) angle) error))
             (radius (+ error margin)))
           (:instance lw-complex-difference-triangle
             (left (lw-complex-exp-value (cons (- value) angle) error))
             (middle (lw-damped-phase-sample value angle (* 1/2 margin) (* 1/2 margin)))
             (right (cons 0 0))
             (radius (+ error margin))
             (other-radius 1)))
           :in-theory (disable lw-complex-exp-kernel-agreement lw-complex-difference-triangle)))
         :rule-classes nil))

(defthm lw-complex-exp-damped-cap
  (implies (and (rationalp value) (<= 0 value) (rationalp angle) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-complex-exp-value (cons (- value) angle) error) (+ 1 error)))
  :hints (("Goal" :cases ((lw-complex-diskp (lw-complex-exp-value (cons (- value) angle) error) (+ 1 error)))
                  :use ((:instance lw-complex-disk-gap-excludes (point (lw-complex-exp-value (cons (- value) angle) error)) (radius (+ 1 error)))
                        (:instance lw-cka-cap-with-margin
                          (margin
                            (lw-disk-gap-error
                              (lw-complex-norm-square (lw-complex-exp-value (cons (- value) angle) error))
                              (+ 1 error)))))
                  :in-theory (disable lw-complex-disk-gap-excludes))))

(assert-event
 (and (lw-complex-diskp
       (lw-complex-sub (lw-damped-phase-sample 1 1/2 1/5 1/4)
                       (lw-complex-exp-value (cons -1 1/2) 1/5))
       13/20)
      (lw-complex-diskp (lw-complex-exp-value (cons -1 -1/2) 1/5) 6/5)))

