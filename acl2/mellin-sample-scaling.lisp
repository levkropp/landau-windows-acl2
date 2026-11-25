(in-package "ACL2")

(include-book "mellin-exponential-sample")

; Cell quadrature puts the width in the kernel constructor, while the
; dyadic integral multiplies a unit-step sample by the width. Prove that
; these actual evaluators agree up to their requested absolute errors.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-value lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-cap
                 lw-complex-l1 lw-complex-power lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-neg-bounds
                 lw-mellin-sample lw-mellin-sample-kernel-form lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-kernel-weight-scale
                 lw-mellin-exponential-sample lw-mellin-exponential-sample-error
                 lw-mellin-exponential-error-factor lw-mellin-signal-error lw-mellin-kernel-error
                 lw-mellin-phase-error lw-mellin-component-error lw-log-signal-bounds
                 lw-complex-norm-square lw-disk-gap-error
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-msscl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-msscl-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-msscl-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-msscl-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-msscl-double-negative
         (implies (rationalp value) (equal (- (- value)) value))))
(local (defthm lw-msscl-zero-times (equal (* 0 a) 0)))
(local (defthm lw-msscl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-msscl-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-msscl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-msscl-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-msscl-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-msscl-same-point-sub
         (implies (and (rationalp a) (rationalp b) (lw-complexp point))
                  (equal (lw-complex-sub (lw-complex-scale a point) (lw-complex-scale b point))
                         (lw-complex-scale (- a b) point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))
(local (defthm lw-msscl-same-factor-sub
         (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                         (lw-complex-scale factor (lw-complex-sub a b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(defthm lw-mellin-signals-step-cauchy
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp left-step) (<= 0 left-step) (rationalp right-step) (<= 0 right-step)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (lw-mellin-signal value sigma index left-step left-error)
                       (lw-mellin-signal value sigma index right-step right-error)))
               (+ left-error right-error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-error-budgets (step left-step) (error left-error))
    (:instance lw-mellin-error-budgets (step right-step) (error right-error))
    (:instance lw-mellin-primitive-errors-at-most (step left-step) (error left-error))
    (:instance lw-mellin-primitive-errors-at-most (step right-step) (error right-error))
    (:instance lw-log-signal-lower-cauchy
      (left-error (lw-mellin-signal-error value sigma index left-step left-error))
      (right-error (lw-mellin-signal-error value sigma index right-step right-error))))
    :in-theory (e/d (lw-mellin-signal)
                    (lw-mellin-error-budgets lw-mellin-primitive-errors-at-most lw-log-signal-lower-cauchy)))))

(local (defthm lw-msscl-mass-step
         (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step))
                  (equal (lw-kernel-weight-scale value index step)
                         (* step (lw-kernel-weight-scale value index 1))))
         :hints (("Goal" :use ((:instance lw-kernel-weight-scale-nonnegative (step 1)))
                         :in-theory (e/d (lw-kernel-weight-scale)
                                         (lw-kernel-weight-scale-nonnegative))))
         :rule-classes nil))

(local (defthm lw-msscl-exponential-step
         (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                       (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
                  (lw-complex-diskp
                   (lw-complex-sub
                    (lw-mellin-exponential-sample value sigma height index step error error)
                    (lw-complex-scale step (lw-mellin-exponential-sample value sigma height index 1 error error)))
                   (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)))
         :hints (("Goal" :use (
           lw-msscl-mass-step lw-mellin-signal-bounded
           (:instance lw-mellin-signal-bounded (step 1))
           lw-kernel-weight-scale-nonnegative
           (:instance lw-kernel-weight-scale-nonnegative (step 1))
           (:instance lw-mellin-signals-step-cauchy
             (left-step step) (right-step 1) (left-error error) (right-error error))
           (:instance lw-complex-exp-damped-cap (value (* sigma value)) (angle (- (* height value))))
           (:instance lw-complex-scale-disk
             (factor (* (- (lw-mellin-signal value sigma index step error)
                           (lw-mellin-signal value sigma index 1 error))
                        (lw-kernel-weight-scale value index step)))
             (point (lw-complex-exp-value (cons (- (* sigma value)) (- (* height value))) error))
             (radius (+ 1 error)))
           (:instance lw-msscl-abs-product
             (a (- (lw-mellin-signal value sigma index step error)
                   (lw-mellin-signal value sigma index 1 error)))
             (b (lw-kernel-weight-scale value index step)))
           (:instance lw-msscl-multiply-order
             (a (abs (- (lw-mellin-signal value sigma index step error)
                        (lw-mellin-signal value sigma index 1 error))))
             (b (* 2 error)) (factor (* (lw-kernel-weight-scale value index step) (+ 1 error))))
           (:instance lw-complex-disk-enlarge
             (point (lw-complex-sub
                     (lw-mellin-exponential-sample value sigma height index step error error)
                     (lw-complex-scale step (lw-mellin-exponential-sample value sigma height index 1 error error))))
             (radius (* (abs (- (lw-mellin-signal value sigma index step error)
                                (lw-mellin-signal value sigma index 1 error)))
                        (lw-kernel-weight-scale value index step) (+ 1 error)))
             (cap (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error))))
           :in-theory (e/d (lw-mellin-exponential-sample)
                           (lw-mellin-signal-bounded lw-kernel-weight-scale-nonnegative
                            lw-mellin-signals-step-cauchy lw-complex-exp-damped-cap
                            lw-complex-scale-disk lw-msscl-abs-product))
           :nonlinearp t))
         :rule-classes nil))


(defun lw-mellin-scaling-factor (value index step)
  (+
    1
    (* 2 (lw-mellin-exponential-error-factor value index step))
    (* 2 step (lw-mellin-exponential-error-factor value index 1))
    (* 4 (lw-kernel-weight-scale value index step))))

(defthm lw-mellin-scaling-factor-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step))
           (and (rationalp (lw-mellin-scaling-factor value index step))
                (<= 1 (lw-mellin-scaling-factor value index step))))
  :hints (("Goal" :use (lw-mellin-exponential-error-factor-valid
                        (:instance lw-mellin-exponential-error-factor-valid (step 1))
                        lw-kernel-weight-scale-nonnegative
                        (:instance lw-msscl-product-nonnegative
                          (a step) (b (lw-mellin-exponential-error-factor value index 1))))
                  :in-theory (disable lw-mellin-exponential-error-factor-valid lw-kernel-weight-scale-nonnegative)
                  :nonlinearp t)))

(local (in-theory (disable lw-mellin-scaling-factor)))


(defthm lw-mellin-sample-step-coarse
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error) (<= error 1))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sample value sigma height index step error)
               (lw-complex-scale step (lw-mellin-sample value sigma height index 1 error)))
             (* (lw-mellin-scaling-factor value index step) error)))
  :hints (("Goal" :use (
    lw-kernel-weight-scale-nonnegative
    (:instance lw-mellin-exponential-error-factor-valid)
    (:instance lw-mellin-exponential-error-factor-valid (step 1))
    (:instance lw-mellin-sample-exponential-comparison (sample-error error) (complex-error error))
    (:instance lw-mellin-sample-exponential-comparison (step 1) (sample-error error) (complex-error error))
    (:instance lw-mellin-exponential-sample-error-budget (sample-error error) (complex-error error))
    (:instance lw-mellin-exponential-sample-error-budget (step 1) (sample-error error) (complex-error error))
    lw-msscl-exponential-step
    (:instance lw-complex-difference-symmetric
      (left (lw-mellin-sample value sigma height index 1 error))
      (right (lw-mellin-exponential-sample value sigma height index 1 error error))
      (radius (lw-mellin-exponential-sample-error value sigma index 1 error error)))
    (:instance lw-complex-scale-disk
      (factor step)
      (point
        (lw-complex-sub
          (lw-mellin-exponential-sample value sigma height index 1 error error)
          (lw-mellin-sample value sigma height index 1 error)))
      (radius (lw-mellin-exponential-sample-error value sigma index 1 error error)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-sample value sigma height index step error))
      (middle (lw-mellin-exponential-sample value sigma height index step error error))
      (right (lw-complex-scale step (lw-mellin-exponential-sample value sigma height index 1 error error)))
      (radius (lw-mellin-exponential-sample-error value sigma index step error error))
      (other-radius (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-sample value sigma height index step error))
      (middle (lw-complex-scale step (lw-mellin-exponential-sample value sigma height index 1 error error)))
      (right (lw-complex-scale step (lw-mellin-sample value sigma height index 1 error)))
      (radius
        (+
          (lw-mellin-exponential-sample-error value sigma index step error error)
          (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)))
      (other-radius (* step (lw-mellin-exponential-sample-error value sigma index 1 error error))))
    (:instance lw-msscl-multiply-order
      (a (lw-mellin-exponential-sample-error value sigma index 1 error error))
      (b (* (lw-mellin-exponential-error-factor value index 1) (+ error error)))
      (factor step))
    (:instance lw-msscl-product-nonnegative (a (lw-kernel-weight-scale value index step)) (b error))
    (:instance lw-msscl-multiply-order
      (a (+ 1 error))
      (b 2)
      (factor (* 2 (lw-kernel-weight-scale value index step) error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sample value sigma height index step error)
          (lw-complex-scale step (lw-mellin-sample value sigma height index 1 error))))
      (radius
        (+
          (lw-mellin-exponential-sample-error value sigma index step error error)
          (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)
          (* step (lw-mellin-exponential-sample-error value sigma index 1 error error))))
      (cap (* (lw-mellin-scaling-factor value index step) error))))
    :in-theory (e/d (lw-mellin-scaling-factor)
                    (lw-kernel-weight-scale-nonnegative lw-mellin-exponential-error-factor-valid
                     lw-mellin-sample-exponential-comparison lw-mellin-exponential-sample-error-budget
                     lw-complex-scale-disk lw-complex-difference-triangle))
    :nonlinearp t)))


(local (defthm lw-msscl-bounded-precision
         (implies (and (rationalp factor) (<= 1 factor) (rationalp error) (< 0 error))
                  (and (rationalp (min 1 (/ error factor)))
                       (< 0 (min 1 (/ error factor))) (<= (min 1 (/ error factor)) 1)
                       (<= (* factor (min 1 (/ error factor))) error)))
         :hints (("Goal" :use ((:instance inverse-of-* (x factor))
                               (:instance lw-msscl-multiply-order
                                 (a 1) (b (/ error factor)) (factor factor)))
                         :in-theory (disable inverse-of-*)))
         :rule-classes nil))

(defun lw-mellin-scaling-precision (value index step error)
  (min 1 (/ error (+ 1 step (lw-mellin-scaling-factor value index step)))))

(defthm lw-mellin-scaling-precision-adequate
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-scaling-precision value index step error))
                (< 0 (lw-mellin-scaling-precision value index step error))
                (<= (lw-mellin-scaling-precision value index step error) 1)
                (<= (* (+ 1 step (lw-mellin-scaling-factor value index step))
                       (lw-mellin-scaling-precision value index step error)) error)))
  :hints (("Goal" :use (lw-mellin-scaling-factor-valid
                        (:instance lw-msscl-bounded-precision
                          (factor (+ 1 step (lw-mellin-scaling-factor value index step)))))
                  :in-theory (disable lw-mellin-scaling-factor-valid))))

(local (in-theory (disable lw-mellin-scaling-precision)))


(defthm lw-mellin-sample-step-with-margin
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
                (rationalp margin) (< 0 margin))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sample value sigma height index step left-error)
               (lw-complex-scale step (lw-mellin-sample value sigma height index 1 right-error)))
             (+ left-error (* step right-error) margin)))
  :hints (("Goal" :use (
    (:instance lw-mellin-scaling-precision-adequate (error margin))
    (:instance lw-mellin-sample-cauchy (right-error (lw-mellin-scaling-precision value index step margin)))
    (:instance lw-mellin-sample-step-coarse (error (lw-mellin-scaling-precision value index step margin)))
    (:instance lw-mellin-sample-cauchy (step 1) (left-error (lw-mellin-scaling-precision value index step margin)))
    (:instance lw-complex-scale-disk
      (factor step)
      (point
        (lw-complex-sub
          (lw-mellin-sample value sigma height index 1 (lw-mellin-scaling-precision value index step margin))
          (lw-mellin-sample value sigma height index 1 right-error)))
      (radius (+ (lw-mellin-scaling-precision value index step margin) right-error)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-sample value sigma height index step left-error))
      (middle
        (lw-mellin-sample value sigma height index step (lw-mellin-scaling-precision value index step margin)))
      (right
        (lw-complex-scale
          step
          (lw-mellin-sample value sigma height index 1 (lw-mellin-scaling-precision value index step margin))))
      (radius (+ left-error (lw-mellin-scaling-precision value index step margin)))
      (other-radius
        (* (lw-mellin-scaling-factor value index step) (lw-mellin-scaling-precision value index step margin))))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-sample value sigma height index step left-error))
      (middle
        (lw-complex-scale
          step
          (lw-mellin-sample value sigma height index 1 (lw-mellin-scaling-precision value index step margin))))
      (right (lw-complex-scale step (lw-mellin-sample value sigma height index 1 right-error)))
      (radius
        (+
          left-error
          (lw-mellin-scaling-precision value index step margin)
          (*
            (lw-mellin-scaling-factor value index step)
            (lw-mellin-scaling-precision value index step margin))))
      (other-radius (* step (+ (lw-mellin-scaling-precision value index step margin) right-error))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sample value sigma height index step left-error)
          (lw-complex-scale step (lw-mellin-sample value sigma height index 1 right-error))))
      (radius
        (+
          left-error
          (lw-mellin-scaling-precision value index step margin)
          (*
            (lw-mellin-scaling-factor value index step)
            (lw-mellin-scaling-precision value index step margin))
          (* step (+ (lw-mellin-scaling-precision value index step margin) right-error))))
      (cap (+ left-error (* step right-error) margin))))
    :in-theory (disable lw-mellin-scaling-precision-adequate lw-mellin-sample-cauchy
                        lw-mellin-sample-step-coarse lw-complex-scale-disk lw-complex-difference-triangle)
    :nonlinearp t)))

(defthm lw-mellin-sample-step-scaling
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sample value sigma height index step left-error)
               (lw-complex-scale step (lw-mellin-sample value sigma height index 1 right-error)))
             (+ left-error (* step right-error))))
  :hints (("Goal" :cases ((lw-complex-diskp (lw-complex-sub (lw-mellin-sample value sigma height index step left-error) (lw-complex-scale step (lw-mellin-sample value sigma height index 1 right-error))) (+ left-error (* step right-error))))
                  :use (
                    (:instance lw-complex-disk-gap-excludes
                      (point
                        (lw-complex-sub
                          (lw-mellin-sample value sigma height index step left-error)
                          (lw-complex-scale step (lw-mellin-sample value sigma height index 1 right-error))))
                      (radius (+ left-error (* step right-error))))
                    (:instance lw-mellin-sample-step-with-margin
                      (margin
                        (lw-disk-gap-error
                          (lw-complex-norm-square
                            (lw-complex-sub
                              (lw-mellin-sample value sigma height index step left-error)
                              (lw-complex-scale
                                step
                                (lw-mellin-sample value sigma height index 1 right-error))))
                          (+ left-error (* step right-error))))))
                  :in-theory (disable lw-complex-disk-gap-excludes lw-mellin-sample-step-with-margin))))

