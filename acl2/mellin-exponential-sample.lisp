(in-package "ACL2")

(include-book "complex-kernel-agreement")
(include-book "mellin-moments")

; Identify the actual Mellin sample's existing reciprocal/phase precision
; choices with a single complex Taylor evaluation. The signal and exact
; factorial-normalized mass factor are retained.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-value lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-cap
                 lw-complex-l1 lw-complex-power lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-neg-bounds
                 lw-exp-neg-bounds-overlap lw-kernel-weight-bounds lw-kernel-weight-scale
                 lw-kernel-weight-precision lw-mellin-sample lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-log-signal-bounds lw-phase-value lw-damped-phase-sample
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mes-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mes-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mes-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mes-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mes-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mes-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-mes-double-negative
         (implies (rationalp value) (equal (- (- value)) value))))
(local (defthm lw-mes-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-mes-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-mes-scaled-difference
         (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                         (lw-complex-scale factor (lw-complex-sub a b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-sub)))))

(defun lw-mellin-negative-error (value index step error)
  (lw-kernel-weight-precision value index step (lw-mellin-kernel-error value error)))

(defthm lw-mellin-negative-error-data
  (implies (and (rationalp value) (<= 0 value)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-negative-error value index step error))
                (< 0 (lw-mellin-negative-error value index step error))
                (<= (lw-mellin-negative-error value index step error) error)))
  :hints (("Goal" :use ((:instance lw-mellin-error-budgets (sigma 0))
                        (:instance lw-mellin-primitive-errors-at-most (sigma 0))
                        lw-kernel-weight-scale-nonnegative
                        (:instance lw-kernel-weight-precision-positive (error (lw-mellin-kernel-error value error)))
                        (:instance lw-positive-division-bound
                          (numerator (lw-mellin-kernel-error value error))
                          (divisor (+ 1 (lw-kernel-weight-scale value index step))) (bound error)))
                  :in-theory (e/d (lw-kernel-weight-precision)
                                  (lw-mellin-error-budgets lw-mellin-primitive-errors-at-most
                                   lw-kernel-weight-precision-positive lw-kernel-weight-scale-nonnegative))
                  :nonlinearp t)))

(local (in-theory (disable lw-mellin-negative-error)))

(defthm lw-mellin-sample-kernel-form
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (equal (lw-mellin-sample value sigma height index step error)
                  (lw-complex-scale
                   (* (lw-mellin-signal value sigma index step error) (lw-kernel-weight-scale value index step))
                   (lw-damped-phase-sample
                    (* sigma value) (- (* height value))
                    (lw-mellin-negative-error value index step error)
                    (lw-mellin-phase-error value sigma index step error)))))
  :hints (("Goal" :use (lw-mellin-signal-bounded lw-mellin-negative-error-data
                        (:instance lw-exp-neg-bounds-valid
                          (value (* sigma value)) (epsilon (lw-mellin-negative-error value index step error))))
                  :in-theory (e/d (lw-mellin-sample lw-mellin-weight lw-mellin-phase
                                   lw-kernel-weight-bounds lw-damped-phase-sample lw-mellin-negative-error lw-intervalp)
                                  (lw-mellin-signal-bounded lw-mellin-negative-error-data lw-exp-neg-bounds-valid)))))

(defun lw-mellin-exponential-sample (value sigma height index step sample-error complex-error)
  (lw-complex-scale
   (* (lw-mellin-signal value sigma index step sample-error) (lw-kernel-weight-scale value index step))
   (lw-complex-exp-value (cons (- (* sigma value)) (- (* height value))) complex-error)))

(defthm lw-mellin-exponential-sample-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step)
                (rationalp sample-error) (< 0 sample-error) (rationalp complex-error) (< 0 complex-error))
           (lw-complexp (lw-mellin-exponential-sample value sigma height index step sample-error complex-error)))
  :hints (("Goal" :use ((:instance lw-mellin-signal-bounded (error sample-error)))
                  :in-theory (disable lw-mellin-signal-bounded))))

(defun lw-mellin-exponential-sample-error (value sigma index step sample-error complex-error)
  (* (abs (lw-mellin-signal value sigma index step sample-error))
     (lw-kernel-weight-scale value index step)
     (+ (lw-mellin-negative-error value index step sample-error)
        (lw-mellin-phase-error value sigma index step sample-error) complex-error)))


(defthm lw-mellin-sample-exponential-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step)
                (rationalp sample-error) (< 0 sample-error) (rationalp complex-error) (< 0 complex-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sample value sigma height index step sample-error)
               (lw-mellin-exponential-sample value sigma height index step sample-error complex-error))
             (lw-mellin-exponential-sample-error value sigma index step sample-error complex-error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-error-budgets (error sample-error))
    (:instance lw-mellin-negative-error-data (error sample-error))
    (:instance lw-mellin-signal-bounded (error sample-error))
    (:instance lw-mellin-sample-kernel-form (error sample-error))
    (:instance lw-mes-product-nonnegative (a sigma) (b value))
    (:instance lw-complex-exp-kernel-agreement
      (value (* sigma value))
      (angle (- (* height value)))
      (negative-error (lw-mellin-negative-error value index step sample-error))
      (phase-error (lw-mellin-phase-error value sigma index step sample-error))
      (complex-error complex-error))
    (:instance lw-complex-scale-disk
      (factor
        (* (lw-mellin-signal value sigma index step sample-error) (lw-kernel-weight-scale value index step)))
      (point
        (lw-complex-sub
          (lw-damped-phase-sample
            (* sigma value)
            (- (* height value))
            (lw-mellin-negative-error value index step sample-error)
            (lw-mellin-phase-error value sigma index step sample-error))
          (lw-complex-exp-value (cons (- (* sigma value)) (- (* height value))) complex-error)))
      (radius
        (+
          (lw-mellin-negative-error value index step sample-error)
          (lw-mellin-phase-error value sigma index step sample-error)
          complex-error)))
    (:instance lw-mes-abs-product
      (a (lw-mellin-signal value sigma index step sample-error))
      (b (lw-kernel-weight-scale value index step))))
    :in-theory (e/d (lw-mellin-exponential-sample lw-mellin-exponential-sample-error)
                    (lw-mellin-error-budgets lw-mellin-negative-error-data lw-mellin-signal-bounded
                     lw-mellin-sample-kernel-form lw-complex-exp-kernel-agreement lw-complex-scale-disk
                     lw-mes-abs-product))
    :nonlinearp t)))

(defun lw-mellin-exponential-error-factor (value index step)
  (+ 1 (* 2 (lw-mellin-signal-cap value) (lw-kernel-weight-scale value index step))))

(defthm lw-mellin-exponential-error-factor-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step))
           (and (rationalp (lw-mellin-exponential-error-factor value index step))
                (<= 1 (lw-mellin-exponential-error-factor value index step))))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative
                        (:instance lw-mes-product-nonnegative
                          (a (lw-mellin-signal-cap value)) (b (lw-kernel-weight-scale value index step))))
                  :in-theory (disable lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative)
                  :nonlinearp t)))


(local (defthm lw-mes-numerical-error-budget
         (implies (and (rationalp cap) (<= 0 cap) (rationalp mass) (<= 0 mass)
                       (rationalp amplitude) (<= 0 amplitude) (<= amplitude cap)
                       (rationalp negative-error) (<= 0 negative-error)
                       (rationalp phase-error) (<= 0 phase-error)
                       (rationalp sample-error) (<= 0 sample-error)
                       (rationalp complex-error) (<= 0 complex-error)
                       (<= negative-error sample-error) (<= phase-error sample-error))
                  (<= (* amplitude mass (+ negative-error phase-error complex-error))
                      (* (+ 1 (* 2 cap mass)) (+ sample-error complex-error))))
         :hints (("Goal" :use (
           (:instance lw-mes-product-nonnegative (a amplitude) (b mass))
           (:instance lw-mes-product-nonnegative (a cap) (b mass))
           (:instance lw-mes-multiply-order
             (a amplitude) (b cap) (factor mass))
           (:instance lw-mes-multiply-order
             (a (+ negative-error phase-error complex-error))
             (b (+ (* 2 sample-error) (* 2 complex-error))) (factor (* amplitude mass)))
           (:instance lw-mes-multiply-order
             (a (* amplitude mass)) (b (* cap mass))
             (factor (+ (* 2 sample-error) (* 2 complex-error)))))
           :nonlinearp t))
         :rule-classes nil))

(defthm lw-mellin-exponential-sample-error-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp sample-error) (< 0 sample-error)
                (rationalp complex-error) (< 0 complex-error))
           (<= (lw-mellin-exponential-sample-error value sigma index step sample-error complex-error)
               (* (lw-mellin-exponential-error-factor value index step) (+ sample-error complex-error))))
  :hints (("Goal" :use (
    (:instance lw-mellin-error-budgets (error sample-error))
    (:instance lw-mellin-primitive-errors-at-most (error sample-error))
    (:instance lw-mellin-negative-error-data (error sample-error))
    (:instance lw-mellin-signal-bounded (error sample-error))
    lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative
    (:instance lw-mes-numerical-error-budget
      (cap (lw-mellin-signal-cap value)) (mass (lw-kernel-weight-scale value index step))
      (amplitude (abs (lw-mellin-signal value sigma index step sample-error)))
      (negative-error (lw-mellin-negative-error value index step sample-error))
      (phase-error (lw-mellin-phase-error value sigma index step sample-error))))
    :in-theory (e/d (lw-mellin-exponential-sample-error lw-mellin-exponential-error-factor)
                    (lw-mellin-error-budgets lw-mellin-primitive-errors-at-most lw-mellin-negative-error-data
                     lw-mellin-signal-bounded lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative)))))

(local (in-theory (disable lw-mellin-exponential-sample lw-mellin-exponential-sample-error
                           lw-mellin-exponential-error-factor)))

(defun lw-mellin-exponential-precision (value index step error)
  (/ error (* 2 (+ 1 (lw-mellin-exponential-error-factor value index step)))))

(defthm lw-mellin-exponential-precision-adequate
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-exponential-precision value index step error))
                (< 0 (lw-mellin-exponential-precision value index step error))
                (<= (* 2 (lw-mellin-exponential-error-factor value index step)
                       (lw-mellin-exponential-precision value index step error)) error)))
  :hints (("Goal" :use (lw-mellin-exponential-error-factor-valid
                        (:instance lw-positive-division-bound
                          (numerator (* 2 (lw-mellin-exponential-error-factor value index step) error))
                          (divisor (* 2 (+ 1 (lw-mellin-exponential-error-factor value index step)))) (bound error)))
                  :in-theory (disable lw-mellin-exponential-error-factor-valid) :nonlinearp t)))

(local (in-theory (disable lw-mellin-exponential-precision)))

(defthm lw-mellin-sample-computed-exponential-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-mellin-sample value sigma height index step (lw-mellin-exponential-precision value index step error))
             (lw-mellin-exponential-sample
              value sigma height index step (lw-mellin-exponential-precision value index step error)
              (lw-mellin-exponential-precision value index step error))) error))
  :hints (("Goal" :use (lw-mellin-exponential-precision-adequate
                        (:instance lw-mellin-sample-exponential-comparison
                          (sample-error (lw-mellin-exponential-precision value index step error))
                          (complex-error (lw-mellin-exponential-precision value index step error)))
                        (:instance lw-mellin-exponential-sample-error-budget
                          (sample-error (lw-mellin-exponential-precision value index step error))
                          (complex-error (lw-mellin-exponential-precision value index step error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-mellin-sample value sigma height index step
                                                    (lw-mellin-exponential-precision value index step error))
                                  (lw-mellin-exponential-sample value sigma height index step
                                    (lw-mellin-exponential-precision value index step error)
                                    (lw-mellin-exponential-precision value index step error))))
                          (radius (lw-mellin-exponential-sample-error value sigma index step
                                    (lw-mellin-exponential-precision value index step error)
                                    (lw-mellin-exponential-precision value index step error))) (cap error)))
                  :in-theory (disable lw-mellin-exponential-precision-adequate lw-mellin-sample-exponential-comparison
                                      lw-mellin-exponential-sample-error-budget)
                  :nonlinearp t)))


(defthm lw-mellin-signals-abscissa-cauchy
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-sigma) (<= 0 left-sigma) (rationalp right-sigma) (<= 0 right-sigma)
                (rationalp step) (<= 0 step) (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (abs (- (lw-mellin-signal value left-sigma index step left-error)
                       (lw-mellin-signal value right-sigma index step right-error)))
               (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-mellin-error-budgets (sigma left-sigma) (error left-error))
                        (:instance lw-mellin-error-budgets (sigma right-sigma) (error right-error))
                        (:instance lw-mellin-primitive-errors-at-most (sigma left-sigma) (error left-error))
                        (:instance lw-mellin-primitive-errors-at-most (sigma right-sigma) (error right-error))
                        (:instance lw-log-signal-lower-cauchy
                          (left-error (lw-mellin-signal-error value left-sigma index step left-error))
                          (right-error (lw-mellin-signal-error value right-sigma index step right-error))))
                  :in-theory (e/d (lw-mellin-signal)
                                  (lw-mellin-error-budgets lw-mellin-primitive-errors-at-most
                                   lw-log-signal-lower-cauchy)))))

