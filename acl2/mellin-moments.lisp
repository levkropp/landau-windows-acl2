(in-package "ACL2")

(include-book "complex-exp")
(include-book "kernel-moments")
(include-book "mellin-integrand")

; Moment samples from the existing evaluator share a single zeroth
; coefficient, up to a computed error. This is the local Taylor link.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-mellin-sample lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-error-budgets lw-log-signal-bounds lw-kernel-weight-bounds
                 lw-phase-value lw-kernel-weight-scale lw-exp-term
                 lw-mellin-product-difference lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mm-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mm-component-at-most
         (implies (and (rationalp error) (< 0 error) (rationalp factor) (<= 0 factor))
                  (<= (lw-mellin-component-error error factor) error))
         :hints (("Goal" :use ((:instance lw-positive-division-bound
                                 (numerator error) (divisor (* 3 (+ 1 factor))) (bound error)))
                         :in-theory (enable lw-mellin-component-error) :nonlinearp t))
         :rule-classes nil))

(defthm lw-mellin-primitive-errors-at-most
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (and (<= (lw-mellin-signal-error value sigma index step error) error)
                (<= (lw-mellin-kernel-error value error) error)
                (<= (lw-mellin-phase-error value sigma index step error) error)))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid
                        (:instance lw-mm-component-at-most (factor (lw-mellin-kernel-cap value sigma index step)))
                        (:instance lw-mm-component-at-most (factor (lw-mellin-signal-cap value)))
                        (:instance lw-mm-component-at-most
                          (factor (* (lw-mellin-signal-cap value) (lw-mellin-kernel-cap value sigma index step)))))
                  :in-theory (e/d (lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error)
                                  (lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid))
                  :nonlinearp t)))

(defthm lw-mellin-moment-components
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (and
            (<= (abs (- (lw-mellin-signal value sigma index step left-error)
                        (lw-mellin-signal value sigma 0 step right-error)))
                (+ (lw-mellin-signal-error value sigma index step left-error)
                   (lw-mellin-signal-error value sigma 0 step right-error)))
            (<= (abs (- (lw-mellin-weight value sigma index step left-error)
                        (* (lw-exp-term value index) (lw-mellin-weight value sigma 0 step right-error))))
                (+ (lw-mellin-kernel-error value left-error)
                   (* (lw-exp-term value index) (lw-mellin-kernel-error value right-error))))
            (lw-complex-diskp
             (lw-complex-sub (lw-mellin-phase value sigma height index step left-error)
                             (lw-mellin-phase value sigma height 0 step right-error))
             (+ (lw-mellin-phase-error value sigma index step left-error)
                (lw-mellin-phase-error value sigma 0 step right-error)))))
  :hints (("Goal" :use ((:instance lw-mellin-error-budgets (error left-error))
                        (:instance lw-mellin-error-budgets (index 0) (error right-error))
                        (:instance lw-log-signal-lower-cauchy
                          (left-error (lw-mellin-signal-error value sigma index step left-error))
                          (right-error (lw-mellin-signal-error value sigma 0 step right-error)))
                        (:instance lw-kernel-moment-lower-comparison
                          (left-error (lw-mellin-kernel-error value left-error))
                          (right-error (lw-mellin-kernel-error value right-error)))
                        (:instance lw-phase-value-cauchy (value (- (* height value)))
                          (left-error (lw-mellin-phase-error value sigma index step left-error))
                          (right-error (lw-mellin-phase-error value sigma 0 step right-error))))
                  :in-theory (enable lw-mellin-signal lw-mellin-weight lw-mellin-phase))))

(defthm lw-mellin-moment-weight-bounds
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (natp index))
           (and
            (rationalp (lw-mellin-weight value sigma index step left-error))
            (<= 0 (lw-mellin-weight value sigma index step left-error))
            (<= (lw-mellin-weight value sigma index step left-error) (lw-kernel-weight-scale value index step))
            (rationalp (* (lw-exp-term value index) (lw-mellin-weight value sigma 0 step right-error)))
            (<= 0 (* (lw-exp-term value index) (lw-mellin-weight value sigma 0 step right-error)))
            (<= (* (lw-exp-term value index) (lw-mellin-weight value sigma 0 step right-error))
                (lw-kernel-weight-scale value index step))))
  :hints (("Goal" :use ((:instance lw-kernel-moment-lower-bounds
                          (left-error (lw-mellin-kernel-error value left-error))
                          (right-error (lw-mellin-kernel-error value right-error))))
                  :in-theory (e/d (lw-mellin-weight lw-kernel-weight-scale)
                                  (lw-kernel-moment-lower-bounds)))))

(defun lw-mellin-moment-pair-error (value sigma index step left-error right-error)
  (+ (* (lw-kernel-weight-scale value index step)
        (+ (lw-mellin-signal-error value sigma index step left-error)
           (lw-mellin-signal-error value sigma 0 step right-error)))
     (* (lw-mellin-signal-cap value)
        (+ (lw-mellin-kernel-error value left-error)
           (* (lw-exp-term value index) (lw-mellin-kernel-error value right-error))))
     (* (lw-mellin-signal-cap value) (lw-kernel-weight-scale value index step)
        (+ (lw-mellin-phase-error value sigma index step left-error)
           (lw-mellin-phase-error value sigma 0 step right-error)))))

(defthm lw-mellin-sample-moment-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sample value sigma height index step left-error)
                            (lw-complex-scale (lw-exp-term value index)
                                              (lw-mellin-sample value sigma height 0 step right-error)))
            (lw-mellin-moment-pair-error value sigma index step left-error right-error)))
  :hints (("Goal" :use (lw-mellin-moment-components lw-mellin-moment-weight-bounds
                        lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative
                        (:instance lw-mellin-error-budgets (error left-error))
                        (:instance lw-mellin-error-budgets (index 0) (error right-error))
                        (:instance lw-mellin-signal-bounded (error left-error))
                        (:instance lw-mellin-signal-bounded (index 0) (error right-error))
                        (:instance lw-mellin-product-difference
                          (g1 (lw-mellin-signal value sigma index step left-error))
                          (g2 (lw-mellin-signal value sigma 0 step right-error))
                          (w1 (lw-mellin-weight value sigma index step left-error))
                          (w2 (* (lw-exp-term value index) (lw-mellin-weight value sigma 0 step right-error)))
                          (m (lw-mellin-signal-cap value)) (k (lw-kernel-weight-scale value index step))
                          (g-error (+ (lw-mellin-signal-error value sigma index step left-error)
                                      (lw-mellin-signal-error value sigma 0 step right-error)))
                          (w-error (+ (lw-mellin-kernel-error value left-error)
                                      (* (lw-exp-term value index) (lw-mellin-kernel-error value right-error))))
                          (left (lw-mellin-phase value sigma height index step left-error))
                          (right (lw-mellin-phase value sigma height 0 step right-error))
                          (phase-error (+ (lw-mellin-phase-error value sigma index step left-error)
                                          (lw-mellin-phase-error value sigma 0 step right-error)))))
                  :in-theory (e/d (lw-mellin-sample)
                                  (lw-mellin-moment-components lw-mellin-moment-weight-bounds
                                   lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative))
                  :nonlinearp t)))

(defun lw-mellin-moment-error-factor (value index step)
  (let ((mass (lw-kernel-weight-scale value index step)) (cap (lw-mellin-signal-cap value)))
    (+ mass (* cap (+ 1 (lw-exp-term value index))) (* cap mass))))

(defthm lw-mellin-moment-error-factor-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step) (natp index))
           (and (rationalp (lw-mellin-moment-error-factor value index step))
                (<= 0 (lw-mellin-moment-error-factor value index step))))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative)
                  :in-theory (disable lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative)
                  :nonlinearp t)))

(local (defthm lw-mm-weighted-two
         (implies (and (rationalp a) (rationalp b) (rationalp bound)
                       (<= a bound) (<= b bound) (rationalp factor) (<= 0 factor))
                  (<= (+ a (* factor b)) (* (+ 1 factor) bound)))
         :hints (("Goal" :use ((:instance lw-mm-multiply-order (a b) (b bound)))))
         :rule-classes nil))

(local (defthm lw-mm-total-budget
         (implies (and (rationalp mass) (<= 0 mass) (rationalp cap) (<= 0 cap)
                       (rationalp term) (<= 0 term) (rationalp bound) (<= 0 bound)
                       (rationalp ge) (<= ge bound)
                       (rationalp we) (<= we (* (+ 1 term) bound))
                       (rationalp pe) (<= pe bound))
                  (<= (+ (* mass ge) (* cap we) (* cap mass pe))
                      (* (+ mass (* cap (+ 1 term)) (* cap mass)) bound)))
         :hints (("Goal" :use ((:instance lw-mm-multiply-order (a ge) (b bound) (factor mass))
                              (:instance lw-mm-multiply-order (a we) (b (* (+ 1 term) bound)) (factor cap))
                              (:instance lw-mm-multiply-order (a pe) (b bound) (factor (* cap mass))))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-mellin-moment-pair-error-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (lw-mellin-moment-pair-error value sigma index step left-error right-error)
               (* (lw-mellin-moment-error-factor value index step) (+ left-error right-error))))
  :hints (("Goal" :use ((:instance lw-mellin-primitive-errors-at-most (error left-error))
                        (:instance lw-mellin-primitive-errors-at-most (index 0) (error right-error))
                        (:instance lw-mellin-error-budgets (error left-error))
                        (:instance lw-mellin-error-budgets (index 0) (error right-error))
                        lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative
                        (:instance lw-mm-weighted-two
                          (a (lw-mellin-kernel-error value left-error))
                          (b (lw-mellin-kernel-error value right-error))
                          (bound (+ left-error right-error)) (factor (lw-exp-term value index)))
                        (:instance lw-mm-total-budget
                          (mass (lw-kernel-weight-scale value index step))
                          (cap (lw-mellin-signal-cap value)) (term (lw-exp-term value index))
                          (bound (+ left-error right-error))
                          (ge (+ (lw-mellin-signal-error value sigma index step left-error)
                                 (lw-mellin-signal-error value sigma 0 step right-error)))
                          (we (+ (lw-mellin-kernel-error value left-error)
                                 (* (lw-exp-term value index) (lw-mellin-kernel-error value right-error))))
                          (pe (+ (lw-mellin-phase-error value sigma index step left-error)
                                 (lw-mellin-phase-error value sigma 0 step right-error)))))
                  :in-theory (disable lw-mellin-primitive-errors-at-most
                                      lw-mellin-signal-cap-valid lw-kernel-weight-scale-nonnegative)
                  :nonlinearp t)))

(defun lw-mellin-moment-precision (value index step error)
  (/ error (* 2 (+ 1 (lw-mellin-moment-error-factor value index step)))))

(defthm lw-mellin-moment-precision-adequate
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step) (natp index)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-moment-precision value index step error))
                (< 0 (lw-mellin-moment-precision value index step error))
                (<= (* 2 (lw-mellin-moment-error-factor value index step)
                       (lw-mellin-moment-precision value index step error)) error)))
  :hints (("Goal" :use (lw-mellin-moment-error-factor-valid
                        (:instance lw-positive-division-bound
                          (numerator (* 2 (lw-mellin-moment-error-factor value index step) error))
                          (divisor (* 2 (+ 1 (lw-mellin-moment-error-factor value index step)))) (bound error)))
                  :in-theory (disable lw-mellin-moment-error-factor lw-mellin-moment-error-factor-valid)
                  :nonlinearp t)))

(local (in-theory (disable lw-mellin-moment-precision lw-mellin-moment-error-factor
                           lw-mellin-moment-pair-error)))

(defthm lw-mellin-sample-computed-moment-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-mellin-sample value sigma height index step (lw-mellin-moment-precision value index step error))
             (lw-complex-scale
              (lw-exp-term value index)
              (lw-mellin-sample value sigma height 0 step (lw-mellin-moment-precision value index step error))))
            error))
  :hints (("Goal" :use (lw-mellin-moment-precision-adequate
                        (:instance lw-mellin-sample-moment-comparison
                          (left-error (lw-mellin-moment-precision value index step error))
                          (right-error (lw-mellin-moment-precision value index step error)))
                        (:instance lw-mellin-moment-pair-error-budget
                          (left-error (lw-mellin-moment-precision value index step error))
                          (right-error (lw-mellin-moment-precision value index step error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-mellin-sample value sigma height index step
                                                    (lw-mellin-moment-precision value index step error))
                                  (lw-complex-scale
                                   (lw-exp-term value index)
                                   (lw-mellin-sample value sigma height 0 step
                                                     (lw-mellin-moment-precision value index step error)))))
                          (radius (lw-mellin-moment-pair-error
                                   value sigma index step
                                   (lw-mellin-moment-precision value index step error)
                                   (lw-mellin-moment-precision value index step error)))
                          (cap error)))
                  :in-theory (disable lw-mellin-moment-precision-adequate lw-mellin-sample-moment-comparison
                                      lw-mellin-moment-pair-error-budget))))

(defthm lw-mellin-moment-precision-at-most
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step) (natp index)
                (rationalp error) (< 0 error))
           (<= (lw-mellin-moment-precision value index step error) error))
  :hints (("Goal" :use (lw-mellin-moment-error-factor-valid
                        (:instance lw-positive-division-bound
                          (numerator error)
                          (divisor (* 2 (+ 1 (lw-mellin-moment-error-factor value index step)))) (bound error)))
                  :in-theory (e/d (lw-mellin-moment-precision)
                                  (lw-mellin-moment-error-factor-valid))
                  :nonlinearp t)))
