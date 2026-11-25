(in-package "ACL2")

(include-book "mellin-frozen-tail")

(include-book "signal-exponential-refinement")

; The mass-five tail remains uniform while exponential point samples
; are refined independently of the frozen coefficients and cutpoints.
; The cutoff and grid constructors are the existing frozen-family ones.

(local (in-theory
        (disable lw-smoothed-sum-bounds lw-mangoldt-bounds lw-ramp
                 lw-log-ramp-extension lw-exp-lipschitz-cap
                 lw-log-signal-point lw-log-signal-delta lw-log-signal-cap
                 lw-log-signal-margin lw-log-signal-lipschitz lw-log-signal-budget
                 lw-log-signal-spatial-cap lw-signal-count lw-signal-precision
                 lw-log-signal-linear-precision lw-interval-add lw-interval-scale
                 lw-log-bounds lw-euler-bounds lw-exp-bounds lw-exp-index lw-exp-term lw-exp-sum
                 lw-smoothed-ramp-unit-error lw-smoothed-ramp-log-error lw-log-signal-ramp-count
                 lw-smoothed-ramp-extension-sum lw-smoothed-sum-bounds-zero-tail lw-exp-bounds-valid
                 lw-signal-exponential-value lw-signal-exponential-linear
                 lw-signal-exponential-cost lw-signal-exponential-precision
                 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
                 lw-complex-disk-enlarge lw-disk-enlarge
                 lw-mellin-sample lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-log-signal-bounds
                 lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision)))

(local (in-theory (disable lw-signal-exponential-refined-value
 lw-mellin-frozen-sample lw-mellin-frozen-tail-sum lw-mellin-frozen-computed-tail
 lw-mellin-frozen-cutoff lw-mellin-frozen-grid-count lw-mellin-frozen-grid-step)))

(local (defthm lw-mrt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mrt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mrt-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrt-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))

(local (defthm lw-mrt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mrt-left-commutes)))))

(local (defthm lw-mrt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrt-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))

(local (defthm lw-mrt-sum-error
         (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- c d)) other-radius))
                  (<= (abs (- (+ a c) (+ b d))) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= c d)))) :rule-classes nil))

(local (defthm lw-mrt-weighted-error
         (implies
          (and (rationalp a) (rationalp b) (rationalp weight) (<= 0 weight)
               (rationalp index) (< 0 index) (<= weight index)
               (rationalp radius) (<= 0 radius) (<= (abs (- a b)) (* radius (/ index))))
          (<= (abs (- (* weight a) (* weight b))) radius))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x index))
                        (:instance lw-mrt-multiply-order
                          (a (abs (- a b))) (b (* radius (/ index))) (factor weight))
                        (:instance lw-mrt-multiply-order
                          (a weight) (b index) (factor (* radius (/ index)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(defun lw-mellin-refined-sample (cap value sigma height index step model-error sample-error exp-error)
  (lw-complex-scale
    (* (lw-signal-exponential-refined-value cap value model-error exp-error)
       (lw-mellin-weight value sigma index step sample-error))
    (lw-mellin-phase value sigma height index step sample-error)))

(defthm lw-mellin-refined-sample-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step)
                (rationalp model-error) (< 0 model-error)
                (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error))
           (lw-complexp (lw-mellin-refined-sample cap value sigma height index step model-error sample-error exp-error)))
  :hints (("Goal"
           :use ((:instance lw-signal-exponential-refined-rational (error model-error))
                 (:instance lw-mellin-weight-bounded (error sample-error))
                 (:instance lw-mellin-phase-rational (error sample-error)))
           :in-theory (disable lw-signal-exponential-refined-rational lw-mellin-weight-bounded
                               lw-mellin-phase-rational)
           :do-not-induct t)))

(defthm lw-mellin-refined-sample-native
 (equal
  (lw-mellin-refined-sample cap value sigma height index step model-error sample-error
                            (lw-signal-exponential-precision cap model-error))
  (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error))
 :hints (("Goal" :in-theory (enable lw-mellin-refined-sample lw-mellin-frozen-sample))))

(defthm lw-mellin-refined-sample-kernel-bound
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp sigma) (<= 2 sigma) (rationalp height) (rationalp step) (<= 0 step)
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error)))
           (lw-complex-diskp
            (lw-mellin-refined-sample cap value sigma height index step model-error sample-error exp-error)
            (* 5 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error)))))
  :hints (("Goal"
           :use ((:instance lw-signal-exponential-refined-rational (error model-error))
                 (:instance lw-signal-exponential-refined-uniform-growth (error model-error))
                 (:instance lw-signal-exponential-parameters (error model-error))
                 (:instance lw-exp-bounds-valid
                   (epsilon exp-error))
                 (:instance lw-mellin-error-budgets (error sample-error))
                 (:instance lw-mellin-weight-bounded (error sample-error))
                 (:instance lw-mellin-phase-unit (error sample-error))
                 (:instance lw-kernel-weight-bounds-valid
                   (error (lw-mellin-kernel-error value sample-error)))
                 (:instance lw-kernel-weight-bounds-valid (sigma (- sigma 2)) (error shifted-error))
                 (:instance lw-kernel-lower-quadratic-shift
                   (signal-error exp-error)
                   (kernel-error (lw-mellin-kernel-error value sample-error)))
                 (:instance lw-mrt-multiply-order
                   (a (abs (lw-signal-exponential-refined-value cap value model-error exp-error)))
                   (b (* 5 (car (lw-exp-bounds value exp-error))
                           (car (lw-exp-bounds value exp-error))))
                   (factor (lw-mellin-weight value sigma index step sample-error)))
                 (:instance lw-complex-scale-disk
                   (point (lw-mellin-phase value sigma height index step sample-error)) (radius 1)
                   (factor (* (lw-signal-exponential-refined-value cap value model-error exp-error)
                              (lw-mellin-weight value sigma index step sample-error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-refined-sample cap value sigma height index step model-error sample-error exp-error))
                   (radius (abs (* (lw-signal-exponential-refined-value cap value model-error exp-error)
                                   (lw-mellin-weight value sigma index step sample-error))))
                   (cap (* 5 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error))))))
           :in-theory
           (e/d (lw-mellin-weight lw-intervalp)
                (lw-signal-exponential-refined-rational lw-signal-exponential-refined-uniform-growth
                 lw-signal-exponential-parameters lw-mellin-error-budgets lw-mellin-weight-bounded
                 lw-mellin-phase-unit lw-kernel-weight-bounds-valid lw-kernel-lower-quadratic-shift
                 lw-complex-scale-disk))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-mellin-refined-sample lw-kernel-tail-rectangles lw-mellin-tail-cutoff
                 lw-mellin-tail-coefficient)))

(defun lw-mellin-refined-tail-sum (cap start step count sigma height index model-error sample-error exp-error)
  (declare (xargs :measure (nfix count)))
  (if (zp count) (cons 0 0)
    (lw-complex-add (lw-mellin-refined-sample cap start sigma height index step model-error sample-error exp-error) (lw-mellin-refined-tail-sum cap (+ start step) step (- count 1) sigma height index model-error sample-error exp-error))))

(local (defthm lw-mrt-tail-zero
         (equal (lw-mellin-refined-tail-sum cap start step 0 sigma height index model-error sample-error exp-error) (cons 0 0))
         :hints (("Goal" :expand ((lw-mellin-refined-tail-sum cap start step 0 sigma height index model-error sample-error exp-error))))))

(local (defthm lw-mrt-kernel-tail-zero
         (equal (lw-kernel-tail-rectangles start step 0 rate index error) 0)
         :hints (("Goal" :expand ((lw-kernel-tail-rectangles start step 0 rate index error))))))

(local (defthm lw-mrt-zero-disk
         (lw-complex-diskp (cons 0 0) 0)
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-mellin-refined-tail-sum-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
                (rationalp step) (<= 0 step) (natp count) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp model-error) (< 0 model-error)
                (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error))
           (lw-complexp
            (lw-mellin-refined-tail-sum cap start step count sigma height index model-error sample-error exp-error)))
  :hints (("Goal" :induct
                   (lw-mellin-refined-tail-sum cap start step count sigma height index model-error sample-error exp-error))))

(defthm lw-mellin-refined-tail-kernel-bound
  (implies (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
                (rationalp step) (<= 0 step) (natp count) (rationalp sigma) (<= 2 sigma)
                (rationalp height) (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error)))
           (lw-complex-diskp
            (lw-mellin-refined-tail-sum cap start step count sigma height index model-error sample-error exp-error)
            (* 5 (lw-kernel-tail-rectangles start step count (- sigma 2) index shifted-error))))
  :hints
  (("Goal" :induct
             (lw-mellin-refined-tail-sum cap start step count sigma height index model-error sample-error exp-error)
           :in-theory (disable (:definition lw-mellin-refined-tail-sum)))
   (and stable-under-simplificationp
        '(:use ((:instance lw-mellin-refined-sample-kernel-bound (value start))
                (:instance lw-complex-add-disk
                  (left (lw-mellin-refined-sample cap start sigma height index step model-error sample-error exp-error))
                  (radius (* 5 (cdr (lw-kernel-weight-bounds start (- sigma 2) index step shifted-error))))
                  (right (lw-mellin-refined-tail-sum cap (+ start step) step (- count 1) sigma height index model-error sample-error exp-error))
                  (other-radius (* 5 (lw-kernel-tail-rectangles (+ start step) step (- count 1)
                                       (- sigma 2) index shifted-error)))))
          :expand ((lw-mellin-refined-tail-sum cap start step count sigma height index model-error sample-error exp-error)
                   (lw-kernel-tail-rectangles start step count (- sigma 2) index shifted-error))
          :in-theory (disable lw-mellin-refined-sample-kernel-bound lw-complex-add-disk)
          :nonlinearp nil :do-not-induct t))))

(local (in-theory (disable lw-mellin-frozen-cutoff)))

(defthm lw-mellin-refined-tail-at-cutoff
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
                (natp index) (natp count) (rationalp target-error) (< 0 target-error)
                (rationalp step) (< 0 step) (<= step (lw-mellin-frozen-cutoff sigma index target-error))
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error)))
           (lw-complex-diskp
            (lw-mellin-refined-tail-sum cap (lw-mellin-frozen-cutoff sigma index target-error) step count
              sigma height index model-error sample-error exp-error)
            target-error))
  :hints (("Goal"
           :use (lw-mellin-frozen-cutoff-valid
                 (:instance lw-mellin-refined-tail-kernel-bound
                   (start (lw-mellin-frozen-cutoff sigma index target-error)) (shifted-error 1))
                 (:instance lw-kernel-tail-rectangles-at-cutoff (rate (- sigma 2)) (mass 5) (error 1))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-refined-tail-sum cap (lw-mellin-frozen-cutoff sigma index target-error) step count
                            sigma height index model-error sample-error exp-error))
                   (radius (* 5 (lw-kernel-tail-rectangles (lw-mellin-frozen-cutoff sigma index target-error)
                                  step count (- sigma 2) index 1)))
                   (cap target-error)))
           :in-theory (e/d (lw-mellin-frozen-cutoff)
                           (lw-mellin-frozen-cutoff-valid lw-mellin-refined-tail-kernel-bound
                            lw-kernel-tail-rectangles-at-cutoff
                            lw-mellin-refined-tail-sum))
           :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-refined-computed-tail (cap end mesh sigma height index model-error sample-error target-error exp-error)
  (lw-mellin-refined-tail-sum cap (lw-mellin-frozen-cutoff sigma index target-error)
    (lw-mellin-frozen-grid-step sigma index target-error end mesh)
    (lw-mellin-frozen-grid-count sigma index target-error end mesh)
    sigma height index model-error sample-error exp-error))

(local (in-theory
        (disable lw-mellin-frozen-grid-count lw-mellin-frozen-grid-step lw-mellin-refined-tail-sum)))

(defthm lw-mellin-refined-computed-tail-rational
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
        (rationalp target-error) (< 0 target-error) (natp index)
        (rationalp end) (< (lw-mellin-frozen-cutoff sigma index target-error) end)
        (rationalp mesh) (< 0 mesh) (rationalp model-error) (< 0 model-error)
        (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error))
   (lw-complexp (lw-mellin-refined-computed-tail cap end mesh sigma height index model-error sample-error target-error exp-error)))
  :hints (("Goal"
           :use (lw-mellin-frozen-cutoff-valid lw-mellin-frozen-grid-parameters)
           :in-theory (disable lw-mellin-frozen-cutoff-valid lw-mellin-frozen-grid-parameters)
           :do-not-induct t)))

(defthm lw-mellin-refined-computed-tail-bound
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
        (rationalp target-error) (< 0 target-error) (natp index)
        (rationalp end) (< (lw-mellin-frozen-cutoff sigma index target-error) end)
        (rationalp mesh) (< 0 mesh) (rationalp model-error) (< 0 model-error) (<= model-error 1)
        (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error)))
   (lw-complex-diskp
    (lw-mellin-refined-computed-tail cap end mesh sigma height index model-error sample-error target-error exp-error)
    target-error))
  :hints (("Goal"
           :use (lw-mellin-frozen-grid-parameters
                 (:instance lw-mellin-refined-tail-at-cutoff
                   (count (lw-mellin-frozen-grid-count sigma index target-error end mesh))
                   (step (lw-mellin-frozen-grid-step sigma index target-error end mesh))))
           :in-theory (disable lw-mellin-frozen-grid-parameters lw-mellin-refined-tail-at-cutoff)
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mrt-coefficient-five
         (equal (lw-mellin-tail-coefficient rate index 5)
                (* 5 (lw-mellin-tail-coefficient rate index 1)))
         :hints (("Goal" :in-theory (e/d (lw-mellin-tail-coefficient) (lw-rational-power))))))

(defthm lw-mellin-refined-tail-after-cutoff
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
        (natp index) (natp count) (rationalp target-error) (< 0 target-error)
        (rationalp start) (<= (lw-mellin-frozen-cutoff sigma index target-error) start)
        (rationalp step) (< 0 step) (<= step start)
        (rationalp model-error) (< 0 model-error) (<= model-error 1)
        (rationalp sample-error) (< 0 sample-error)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error)))
   (lw-complex-diskp
    (lw-mellin-refined-tail-sum cap start step count sigma height index model-error sample-error exp-error)
    target-error))
  :hints (("Goal"
           :use (lw-mellin-frozen-cutoff-valid
                 (:instance lw-mellin-tail-cutoff-adequate (rate (- sigma 2)) (mass 5) (error target-error))
                 (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                 (:instance lw-mrt-multiply-order
                   (a (lw-mellin-frozen-cutoff sigma index target-error)) (b start) (factor (- sigma 2)))
                 (:instance lw-mrt-multiply-order
                   (a (lw-mellin-frozen-cutoff sigma index target-error)) (b start) (factor target-error))
                 (:instance lw-mellin-refined-tail-kernel-bound (shifted-error 1))
                 (:instance lw-kernel-tail-rectangles-bound (rate (- sigma 2)) (error 1))
                 (:instance lw-mrt-multiply-order
                   (a (lw-kernel-tail-rectangles start step count (- sigma 2) index 1))
                   (b (/ (* 2 (lw-mellin-tail-coefficient (- sigma 2) index 1)) start)) (factor 5))
                 (:instance lw-positive-division-bound
                   (numerator (* 2 (lw-mellin-tail-coefficient (- sigma 2) index 5))) (divisor start) (bound target-error))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-refined-tail-sum cap start step count sigma height index model-error sample-error exp-error))
                   (radius (* 5 (lw-kernel-tail-rectangles start step count (- sigma 2) index 1)))
                   (cap target-error)))
           :in-theory (e/d (lw-mellin-frozen-cutoff)
                           (lw-mellin-frozen-cutoff-valid lw-mellin-tail-cutoff-adequate
                            lw-mellin-tail-coefficient-nonnegative lw-mellin-refined-tail-kernel-bound
                            lw-kernel-tail-rectangles-bound lw-rational-power))
           :nonlinearp nil :do-not-induct t)))

