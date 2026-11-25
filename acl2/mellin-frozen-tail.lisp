(in-package "ACL2")

(include-book "signal-exponential-growth")
(include-book "mellin-window")

; Transfer the frozen signal family to the actual Mellin sampler.
; Its global growth gives a mass-five kernel tail, independent of the
; prime truncation, construction interval and positive point precision.

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

(local (defthm lw-mft-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mft-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mft-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-mft-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mft-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-mft-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mft-left-commutes)))))
(local (defthm lw-mft-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mft-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mft-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-mft-sum-error
         (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- c d)) other-radius))
                  (<= (abs (- (+ a c) (+ b d))) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= c d)))) :rule-classes nil))
(local (defthm lw-mft-weighted-error
         (implies
          (and (rationalp a) (rationalp b) (rationalp weight) (<= 0 weight)
               (rationalp index) (< 0 index) (<= weight index)
               (rationalp radius) (<= 0 radius) (<= (abs (- a b)) (* radius (/ index))))
          (<= (abs (- (* weight a) (* weight b))) radius))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x index))
                        (:instance lw-mft-multiply-order
                          (a (abs (- a b))) (b (* radius (/ index))) (factor weight))
                        (:instance lw-mft-multiply-order
                          (a weight) (b index) (factor (* radius (/ index)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))



(defun lw-mellin-frozen-sample (cap value sigma height index step model-error sample-error)
  (lw-complex-scale
    (* (lw-signal-exponential-value cap value model-error)
       (lw-mellin-weight value sigma index step sample-error))
    (lw-mellin-phase value sigma height index step sample-error)))

(defthm lw-mellin-frozen-sample-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step)
                (rationalp model-error) (< 0 model-error)
                (rationalp sample-error) (< 0 sample-error))
           (lw-complexp (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error)))
  :hints (("Goal"
           :use ((:instance lw-signal-exponential-global-rational (error model-error))
                 (:instance lw-mellin-weight-bounded (error sample-error))
                 (:instance lw-mellin-phase-rational (error sample-error)))
           :in-theory (disable lw-signal-exponential-global-rational lw-mellin-weight-bounded
                               lw-mellin-phase-rational)
           :do-not-induct t)))

(local (defthm lw-mft-sample-difference
         (implies (and (rationalp a) (rationalp b) (rationalp weight) (lw-complexp phase))
                  (equal
                   (lw-complex-sub (lw-complex-scale (* a weight) phase) (lw-complex-scale (* b weight) phase))
                   (lw-complex-scale (* weight (- a b)) phase)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mft-scaled-error
         (implies (and (rationalp a) (rationalp b) (rationalp weight) (<= 0 weight)
                       (rationalp radius) (<= (abs (- a b)) radius))
                  (<= (abs (* weight (- a b))) (* weight radius)))
         :hints (("Goal"
                  :use ((:instance lw-mft-multiply-order (a (- a b)) (b radius) (factor weight))
                        (:instance lw-mft-multiply-order (a (- b a)) (b radius) (factor weight)))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defthm lw-mellin-frozen-sample-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step)
                (rationalp model-error) (< 0 model-error)
                (rationalp sample-error) (< 0 sample-error))
           (lw-complex-diskp
            (lw-complex-sub
              (lw-mellin-sample value sigma height index step sample-error)
              (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error))
            (* (lw-mellin-weight value sigma index step sample-error)
               (+ (lw-mellin-signal-error value sigma index step sample-error) model-error))))
  :hints (("Goal"
           :use ((:instance lw-mellin-error-budgets (error sample-error))
                 (:instance lw-mellin-signal-bounded (error sample-error))
                 (:instance lw-mellin-weight-bounded (error sample-error))
                 (:instance lw-mellin-phase-unit (error sample-error))
                 (:instance lw-signal-exponential-global-rational (error model-error))
                 (:instance lw-signal-exponential-independent-error
                   (error model-error) (signal-error (lw-mellin-signal-error value sigma index step sample-error)))
                 (:instance lw-mft-sample-difference
                   (a (lw-mellin-signal value sigma index step sample-error))
                   (b (lw-signal-exponential-value cap value model-error))
                   (weight (lw-mellin-weight value sigma index step sample-error))
                   (phase (lw-mellin-phase value sigma height index step sample-error)))
                 (:instance lw-mft-scaled-error
                   (a (lw-mellin-signal value sigma index step sample-error))
                   (b (lw-signal-exponential-value cap value model-error))
                   (radius (+ (lw-mellin-signal-error value sigma index step sample-error) model-error))
                   (weight (lw-mellin-weight value sigma index step sample-error)))
                 (:instance lw-complex-scale-disk
                   (point (lw-mellin-phase value sigma height index step sample-error)) (radius 1)
                   (factor (* (lw-mellin-weight value sigma index step sample-error)
                              (- (lw-mellin-signal value sigma index step sample-error)
                                 (lw-signal-exponential-value cap value model-error)))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-sample value sigma height index step sample-error)
                     (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error)))
                   (radius (abs (* (lw-mellin-weight value sigma index step sample-error)
                                   (- (lw-mellin-signal value sigma index step sample-error)
                                      (lw-signal-exponential-value cap value model-error)))))
                   (cap (* (lw-mellin-weight value sigma index step sample-error)
                           (+ (lw-mellin-signal-error value sigma index step sample-error) model-error)))))
           :in-theory
           (e/d (lw-mellin-sample lw-mellin-signal)
                (lw-mellin-error-budgets lw-mellin-signal-bounded lw-mellin-weight-bounded
                 lw-mellin-phase-unit lw-signal-exponential-global-rational
                 lw-signal-exponential-independent-error lw-complex-scale-disk lw-mft-sample-difference))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-frozen-sample-kernel-bound
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp sigma) (<= 2 sigma) (rationalp height) (rationalp step) (<= 0 step)
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp sample-error) (< 0 sample-error))
           (lw-complex-diskp
            (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error)
            (* 5 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error)))))
  :hints (("Goal"
           :use ((:instance lw-signal-exponential-global-rational (error model-error))
                 (:instance lw-signal-exponential-uniform-growth (error model-error))
                 (:instance lw-signal-exponential-parameters (error model-error))
                 (:instance lw-exp-bounds-valid
                   (epsilon (lw-signal-exponential-precision cap model-error)))
                 (:instance lw-mellin-error-budgets (error sample-error))
                 (:instance lw-mellin-weight-bounded (error sample-error))
                 (:instance lw-mellin-phase-unit (error sample-error))
                 (:instance lw-kernel-weight-bounds-valid
                   (error (lw-mellin-kernel-error value sample-error)))
                 (:instance lw-kernel-weight-bounds-valid (sigma (- sigma 2)) (error shifted-error))
                 (:instance lw-kernel-lower-quadratic-shift
                   (signal-error (lw-signal-exponential-precision cap model-error))
                   (kernel-error (lw-mellin-kernel-error value sample-error)))
                 (:instance lw-mft-multiply-order
                   (a (abs (lw-signal-exponential-value cap value model-error)))
                   (b (* 5 (car (lw-exp-bounds value (lw-signal-exponential-precision cap model-error)))
                           (car (lw-exp-bounds value (lw-signal-exponential-precision cap model-error)))))
                   (factor (lw-mellin-weight value sigma index step sample-error)))
                 (:instance lw-complex-scale-disk
                   (point (lw-mellin-phase value sigma height index step sample-error)) (radius 1)
                   (factor (* (lw-signal-exponential-value cap value model-error)
                              (lw-mellin-weight value sigma index step sample-error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error))
                   (radius (abs (* (lw-signal-exponential-value cap value model-error)
                                   (lw-mellin-weight value sigma index step sample-error))))
                   (cap (* 5 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error))))))
           :in-theory
           (e/d (lw-mellin-weight lw-intervalp)
                (lw-signal-exponential-global-rational lw-signal-exponential-uniform-growth
                 lw-signal-exponential-parameters lw-mellin-error-budgets lw-mellin-weight-bounded
                 lw-mellin-phase-unit lw-kernel-weight-bounds-valid lw-kernel-lower-quadratic-shift
                 lw-complex-scale-disk))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-mellin-frozen-sample lw-kernel-tail-rectangles lw-mellin-tail-cutoff
                 lw-mellin-tail-coefficient)))

(defun lw-mellin-frozen-tail-sum (cap start step count sigma height index model-error sample-error)
  (declare (xargs :measure (nfix count)))
  (if (zp count) (cons 0 0)
    (lw-complex-add (lw-mellin-frozen-sample cap start sigma height index step model-error sample-error) (lw-mellin-frozen-tail-sum cap (+ start step) step (- count 1) sigma height index model-error sample-error))))

(local (defthm lw-mft-tail-zero
         (equal (lw-mellin-frozen-tail-sum cap start step 0 sigma height index model-error sample-error) (cons 0 0))
         :hints (("Goal" :expand ((lw-mellin-frozen-tail-sum cap start step 0 sigma height index model-error sample-error))))))

(local (defthm lw-mft-kernel-tail-zero
         (equal (lw-kernel-tail-rectangles start step 0 rate index error) 0)
         :hints (("Goal" :expand ((lw-kernel-tail-rectangles start step 0 rate index error))))))

(local (defthm lw-mft-zero-disk
         (lw-complex-diskp (cons 0 0) 0)
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-mellin-frozen-tail-sum-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
                (rationalp step) (<= 0 step) (natp count) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp model-error) (< 0 model-error)
                (rationalp sample-error) (< 0 sample-error))
           (lw-complexp
            (lw-mellin-frozen-tail-sum cap start step count sigma height index model-error sample-error)))
  :hints (("Goal" :induct
                   (lw-mellin-frozen-tail-sum cap start step count sigma height index model-error sample-error))))

(defthm lw-mellin-frozen-tail-kernel-bound
  (implies (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
                (rationalp step) (<= 0 step) (natp count) (rationalp sigma) (<= 2 sigma)
                (rationalp height) (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp sample-error) (< 0 sample-error))
           (lw-complex-diskp
            (lw-mellin-frozen-tail-sum cap start step count sigma height index model-error sample-error)
            (* 5 (lw-kernel-tail-rectangles start step count (- sigma 2) index shifted-error))))
  :hints
  (("Goal" :induct
             (lw-mellin-frozen-tail-sum cap start step count sigma height index model-error sample-error)
           :in-theory (disable (:definition lw-mellin-frozen-tail-sum)))
   (and stable-under-simplificationp
        '(:use ((:instance lw-mellin-frozen-sample-kernel-bound (value start))
                (:instance lw-complex-add-disk
                  (left (lw-mellin-frozen-sample cap start sigma height index step model-error sample-error))
                  (radius (* 5 (cdr (lw-kernel-weight-bounds start (- sigma 2) index step shifted-error))))
                  (right (lw-mellin-frozen-tail-sum cap (+ start step) step (- count 1) sigma height index model-error sample-error))
                  (other-radius (* 5 (lw-kernel-tail-rectangles (+ start step) step (- count 1)
                                       (- sigma 2) index shifted-error)))))
          :expand ((lw-mellin-frozen-tail-sum cap start step count sigma height index model-error sample-error)
                   (lw-kernel-tail-rectangles start step count (- sigma 2) index shifted-error))
          :in-theory (disable lw-mellin-frozen-sample-kernel-bound lw-complex-add-disk)
          :nonlinearp nil :do-not-induct t))))

(defun lw-mellin-frozen-cutoff (sigma index target-error)
  (lw-mellin-tail-cutoff (- sigma 2) index 5 target-error))

(defthm lw-mellin-frozen-cutoff-valid
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp target-error) (< 0 target-error))
           (and (rationalp (lw-mellin-frozen-cutoff sigma index target-error))
                (< 0 (lw-mellin-frozen-cutoff sigma index target-error))
                (<= (+ 2 (nfix index)) (* (- sigma 2) (lw-mellin-frozen-cutoff sigma index target-error)))))
  :hints (("Goal" :use ((:instance lw-mellin-tail-cutoff-adequate
                         (rate (- sigma 2)) (mass 5) (error target-error)))
                   :in-theory (disable lw-mellin-tail-cutoff-adequate))))

(local (in-theory (disable lw-mellin-frozen-cutoff)))

(defthm lw-mellin-frozen-tail-at-cutoff
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
                (natp index) (natp count) (rationalp target-error) (< 0 target-error)
                (rationalp step) (< 0 step) (<= step (lw-mellin-frozen-cutoff sigma index target-error))
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp sample-error) (< 0 sample-error))
           (lw-complex-diskp
            (lw-mellin-frozen-tail-sum cap (lw-mellin-frozen-cutoff sigma index target-error) step count
              sigma height index model-error sample-error)
            target-error))
  :hints (("Goal"
           :use (lw-mellin-frozen-cutoff-valid
                 (:instance lw-mellin-frozen-tail-kernel-bound
                   (start (lw-mellin-frozen-cutoff sigma index target-error)) (shifted-error 1))
                 (:instance lw-kernel-tail-rectangles-at-cutoff (rate (- sigma 2)) (mass 5) (error 1))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-frozen-tail-sum cap (lw-mellin-frozen-cutoff sigma index target-error) step count
                            sigma height index model-error sample-error))
                   (radius (* 5 (lw-kernel-tail-rectangles (lw-mellin-frozen-cutoff sigma index target-error)
                                  step count (- sigma 2) index 1)))
                   (cap target-error)))
           :in-theory (e/d (lw-mellin-frozen-cutoff)
                           (lw-mellin-frozen-cutoff-valid lw-mellin-frozen-tail-kernel-bound
                            lw-kernel-tail-rectangles-at-cutoff
                            lw-mellin-frozen-tail-sum))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mft-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))

(defun lw-mellin-frozen-grid-count (sigma index target-error end mesh)
  (let ((start (lw-mellin-frozen-cutoff sigma index target-error)))
    (+ 1 (lw-precision-fuel (- end start) (min start mesh)))))

(defun lw-mellin-frozen-grid-step (sigma index target-error end mesh)
  (/ (- end (lw-mellin-frozen-cutoff sigma index target-error))
     (lw-mellin-frozen-grid-count sigma index target-error end mesh)))

(defun lw-mellin-frozen-computed-tail (cap end mesh sigma height index model-error sample-error target-error)
  (lw-mellin-frozen-tail-sum cap (lw-mellin-frozen-cutoff sigma index target-error)
    (lw-mellin-frozen-grid-step sigma index target-error end mesh)
    (lw-mellin-frozen-grid-count sigma index target-error end mesh)
    sigma height index model-error sample-error))

(defthm lw-mellin-frozen-grid-count-natural
  (posp (lw-mellin-frozen-grid-count sigma index target-error end mesh))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-mft-grid-scalar
         (implies (and (rationalp width) (< 0 width) (rationalp start) (< 0 start)
                       (rationalp mesh) (< 0 mesh) (posp count)
                       (<= width (* count (min start mesh))))
                  (let ((step (/ width count)))
                    (and (rationalp step) (< 0 step) (equal (* count step) width)
                         (<= step start) (<= step mesh))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x count))
                        (:instance lw-mft-positive-product (a width) (b (/ count)))
                        (:instance lw-positive-division-bound (numerator width) (divisor count) (bound (min start mesh))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-frozen-grid-parameters
  (implies
   (and (rationalp sigma) (< 2 sigma) (rationalp target-error) (< 0 target-error)
        (rationalp end) (< (lw-mellin-frozen-cutoff sigma index target-error) end)
        (rationalp mesh) (< 0 mesh))
   (let ((start (lw-mellin-frozen-cutoff sigma index target-error))
         (count (lw-mellin-frozen-grid-count sigma index target-error end mesh))
         (step (lw-mellin-frozen-grid-step sigma index target-error end mesh)))
     (and (posp count) (rationalp step) (< 0 step) (equal (+ start (* count step)) end)
          (<= step start) (<= step mesh))))
  :hints (("Goal"
           :use (lw-mellin-frozen-cutoff-valid lw-mellin-frozen-grid-count-natural
                 (:instance lw-precision-fuel-adequate
                   (width (- end (lw-mellin-frozen-cutoff sigma index target-error)))
                   (epsilon (min (lw-mellin-frozen-cutoff sigma index target-error) mesh)))
                 (:instance lw-mft-grid-scalar
                   (width (- end (lw-mellin-frozen-cutoff sigma index target-error)))
                   (start (lw-mellin-frozen-cutoff sigma index target-error))
                   (count (lw-mellin-frozen-grid-count sigma index target-error end mesh))))
           :in-theory
           (e/d (lw-mellin-frozen-grid-count lw-mellin-frozen-grid-step)
                (lw-mellin-frozen-cutoff-valid lw-mellin-frozen-grid-count-natural lw-precision-fuel
                 lw-precision-fuel-adequate))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-mellin-frozen-grid-count lw-mellin-frozen-grid-step lw-mellin-frozen-tail-sum)))

(defthm lw-mellin-frozen-computed-tail-rational
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
        (rationalp target-error) (< 0 target-error) (natp index)
        (rationalp end) (< (lw-mellin-frozen-cutoff sigma index target-error) end)
        (rationalp mesh) (< 0 mesh) (rationalp model-error) (< 0 model-error)
        (rationalp sample-error) (< 0 sample-error))
   (lw-complexp (lw-mellin-frozen-computed-tail cap end mesh sigma height index model-error sample-error target-error)))
  :hints (("Goal"
           :use (lw-mellin-frozen-cutoff-valid lw-mellin-frozen-grid-parameters)
           :in-theory (disable lw-mellin-frozen-cutoff-valid lw-mellin-frozen-grid-parameters)
           :do-not-induct t)))

(defthm lw-mellin-frozen-computed-tail-bound
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
        (rationalp target-error) (< 0 target-error) (natp index)
        (rationalp end) (< (lw-mellin-frozen-cutoff sigma index target-error) end)
        (rationalp mesh) (< 0 mesh) (rationalp model-error) (< 0 model-error) (<= model-error 1)
        (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-mellin-frozen-computed-tail cap end mesh sigma height index model-error sample-error target-error)
    target-error))
  :hints (("Goal"
           :use (lw-mellin-frozen-grid-parameters
                 (:instance lw-mellin-frozen-tail-at-cutoff
                   (count (lw-mellin-frozen-grid-count sigma index target-error end mesh))
                   (step (lw-mellin-frozen-grid-step sigma index target-error end mesh))))
           :in-theory (disable lw-mellin-frozen-grid-parameters lw-mellin-frozen-tail-at-cutoff)
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mft-coefficient-five
         (equal (lw-mellin-tail-coefficient rate index 5)
                (* 5 (lw-mellin-tail-coefficient rate index 1)))
         :hints (("Goal" :in-theory (e/d (lw-mellin-tail-coefficient) (lw-rational-power))))))

(defthm lw-mellin-frozen-tail-after-cutoff
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height)
        (natp index) (natp count) (rationalp target-error) (< 0 target-error)
        (rationalp start) (<= (lw-mellin-frozen-cutoff sigma index target-error) start)
        (rationalp step) (< 0 step) (<= step start)
        (rationalp model-error) (< 0 model-error) (<= model-error 1)
        (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-mellin-frozen-tail-sum cap start step count sigma height index model-error sample-error)
    target-error))
  :hints (("Goal"
           :use (lw-mellin-frozen-cutoff-valid
                 (:instance lw-mellin-tail-cutoff-adequate (rate (- sigma 2)) (mass 5) (error target-error))
                 (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                 (:instance lw-mft-multiply-order
                   (a (lw-mellin-frozen-cutoff sigma index target-error)) (b start) (factor (- sigma 2)))
                 (:instance lw-mft-multiply-order
                   (a (lw-mellin-frozen-cutoff sigma index target-error)) (b start) (factor target-error))
                 (:instance lw-mellin-frozen-tail-kernel-bound (shifted-error 1))
                 (:instance lw-kernel-tail-rectangles-bound (rate (- sigma 2)) (error 1))
                 (:instance lw-mft-multiply-order
                   (a (lw-kernel-tail-rectangles start step count (- sigma 2) index 1))
                   (b (/ (* 2 (lw-mellin-tail-coefficient (- sigma 2) index 1)) start)) (factor 5))
                 (:instance lw-positive-division-bound
                   (numerator (* 2 (lw-mellin-tail-coefficient (- sigma 2) index 5))) (divisor start) (bound target-error))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-frozen-tail-sum cap start step count sigma height index model-error sample-error))
                   (radius (* 5 (lw-kernel-tail-rectangles start step count (- sigma 2) index 1)))
                   (cap target-error)))
           :in-theory (e/d (lw-mellin-frozen-cutoff)
                           (lw-mellin-frozen-cutoff-valid lw-mellin-tail-cutoff-adequate
                            lw-mellin-tail-coefficient-nonnegative lw-mellin-frozen-tail-kernel-bound
                            lw-kernel-tail-rectangles-bound lw-rational-power))
           :nonlinearp nil :do-not-induct t)))
