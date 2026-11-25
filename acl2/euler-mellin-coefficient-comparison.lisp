; Generate finite Cauchy checks comparing reflected Euler and Mellin coefficients.
(in-package "ACL2")
(include-book "euler-mellin-polynomial-comparison")
(include-book "polynomial-capped-coefficients")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(local (in-theory (disable lw-euler-uniform-polynomial
 lw-complex-euler-continuation-value lw-polynomial-affine
 lw-polynomial-multiply-linear lw-polynomial-add-constant)))
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-mellin-radius
 lw-euler-local-normalized-radius lw-euler-mellin-polynomial lw-mellin-improper-polynomial
 lw-euler-mellin-comparison-error lw-polynomial-disk-difference lw-polynomial-rescale
 lw-complex-polynomial lw-complex-coefficient-at lw-rational-power
 lw-polynomial-cauchy-cap-check lw-polynomial-cap-test-error
 lw-cauchy-coefficient-count lw-cauchy-boundary-check lw-cauchy-orbit-rotation)))
(local (defthm lw-emcc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emcc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emcc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emcc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emcc-times-negative (a b) (b a)))
                 :in-theory (disable lw-emcc-times-negative)))))

(local (defthm lw-emcc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emcc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emcc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emcc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emcc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emcc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emcc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-emcc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emcc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emcc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-emcc-left-commutes)))))
(local (defthm lw-emcc-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-emcc-scaled-unit-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point 1) (natp power))
 (lw-complex-diskp (lw-complex-scale radius (lw-complex-power point power)) radius))
 :hints (("Goal"
 :use ((:instance lw-complex-unit-power (index power))
       (:instance lw-complex-scale-disk (point (lw-complex-power point power)) (factor radius) (radius 1)))
 :in-theory (union-theories
 '(abs lw-emcc-left-commutes lw-emcc-left-distributes lw-emcc-fold-constants lw-emcc-times-negative lw-emcc-negative-times lw-emcc-zero-times lw-emcc-minus-one lw-emcc-double-negative lw-emcc-add-cancel lw-emcc-double lw-emcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defun lw-emcc-countdown (samples)
 (declare (xargs :measure (nfix samples)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp samples) 0 (lw-emcc-countdown (- samples 1)))))
(defun lw-euler-mellin-difference-count (rate height outer-radius anchor-error left-target right-target left-error right-error)
 (+ 1 (max (len (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)) (len (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)))))
(defun lw-euler-mellin-difference-polynomial (rate height outer-radius anchor-error left-target right-target left-error right-error)
 (lw-polynomial-disk-difference (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error) (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) (lw-euler-mellin-radius rate height outer-radius anchor-error) (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)))
(local (in-theory (disable lw-euler-mellin-difference-count lw-euler-mellin-difference-polynomial)))
(defthm lw-euler-mellin-difference-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp left-target) (natp right-target) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (and (posp (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (<= (len (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)) (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (<= (len (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)) (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))
      (lw-complex-coefficientsp (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (equal (len (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-mellin-radius-data
       (:instance lw-euler-mellin-polynomial-valid (target left-target) (error left-error))
       (:instance lw-mellin-improper-polynomial-valid (sigma rate) (target right-target) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (error right-error))
       (:instance lw-emcc-length-natural (coefficients (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)))
       (:instance lw-emcc-length-natural (coefficients (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)))
       (:instance lw-polynomial-disk-difference-valid (left (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (count (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))))
 :in-theory (union-theories
 '(lw-euler-mellin-difference-count lw-euler-mellin-difference-polynomial max lw-emcc-left-commutes lw-emcc-left-distributes lw-emcc-fold-constants lw-emcc-times-negative lw-emcc-negative-times lw-emcc-zero-times lw-emcc-minus-one lw-emcc-double-negative lw-emcc-add-cancel lw-emcc-double lw-emcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-mellin-difference-boundary-check
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (lw-complex-diskp point 1) (natp samples))
 (lw-cauchy-boundary-check (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) point 0 samples (lw-euler-mellin-comparison-error left-error right-error)))
 :hints (("Goal" :induct (lw-emcc-countdown samples)
 :in-theory (union-theories
 '((:induction lw-emcc-countdown) lw-cauchy-boundary-check lw-emcc-left-commutes lw-emcc-left-distributes lw-emcc-fold-constants lw-emcc-times-negative lw-emcc-negative-times lw-emcc-zero-times lw-emcc-minus-one lw-emcc-double-negative lw-emcc-add-cancel lw-emcc-double lw-emcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))
 (and stable-under-simplificationp
 '(:use (lw-euler-mellin-comparison-error-data lw-euler-mellin-radius-data lw-euler-mellin-difference-data
         (:instance lw-euler-mellin-polynomial-valid (target left-target) (error left-error))
         (:instance lw-mellin-improper-polynomial-valid (sigma rate) (target right-target) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (error right-error))
         (:instance lw-complex-unit-power (index (- samples 1)))
         (:instance lw-complex-disk-data (radius 1))
         (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
         (:instance lw-emcc-scaled-unit-point (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (power (- samples 1)))
         (:instance lw-polynomial-disk-difference-evaluation
          (left (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (count (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (point (lw-complex-power point (- samples 1))))
         (:instance lw-complex-euler-mellin-polynomial-comparison
          (point (lw-complex-scale (lw-euler-mellin-radius rate height outer-radius anchor-error) (lw-complex-power point (- samples 1))))))
 :in-theory (union-theories
 '(lw-euler-mellin-difference-polynomial lw-emcc-left-commutes lw-emcc-left-distributes lw-emcc-fold-constants lw-emcc-times-negative lw-emcc-negative-times lw-emcc-zero-times lw-emcc-minus-one lw-emcc-double-negative lw-emcc-add-cancel lw-emcc-double lw-emcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))))
(defthm lw-euler-mellin-difference-coefficient-caps
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-polynomial-coefficient-caps (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (lw-euler-mellin-comparison-error left-error right-error)))
 :hints (("Goal"
 :use (lw-euler-mellin-comparison-error-data lw-euler-mellin-difference-data
       (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (lw-euler-mellin-comparison-error left-error right-error)))
       (:instance lw-cauchy-orbit-data (degree (len (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error))))
       (:instance lw-euler-mellin-difference-boundary-check
        (point (lw-cauchy-orbit-rotation (len (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error))))
        (samples (lw-cauchy-coefficient-count (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (len (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (lw-polynomial-cap-test-error (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (lw-euler-mellin-comparison-error left-error right-error)))))
       (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-mellin-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (lw-euler-mellin-comparison-error left-error right-error))))
 :in-theory (union-theories
 '(lw-polynomial-cauchy-cap-check lw-emcc-left-commutes lw-emcc-left-distributes lw-emcc-fold-constants lw-emcc-times-negative lw-emcc-negative-times lw-emcc-zero-times lw-emcc-minus-one lw-emcc-double-negative lw-emcc-add-cancel lw-emcc-double lw-emcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))


(defthm lw-euler-mellin-coefficient-gains-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp index))
 (and (rationalp (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)) (< 0 (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)) (rationalp (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index))) (< 0 (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)))
      (rationalp (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (< 0 (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (rationalp (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))) (< 0 (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))))
 :hints (("Goal"
 :use (lw-euler-mellin-radius-data
       (:instance lw-rational-power-rational (base (lw-euler-mellin-radius rate height outer-radius anchor-error)) (exponent index))
       (:instance lw-rational-power-positive (base (lw-euler-mellin-radius rate height outer-radius anchor-error)) (exponent index))
       (:instance lw-rational-power-rational (base (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (exponent index))
       (:instance lw-rational-power-positive (base (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (exponent index))
       (:instance lw-reciprocal-positive (value (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)))
       (:instance lw-reciprocal-positive (value (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))))
 :in-theory (union-theories
 '( lw-emcc-left-commutes lw-emcc-left-distributes lw-emcc-fold-constants lw-emcc-times-negative lw-emcc-negative-times lw-emcc-zero-times lw-emcc-minus-one lw-emcc-double-negative lw-emcc-add-cancel lw-emcc-double lw-emcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-mellin-polynomial-coefficient-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp left-target) (natp right-target) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (natp index))
 (lw-complex-diskp (lw-complex-sub (lw-complex-coefficient-at (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error) index 0) (lw-complex-coefficient-at (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) index 0)) (* (lw-euler-mellin-comparison-error left-error right-error) (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)))))
 :hints (("Goal"
 :use (lw-euler-mellin-radius-data lw-euler-mellin-coefficient-gains-data
       lw-euler-mellin-difference-data lw-euler-mellin-difference-coefficient-caps lw-euler-mellin-comparison-error-data
       (:instance lw-euler-mellin-polynomial-valid (target left-target) (error left-error))
       (:instance lw-mellin-improper-polynomial-valid (sigma rate) (target right-target) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (error right-error))
       (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)) (target index) (offset 0))
       (:instance lw-complex-coefficient-at-rational (coefficients (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)) (target index) (offset 0))
       (:instance lw-complex-operations-rational (left (lw-complex-coefficient-at (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error) index 0)) (right (lw-complex-coefficient-at (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) index 0)) (factor 1))
       (:instance lw-polynomial-disk-difference-capped-coefficient (left (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (count (lw-euler-mellin-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (lw-euler-mellin-comparison-error left-error right-error)))
       (:instance lw-emcc-inverse-factor (divisor (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)) (coefficient 1))
       (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-coefficient-at (lw-polynomial-rescale (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error) (lw-euler-mellin-radius rate height outer-radius anchor-error) 0) index 0) (lw-complex-coefficient-at (lw-polynomial-rescale (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) (lw-euler-mellin-radius rate height outer-radius anchor-error) 0) index 0)))
        (factor (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index))) (radius (lw-euler-mellin-comparison-error left-error right-error))))
 :in-theory (union-theories
 '(lw-euler-mellin-difference-polynomial lw-polynomial-rescale-coefficient lw-complex-sub-scales lw-complex-scale-compose lw-complex-scale-one lw-complex-scale-rational abs lw-emcc-left-commutes lw-emcc-left-distributes lw-emcc-fold-constants lw-emcc-times-negative lw-emcc-negative-times lw-emcc-zero-times lw-emcc-minus-one lw-emcc-double-negative lw-emcc-add-cancel lw-emcc-double lw-emcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

