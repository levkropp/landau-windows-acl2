; Generated finite boundary checks bound every normalized quotient coefficient.
(in-package "ACL2")
(include-book "euler-log-polynomial-cauchy")
(include-book "polynomial-cauchy-caps")
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
(local (in-theory (disable lw-euler-uniform-log-polynomial lw-euler-uniform-log-cap
 lw-euler-neighborhood-radius lw-euler-value-clearance-check lw-polynomial-rescale
 lw-polynomial-disk-difference lw-complex-polynomial lw-complex-power
 lw-polynomial-cauchy-cap-check lw-polynomial-cap-test-error
 lw-cauchy-coefficient-count lw-cauchy-boundary-check lw-cauchy-orbit-rotation)))
(local (defthm lw-lcc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lcc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-lcc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-lcc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-lcc-times-negative (a b) (b a)))
                 :in-theory (disable lw-lcc-times-negative)))))

(local (defthm lw-lcc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-lcc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-lcc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-lcc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-lcc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-lcc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-lcc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-lcc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lcc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lcc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-lcc-left-commutes)))))

(local (defthm lw-lcc-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-lcc-scaled-unit-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point 1) (natp power))
 (lw-complex-diskp (lw-complex-scale radius (lw-complex-power point power)) radius))
 :hints (("Goal"
 :use ((:instance lw-complex-unit-power (index power))
       (:instance lw-complex-scale-disk (point (lw-complex-power point power)) (factor radius) (radius 1)))
 :in-theory (union-theories
 '(abs lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defun lw-lcc-countdown (samples)
 (declare (xargs :measure (nfix samples)))
 (if (zp samples) 0 (lw-lcc-countdown (- samples 1)))))

(defun lw-euler-log-coefficient-polynomial (rate height outer-radius anchor-error target error)
 (lw-polynomial-rescale (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) (lw-euler-neighborhood-radius rate height outer-radius anchor-error) 0))

(defun lw-euler-log-difference-count (rate height outer-radius anchor-error left-target right-target left-error right-error)
 (+ 1 (max (len (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error)) (len (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error)))))

(defun lw-euler-log-difference-polynomial (rate height outer-radius anchor-error left-target right-target left-error right-error)
 (lw-polynomial-disk-difference (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) (lw-euler-neighborhood-radius rate height outer-radius anchor-error) (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)))

(local (in-theory (disable lw-euler-log-coefficient-polynomial
 lw-euler-log-difference-count lw-euler-log-difference-polynomial)))

(defthm lw-euler-log-coefficient-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (and (lw-complex-coefficientsp (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (equal (len (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (len (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-uniform-log-polynomial-valid
       (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)) (factor (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-log-coefficient-polynomial lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-log-difference-polynomial-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (and (posp (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (<= (len (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error)) (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (<= (len (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error)) (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))
      (lw-complex-coefficientsp (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (equal (len (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data
       (:instance lw-euler-uniform-log-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-uniform-log-polynomial-valid (target right-target) (error right-error))
       (:instance lw-lcc-length-natural (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error)))
       (:instance lw-lcc-length-natural (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error)))
       (:instance lw-polynomial-disk-difference-valid (left (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error)) (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (count (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))))
 :in-theory (union-theories
 '(lw-euler-log-difference-count lw-euler-log-difference-polynomial max lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-log-coefficient-boundary-check
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point 1) (natp samples))
 (lw-cauchy-boundary-check (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error) point 0 samples (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
 :hints (("Goal" :induct (lw-lcc-countdown samples)
 :in-theory (union-theories
 '((:induction lw-lcc-countdown) lw-cauchy-boundary-check lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))
 (and stable-under-simplificationp
 '(:use (lw-euler-neighborhood-data
         lw-euler-uniform-log-polynomial-valid
         (:instance lw-complex-unit-power (index (- samples 1)))
         (:instance lw-complex-disk-data (radius 1))
         (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
         (:instance lw-lcc-scaled-unit-point (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (power (- samples 1)))
         (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error))
          (factor (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (offset 0) (point (lw-complex-power point (- samples 1))))
         (:instance lw-complex-euler-uniform-log-polynomial-cap
          (point (lw-complex-scale (lw-euler-neighborhood-radius rate height outer-radius anchor-error) (lw-complex-power point (- samples 1))))))
 :in-theory (union-theories
 '(lw-euler-log-coefficient-polynomial lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))))

(defthm lw-euler-log-difference-boundary-check
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (lw-complex-diskp point 1) (natp samples))
 (lw-cauchy-boundary-check (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) point 0 samples (+ left-error right-error)))
 :hints (("Goal" :induct (lw-lcc-countdown samples)
 :in-theory (union-theories
 '((:induction lw-lcc-countdown) lw-cauchy-boundary-check lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))
 (and stable-under-simplificationp
 '(:use (lw-euler-neighborhood-data lw-euler-log-difference-polynomial-data
         (:instance lw-euler-uniform-log-polynomial-valid (target left-target) (error left-error))
         (:instance lw-euler-uniform-log-polynomial-valid (target right-target) (error right-error))
         (:instance lw-complex-unit-power (index (- samples 1)))
         (:instance lw-complex-disk-data (radius 1))
         (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
         (:instance lw-lcc-scaled-unit-point (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (power (- samples 1)))
         (:instance lw-polynomial-disk-difference-evaluation
          (left (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error)) (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (count (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (point (lw-complex-power point (- samples 1))))
         (:instance lw-complex-euler-log-polynomial-cauchy
          (point (lw-complex-scale (lw-euler-neighborhood-radius rate height outer-radius anchor-error) (lw-complex-power point (- samples 1))))))
 :in-theory (union-theories
 '(lw-euler-log-difference-polynomial lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))))

(defthm lw-euler-log-polynomial-coefficient-caps
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (lw-polynomial-coefficient-caps (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
 :hints (("Goal"
 :use (lw-euler-log-coefficient-polynomial-valid lw-euler-uniform-log-model-data
       (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-cauchy-orbit-data (degree (len (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error))))
       (:instance lw-euler-log-coefficient-boundary-check
        (point (lw-cauchy-orbit-rotation (len (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error))))
        (samples (lw-cauchy-coefficient-count (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error) (len (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (lw-polynomial-cap-test-error (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))))
       (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-polynomial-cauchy-cap-check lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-log-polynomial-difference-coefficient-caps
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-polynomial-coefficient-caps (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (+ left-error right-error)))
 :hints (("Goal"
 :use (lw-euler-log-difference-polynomial-data
       (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (+ left-error right-error)))
       (:instance lw-cauchy-orbit-data (degree (len (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error))))
       (:instance lw-euler-log-difference-boundary-check
        (point (lw-cauchy-orbit-rotation (len (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error))))
        (samples (lw-cauchy-coefficient-count (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (len (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (lw-polynomial-cap-test-error (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (+ left-error right-error)))))
       (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-log-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (+ left-error right-error))))
 :in-theory (union-theories
 '(lw-polynomial-cauchy-cap-check lw-lcc-left-commutes lw-lcc-left-distributes lw-lcc-fold-constants lw-lcc-times-negative lw-lcc-negative-times lw-lcc-zero-times lw-lcc-minus-one lw-lcc-double-negative lw-lcc-add-cancel lw-lcc-double lw-lcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

