; Finite boundary checks bound the normalized evaluator coefficients, including one.
(in-package "ACL2")
(include-book "euler-local-normalized-model")
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
(local (in-theory (disable lw-euler-local-normalized-polynomial lw-euler-local-normalized-cap
 lw-euler-local-normalized-radius lw-euler-value-clearance-check lw-polynomial-rescale
 lw-polynomial-disk-difference lw-complex-polynomial lw-complex-power
 lw-polynomial-cauchy-cap-check lw-polynomial-cap-test-error
 lw-cauchy-coefficient-count lw-cauchy-boundary-check lw-cauchy-orbit-rotation)))
(local (defthm lw-lnc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lnc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-lnc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-lnc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-lnc-times-negative (a b) (b a)))
                 :in-theory (disable lw-lnc-times-negative)))))

(local (defthm lw-lnc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-lnc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-lnc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-lnc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-lnc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-lnc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-lnc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-lnc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lnc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lnc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-lnc-left-commutes)))))

(local (defthm lw-lnc-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-lnc-scaled-unit-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point 1) (natp power))
 (lw-complex-diskp (lw-complex-scale radius (lw-complex-power point power)) radius))
 :hints (("Goal"
 :use ((:instance lw-complex-unit-power (index power))
       (:instance lw-complex-scale-disk (point (lw-complex-power point power)) (factor radius) (radius 1)))
 :in-theory (union-theories
 '(abs lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defun lw-lnc-countdown (samples)
 (declare (xargs :measure (nfix samples)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp samples) 0 (lw-lnc-countdown (- samples 1)))))

(defun lw-euler-local-normalized-coefficient-polynomial (rate height outer-radius anchor-error target error)
 (lw-polynomial-rescale (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error) (lw-euler-local-normalized-radius rate height outer-radius anchor-error) 0))

(defun lw-euler-local-normalized-difference-count (rate height outer-radius anchor-error left-target right-target left-error right-error)
 (+ 1 (max (len (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)) (len (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)))))

(defun lw-euler-local-normalized-difference-polynomial (rate height outer-radius anchor-error left-target right-target left-error right-error)
 (lw-polynomial-disk-difference (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) (lw-euler-local-normalized-radius rate height outer-radius anchor-error) (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)))

(local (in-theory (disable lw-euler-local-normalized-coefficient-polynomial
 lw-euler-local-normalized-difference-count lw-euler-local-normalized-difference-polynomial)))

(defthm lw-euler-local-normalized-coefficient-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (and (lw-complex-coefficientsp (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (equal (len (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (len (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error)))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data lw-euler-local-normalized-polynomial-valid
       (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error)) (factor (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-local-normalized-coefficient-polynomial lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-local-normalized-difference-polynomial-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (and (posp (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (<= (len (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)) (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (<= (len (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)) (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))
      (lw-complex-coefficientsp (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (equal (len (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data
       (:instance lw-euler-local-normalized-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-local-normalized-polynomial-valid (target right-target) (error right-error))
       (:instance lw-lnc-length-natural (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)))
       (:instance lw-lnc-length-natural (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)))
       (:instance lw-polynomial-disk-difference-valid (left (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)) (radius (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (count (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))))
 :in-theory (union-theories
 '(lw-euler-local-normalized-difference-count lw-euler-local-normalized-difference-polynomial max lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-local-normalized-coefficient-boundary-check
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point 1) (natp samples))
 (lw-cauchy-boundary-check (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error) point 0 samples (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
 :hints (("Goal" :induct (lw-lnc-countdown samples)
 :in-theory (union-theories
 '((:induction lw-lnc-countdown) lw-cauchy-boundary-check lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))
 (and stable-under-simplificationp
 '(:use (lw-euler-local-normalized-data
         lw-euler-local-normalized-polynomial-valid
         (:instance lw-complex-unit-power (index (- samples 1)))
         (:instance lw-complex-disk-data (radius 1))
         (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
         (:instance lw-lnc-scaled-unit-point (radius (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (power (- samples 1)))
         (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error))
          (factor (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (offset 0) (point (lw-complex-power point (- samples 1))))
         (:instance lw-complex-euler-local-normalized-polynomial-cap
          (point (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) (lw-complex-power point (- samples 1))))))
 :in-theory (union-theories
 '(lw-euler-local-normalized-coefficient-polynomial lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))))

(defthm lw-euler-local-normalized-difference-boundary-check
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (lw-complex-diskp point 1) (natp samples))
 (lw-cauchy-boundary-check (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) point 0 samples (* 1/2 (+ left-error right-error))))
 :hints (("Goal" :induct (lw-lnc-countdown samples)
 :in-theory (union-theories
 '((:induction lw-lnc-countdown) lw-cauchy-boundary-check lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))
 (and stable-under-simplificationp
 '(:use (lw-euler-local-normalized-data lw-euler-local-normalized-difference-polynomial-data
         (:instance lw-euler-local-normalized-polynomial-valid (target left-target) (error left-error))
         (:instance lw-euler-local-normalized-polynomial-valid (target right-target) (error right-error))
         (:instance lw-complex-unit-power (index (- samples 1)))
         (:instance lw-complex-disk-data (radius 1))
         (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
         (:instance lw-lnc-scaled-unit-point (radius (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (power (- samples 1)))
         (:instance lw-polynomial-disk-difference-evaluation
          (left (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)) (radius (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (count (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (point (lw-complex-power point (- samples 1))))
         (:instance lw-complex-euler-local-normalized-polynomial-cauchy
          (point (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) (lw-complex-power point (- samples 1))))))
 :in-theory (union-theories
 '(lw-euler-local-normalized-difference-polynomial lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))))

(defthm lw-euler-local-normalized-polynomial-coefficient-caps
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (lw-polynomial-coefficient-caps (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error) (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
 :hints (("Goal"
 :use (lw-euler-local-normalized-coefficient-polynomial-valid lw-euler-local-normalized-data
       (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
       (:instance lw-cauchy-orbit-data (degree (len (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error))))
       (:instance lw-euler-local-normalized-coefficient-boundary-check
        (point (lw-cauchy-orbit-rotation (len (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error))))
        (samples (lw-cauchy-coefficient-count (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error) (len (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (lw-polynomial-cap-test-error (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error) (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))))
       (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-local-normalized-cap rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-polynomial-cauchy-cap-check lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-local-normalized-polynomial-difference-coefficient-caps
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-polynomial-coefficient-caps (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-difference-polynomial-data
       (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (* 1/2 (+ left-error right-error))))
       (:instance lw-cauchy-orbit-data (degree (len (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error))))
       (:instance lw-euler-local-normalized-difference-boundary-check
        (point (lw-cauchy-orbit-rotation (len (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error))))
        (samples (lw-cauchy-coefficient-count (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (len (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (lw-polynomial-cap-test-error (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error) (* 1/2 (+ left-error right-error))))))
       (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-local-normalized-difference-polynomial rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (* 1/2 (+ left-error right-error)))))
 :in-theory (union-theories
 '(lw-polynomial-cauchy-cap-check lw-lnc-left-commutes lw-lnc-left-distributes lw-lnc-fold-constants lw-lnc-times-negative lw-lnc-negative-times lw-lnc-zero-times lw-lnc-minus-one lw-lnc-double-negative lw-lnc-add-cancel lw-lnc-double lw-lnc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))
