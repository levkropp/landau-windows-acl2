; Uniform Cauchy extraction from shifted Euler polynomial models.
; The boundary checks are proved for every sample, not supplied as hypotheses.
(in-package "ACL2")
(include-book "euler-shifted-polynomial")

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
(local (in-theory (disable lw-euler-shifted-polynomial lw-complex-euler-polynomial-coefficient
 lw-euler-coefficient-polynomial lw-complex-coefficient-at lw-polynomial-rescale lw-complex-power)))

(local (defthm lw-esc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esc-times-negative (a b) (b a)))
                 :in-theory (disable lw-esc-times-negative)))))

(local (defthm lw-esc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esc-left-commutes)))))

(local (defthm lw-esc-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-esc-scaled-unit-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point 1) (natp power))
  (lw-complex-diskp (lw-complex-scale radius (lw-complex-power point power)) radius))
 :hints (("Goal"
  :use ((:instance lw-complex-unit-power (index power))
        (:instance lw-complex-scale-disk (point (lw-complex-power point power)) (factor radius) (radius 1)))
  :in-theory (union-theories
   '(abs lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defun lw-esc-countdown (samples)
 (declare (xargs :measure (nfix samples)))
 (if (zp samples) 0 (lw-esc-countdown (- samples 1)))))

(defun lw-complex-euler-shifted-polynomial-coefficient
 (rate height outer-radius center radius target index error)
 (lw-complex-coefficient-at
  (lw-polynomial-rescale
   (lw-euler-shifted-polynomial rate height outer-radius center target error)
   radius 0) index 0))

(local (in-theory (disable lw-complex-euler-shifted-polynomial-coefficient)))

(defthm lw-complex-euler-shifted-polynomial-coefficient-rational
 (implies (and (rationalp rate) (rationalp height)
  (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
  (lw-complexp center) (rationalp radius)
  (natp target) (natp index) (rationalp error) (< 0 error))
 (lw-complexp (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius target index error)))
 :hints (("Goal"
 :use (lw-euler-shifted-polynomial-valid
  (:instance lw-polynomial-rescale-valid
   (coefficients (lw-euler-shifted-polynomial rate height outer-radius center target error)) (factor radius) (offset 0))
  (:instance lw-complex-coefficient-at-rational
   (coefficients (lw-polynomial-rescale (lw-euler-shifted-polynomial rate height outer-radius center target error) radius 0)) (target index) (offset 0)))
 :in-theory (union-theories
 '(lw-complex-euler-shifted-polynomial-coefficient lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-euler-shifted-comparison-count (rate height outer-radius center radius left-target right-target index left-error right-error)
 (+ 1 (max (nfix index) (max (len (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)) (len (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error))))))

(defun lw-euler-shifted-comparison-polynomial (rate height outer-radius center radius left-target right-target index left-error right-error)
 (lw-polynomial-disk-difference (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error) (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error) radius (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)))

(local (in-theory (disable lw-euler-shifted-comparison-count lw-euler-shifted-comparison-polynomial)))

(defthm lw-euler-shifted-comparison-data
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (rationalp radius) (< 0 radius) (<= radius outer-radius)
 (lw-complex-diskp center (- outer-radius radius))
 (natp left-target) (natp right-target) (natp index)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (and (posp (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)) (< index (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)) (<= (len (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)) (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)) (<= (len (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error)) (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error))
  (lw-complex-coefficientsp (lw-euler-shifted-comparison-polynomial rate height outer-radius center radius left-target right-target index left-error right-error)) (equal (len (lw-euler-shifted-comparison-polynomial rate height outer-radius center radius left-target right-target index left-error right-error)) (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-shifted-center-data (:instance lw-euler-shifted-polynomial-valid (target left-target) (error left-error)) (:instance lw-euler-uniform-polynomial-valid (rate (+ rate (car center))) (height (+ height (cdr center))) (target right-target) (error right-error))
  (:instance lw-esc-length-natural (coefficients (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)))
  (:instance lw-esc-length-natural (coefficients (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error)))
  (:instance lw-polynomial-disk-difference-valid (left (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)) (right (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error)) (count (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error))))
 :in-theory (union-theories
 '(lw-euler-shifted-comparison-count lw-euler-shifted-comparison-polynomial nfix max lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-shifted-coefficient-boundary-check
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (rationalp radius) (< 0 radius) (<= radius outer-radius)
 (lw-complex-diskp center (- outer-radius radius))
 (natp left-target) (natp right-target) (natp index)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (lw-complex-diskp point 1) (natp samples))
 (lw-cauchy-boundary-check (lw-euler-shifted-comparison-polynomial rate height outer-radius center radius left-target right-target index left-error right-error) point 0 samples (+ left-error right-error)))
 :hints (("Goal" :induct (lw-esc-countdown samples)
 :in-theory (union-theories
 '((:induction lw-esc-countdown) lw-cauchy-boundary-check lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))
 (and stable-under-simplificationp
 '(:use (lw-euler-shifted-center-data lw-euler-shifted-comparison-data (:instance lw-euler-shifted-polynomial-valid (target left-target) (error left-error)) (:instance lw-euler-uniform-polynomial-valid (rate (+ rate (car center))) (height (+ height (cdr center))) (target right-target) (error right-error))
  (:instance lw-complex-unit-power (index (- samples 1)))
  (:instance lw-complex-disk-data (radius 1))
  (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
  (:instance lw-esc-scaled-unit-point (power (- samples 1)))
  (:instance lw-polynomial-disk-difference-evaluation
   (left (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)) (right (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error)) (count (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)) (point (lw-complex-power point (- samples 1))))
  (:instance lw-complex-euler-shifted-polynomial-comparison
   (point (lw-complex-scale radius (lw-complex-power point (- samples 1))))))
 :in-theory (union-theories
 '(lw-euler-shifted-comparison-polynomial lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))))

(defthm lw-complex-euler-shifted-coefficient-with-margin
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (rationalp radius) (< 0 radius) (<= radius outer-radius)
 (lw-complex-diskp center (- outer-radius radius))
 (natp left-target) (natp right-target) (natp index)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius left-target index left-error) (lw-complex-euler-polynomial-coefficient (+ rate (car center)) (+ height (cdr center)) radius right-target index right-error)) (+ left-error right-error margin)))
 :hints (("Goal"
 :use (lw-euler-shifted-center-data lw-euler-shifted-comparison-data (:instance lw-euler-shifted-polynomial-valid (target left-target) (error left-error)) (:instance lw-euler-uniform-polynomial-valid (rate (+ rate (car center))) (height (+ height (cdr center))) (target right-target) (error right-error))
  (:instance lw-cauchy-orbit-data (degree (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)))
  (:instance lw-cauchy-coefficient-count-natural (coefficients (lw-euler-shifted-comparison-polynomial rate height outer-radius center radius left-target right-target index left-error right-error)) (degree (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)) (error margin))
  (:instance lw-euler-shifted-coefficient-boundary-check
   (point (lw-cauchy-orbit-rotation (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)))
   (samples (lw-cauchy-coefficient-count (lw-euler-shifted-comparison-polynomial rate height outer-radius center radius left-target right-target index left-error right-error) (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error) margin)))
  (:instance lw-cauchy-finite-coefficient-bound
   (coefficients (lw-euler-shifted-comparison-polynomial rate height outer-radius center radius left-target right-target index left-error right-error)) (degree (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error)) (target index) (error margin) (cap (+ left-error right-error)))
  (:instance lw-polynomial-disk-difference-coefficient (left (lw-euler-shifted-polynomial rate height outer-radius center left-target left-error)) (right (lw-euler-uniform-polynomial (+ rate (car center)) (+ height (cdr center)) radius right-target right-error)) (count (lw-euler-shifted-comparison-count rate height outer-radius center radius left-target right-target index left-error right-error))))
 :in-theory (union-theories
 '(lw-euler-shifted-comparison-polynomial lw-euler-coefficient-polynomial lw-complex-euler-polynomial-coefficient lw-complex-euler-shifted-polynomial-coefficient lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-shifted-coefficient-comparison
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (rationalp radius) (< 0 radius) (<= radius outer-radius)
 (lw-complex-diskp center (- outer-radius radius))
 (natp left-target) (natp right-target) (natp index)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius left-target index left-error) (lw-complex-euler-polynomial-coefficient (+ rate (car center)) (+ height (cdr center)) radius right-target index right-error)) (+ left-error right-error)))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius left-target index left-error) (lw-complex-euler-polynomial-coefficient (+ rate (car center)) (+ height (cdr center)) radius right-target index right-error)) (+ left-error right-error)))
 :use (lw-euler-shifted-center-data
  (:instance lw-complex-euler-shifted-polynomial-coefficient-rational (target left-target) (error left-error))
  (:instance lw-euler-polynomial-coefficient-rational (rate (+ rate (car center))) (height (+ height (cdr center))) (target right-target) (error right-error))
  (:instance lw-complex-operations-rational (left (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius left-target index left-error)) (right (lw-complex-euler-polynomial-coefficient (+ rate (car center)) (+ height (cdr center)) radius right-target index right-error)) (factor 1))
  (:instance lw-complex-disk-gap-refinement-excludes
   (point (lw-complex-sub (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius left-target index left-error) (lw-complex-euler-polynomial-coefficient (+ rate (car center)) (+ height (cdr center)) radius right-target index right-error))) (radius (+ left-error right-error)) (cost 1))
  (:instance lw-complex-euler-shifted-coefficient-with-margin
   (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius left-target index left-error) (lw-complex-euler-polynomial-coefficient (+ rate (car center)) (+ height (cdr center)) radius right-target index right-error)) (+ left-error right-error) 1))))
 :in-theory (union-theories
 '( lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(local (defthm lw-esc-unscale-difference
 (implies (and (lw-complexp left) (lw-complexp right) (rationalp radius) (not (equal radius 0)))
  (equal
   (lw-complex-scale (/ radius) (lw-complex-sub (lw-complex-scale radius left) (lw-complex-scale radius right)))
   (lw-complex-sub left right)))
 :hints (("Goal"
  :use ((:instance lw-esc-inverse-factor (divisor radius) (coefficient (- (car left) (car right))))
        (:instance lw-esc-inverse-factor (divisor radius) (coefficient (- (cdr left) (cdr right)))))
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))


(defthm lw-complex-euler-shifted-local-coefficient-comparison
 (implies (and (rationalp rate) (rationalp height)
  (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
  (rationalp radius) (< 0 radius) (<= radius outer-radius)
  (lw-complex-diskp center (- outer-radius radius))
  (natp target) (natp index) (rationalp error) (< 0 error)
  (rationalp coefficient-error) (< 0 coefficient-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-coefficient-at (lw-euler-shifted-polynomial rate height outer-radius center target error) index 0) (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) radius index coefficient-error))
  (+ (* error (/ (lw-rational-power radius index))) coefficient-error)))
 :hints (("Goal"
 :use (lw-euler-shifted-center-data lw-euler-shifted-polynomial-valid
  (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-shifted-polynomial rate height outer-radius center target error)) (target index) (offset 0))
  (:instance lw-complex-euler-local-coefficient-rational
   (rate (+ rate (car center))) (height (+ height (cdr center))) (error coefficient-error))
  (:instance lw-euler-local-coefficient-request-valid (error coefficient-error))
  (:instance lw-complex-euler-local-coefficient-identity
   (rate (+ rate (car center))) (height (+ height (cdr center))) (error coefficient-error))
  (:instance lw-complex-euler-polynomial-coefficient-scaling
   (rate (+ rate (car center))) (height (+ height (cdr center))) (target index) (error (lw-euler-local-coefficient-request radius index coefficient-error)))
  (:instance lw-polynomial-rescale-coefficient (coefficients (lw-euler-shifted-polynomial rate height outer-radius center target error)) (factor radius) (offset 0) (target index))
  (:instance lw-complex-euler-shifted-coefficient-comparison
   (left-target target) (right-target index) (left-error error) (right-error (lw-euler-local-coefficient-request radius index coefficient-error)))
  (:instance lw-reciprocal-positive (value (lw-rational-power radius index)))
  (:instance lw-complex-scale-disk
   (point (lw-complex-sub (lw-complex-euler-shifted-polynomial-coefficient rate height outer-radius center radius target index error) (lw-complex-euler-polynomial-coefficient (+ rate (car center)) (+ height (cdr center)) radius index index (lw-euler-local-coefficient-request radius index coefficient-error)))) (factor (/ (lw-rational-power radius index))) (radius (+ error (lw-euler-local-coefficient-request radius index coefficient-error))))
  (:instance lw-esc-unscale-difference (left (lw-complex-coefficient-at (lw-euler-shifted-polynomial rate height outer-radius center target error) index 0)) (right (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) radius index coefficient-error)) (radius (lw-rational-power radius index)))
  (:instance lw-complex-disk-enlarge
   (point (lw-complex-sub (lw-complex-coefficient-at (lw-euler-shifted-polynomial rate height outer-radius center target error) index 0) (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) radius index coefficient-error)))
   (radius (* (/ (lw-rational-power radius index)) (+ error (lw-euler-local-coefficient-request radius index coefficient-error))))
   (cap (+ (* error (/ (lw-rational-power radius index))) coefficient-error))))
 :in-theory (union-theories
 '(lw-complex-euler-shifted-polynomial-coefficient abs lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))


