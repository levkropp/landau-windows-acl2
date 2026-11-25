(in-package "ACL2")

(include-book "euler-refined-polynomial")
(include-book "euler-local-coefficients")

; Extract coefficients from the same refined polynomial used by the
; native derivative comparison. All boundary checks are constructed.

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

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-euler-uniform-polynomial lw-complex-euler-continuation-value
 lw-polynomial-disk-difference lw-polynomial-pad lw-polynomial-rescale lw-complex-polynomial
 lw-complex-coefficient-at lw-cauchy-boundary-check lw-cauchy-coefficient-count
 lw-cauchy-orbit-rotation lw-complex-power lw-complex-power-scale)))

(local (in-theory (disable lw-euler-coefficient-polynomial lw-complex-euler-polynomial-coefficient
 lw-euler-coefficient-comparison-count lw-euler-coefficient-comparison-polynomial)))

(local (in-theory (disable lw-complex-euler-coefficient-value)))
(local (in-theory (disable lw-euler-refined-polynomial)))

(local (defthm lw-erc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erc-times-negative (a b) (b a)))
                 :in-theory (disable lw-erc-times-negative)))))

(local (defthm lw-erc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erc-left-commutes)))))

(local (defthm lw-erc-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-erc-scaled-unit-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point 1) (natp power))
  (lw-complex-diskp (lw-complex-scale radius (lw-complex-power point power)) radius))
 :hints (("Goal"
  :use ((:instance lw-complex-unit-power (index power))
        (:instance lw-complex-scale-disk (point (lw-complex-power point power)) (factor radius) (radius 1)))
  :in-theory (union-theories
   '(abs lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defun lw-erc-countdown (samples)
 (declare (xargs :measure (nfix samples)))
 (if (zp samples) 0 (lw-erc-countdown (- samples 1)))))

(defun lw-complex-euler-refined-coefficient (rate height radius block request target index error)
 (lw-complex-coefficient-at
  (lw-polynomial-rescale (lw-euler-refined-polynomial rate height radius block request target error) radius 0) index 0))

(local (in-theory (disable lw-complex-euler-refined-coefficient)))

(defthm lw-complex-euler-refined-coefficient-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp request) (< 0 request)
               (natp target) (natp index) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-refined-coefficient rate height radius block request target index error)))
 :hints (("Goal"
  :use (lw-euler-refined-polynomial-valid
        (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-refined-polynomial rate height radius block request target error)) (factor radius) (offset 0))
        (:instance lw-complex-coefficient-at-rational
         (coefficients (lw-polynomial-rescale (lw-euler-refined-polynomial rate height radius block request target error) radius 0)) (target index) (offset 0)))
  :in-theory (union-theories
 '(lw-complex-euler-refined-coefficient lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-refined-comparison-count
 (rate height radius block request left-target right-target index left-error right-error)
 (+ 1 (max (nfix index)
       (max (len (lw-euler-refined-polynomial rate height radius block request left-target left-error)) (len (lw-euler-uniform-polynomial rate height radius right-target right-error))))))

(defun lw-euler-refined-comparison-polynomial
 (rate height radius block request left-target right-target index left-error right-error)
 (lw-polynomial-disk-difference (lw-euler-refined-polynomial rate height radius block request left-target left-error) (lw-euler-uniform-polynomial rate height radius right-target right-error) radius (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)))

(local (in-theory (disable lw-euler-refined-comparison-count lw-euler-refined-comparison-polynomial)))

(defthm lw-euler-refined-comparison-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp request) (< 0 request)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ left-error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block left-error))
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (and (posp (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)) (< index (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)) (<= (len (lw-euler-refined-polynomial rate height radius block request left-target left-error)) (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)) (<= (len (lw-euler-uniform-polynomial rate height radius right-target right-error)) (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error))
       (lw-complex-coefficientsp (lw-euler-refined-comparison-polynomial rate height radius block request left-target right-target index left-error right-error)) (equal (len (lw-euler-refined-comparison-polynomial rate height radius block request left-target right-target index left-error right-error)) (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-euler-refined-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-erc-length-natural (coefficients (lw-euler-refined-polynomial rate height radius block request left-target left-error)))
        (:instance lw-erc-length-natural (coefficients (lw-euler-uniform-polynomial rate height radius right-target right-error)))
        (:instance lw-polynomial-disk-difference-valid (left (lw-euler-refined-polynomial rate height radius block request left-target left-error)) (right (lw-euler-uniform-polynomial rate height radius right-target right-error)) (count (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error))))
  :in-theory (union-theories
   '(lw-euler-refined-comparison-count lw-euler-refined-comparison-polynomial nfix max lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-refined-coefficient-boundary-check
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp request) (< 0 request)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ left-error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block left-error))
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (lw-complex-diskp point 1) (natp samples))
  (lw-cauchy-boundary-check (lw-euler-refined-comparison-polynomial rate height radius block request left-target right-target index left-error right-error) point 0 samples (+ left-error right-error)))
 :hints (("Goal" :induct (lw-erc-countdown samples)
  :in-theory (union-theories
   '((:induction lw-erc-countdown) lw-cauchy-boundary-check lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-euler-refined-comparison-data)
          (:instance lw-euler-refined-polynomial-valid (target left-target) (error left-error))
          (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
          (:instance lw-complex-unit-power (index (- samples 1)))
          (:instance lw-complex-disk-data (radius 1))
          (:instance lw-complex-disk-data
           (point (lw-complex-power point (- samples 1))) (radius 1))
          (:instance lw-erc-scaled-unit-point (power (- samples 1)))
          (:instance lw-polynomial-disk-difference-evaluation
           (left (lw-euler-refined-polynomial rate height radius block request left-target left-error)) (right (lw-euler-uniform-polynomial rate height radius right-target right-error)) (count (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error))
           (point (lw-complex-power point (- samples 1))))
          (:instance lw-complex-euler-refined-uniform-comparison
           (point (lw-complex-scale radius (lw-complex-power point (- samples 1))))))
    :in-theory (union-theories
   '(lw-euler-refined-comparison-polynomial lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
    :nonlinearp nil :do-not-induct t))))

(defthm lw-complex-euler-refined-coefficient-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp request) (< 0 request)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ left-error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block left-error))
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-refined-coefficient rate height radius block request left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error margin)))
 :hints (("Goal"
  :use (lw-euler-refined-comparison-data
        (:instance lw-euler-refined-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-cauchy-orbit-data (degree (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)))
        (:instance lw-cauchy-coefficient-count-natural (coefficients (lw-euler-refined-comparison-polynomial rate height radius block request left-target right-target index left-error right-error)) (degree (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)) (error margin))
        (:instance lw-euler-refined-coefficient-boundary-check
         (point (lw-cauchy-orbit-rotation (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)))
         (samples (lw-cauchy-coefficient-count (lw-euler-refined-comparison-polynomial rate height radius block request left-target right-target index left-error right-error) (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error) margin)))
        (:instance lw-cauchy-finite-coefficient-bound
         (coefficients (lw-euler-refined-comparison-polynomial rate height radius block request left-target right-target index left-error right-error)) (degree (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error)) (target index) (error margin) (cap (+ left-error right-error)))
        (:instance lw-polynomial-disk-difference-coefficient
         (left (lw-euler-refined-polynomial rate height radius block request left-target left-error)) (right (lw-euler-uniform-polynomial rate height radius right-target right-error)) (count (lw-euler-refined-comparison-count rate height radius block request left-target right-target index left-error right-error))))
  :in-theory (union-theories
   '(lw-euler-refined-comparison-polynomial lw-euler-coefficient-polynomial lw-complex-euler-polynomial-coefficient lw-complex-euler-refined-coefficient lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-refined-coefficient-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp request) (< 0 request)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ left-error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block left-error))
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-refined-coefficient rate height radius block request left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-refined-coefficient rate height radius block request left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error)))
  :use ((:instance lw-complex-euler-refined-coefficient-rational (target left-target) (error left-error))
        (:instance lw-euler-polynomial-coefficient-rational (target right-target) (error right-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-refined-coefficient rate height radius block request left-target index left-error)) (right (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-refined-coefficient rate height radius block request left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error))) (radius (+ left-error right-error)) (cost 1))
        (:instance lw-complex-euler-refined-coefficient-with-margin
         (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-refined-coefficient rate height radius block request left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error) 1))))
  :in-theory (union-theories
   '( lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-erc-power-first
 (implies (rationalp radius) (equal (lw-rational-power radius 1) radius))
 :hints (("Goal" :expand ((lw-rational-power radius 1) (lw-rational-power radius 0))
                 :in-theory (enable lw-rational-power)))))

(local (defthm lw-erc-unscale-difference
 (implies (and (lw-complexp left) (lw-complexp right) (rationalp radius) (not (equal radius 0)))
  (equal
   (lw-complex-scale (/ radius) (lw-complex-sub (lw-complex-scale radius left) (lw-complex-scale radius right)))
   (lw-complex-sub left right)))
 :hints (("Goal"
  :use ((:instance lw-erc-inverse-factor (divisor radius) (coefficient (- (car left) (car right))))
        (:instance lw-erc-inverse-factor (divisor radius) (coefficient (- (cdr left) (cdr right)))))
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-complex-euler-refined-first-local-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp request) (< 0 request) (natp target)
               (rationalp error) (< 0 error)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block error))
               (rationalp coefficient-error) (< 0 coefficient-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-coefficient-at (lw-euler-refined-polynomial rate height radius block request target error) 1 0) (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error)) (+ (* error (/ radius)) coefficient-error)))
 :hints (("Goal"
  :use (lw-euler-refined-polynomial-valid
        (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-refined-polynomial rate height radius block request target error)) (target 1) (offset 0))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error coefficient-error))
        (:instance lw-euler-local-coefficient-request-valid (index 1) (error coefficient-error))
        (:instance lw-complex-euler-local-coefficient-identity (index 1) (error coefficient-error))
        (:instance lw-complex-euler-polynomial-coefficient-scaling (target 1) (index 1) (error (lw-euler-local-coefficient-request radius 1 coefficient-error)))
        (:instance lw-polynomial-rescale-coefficient (coefficients (lw-euler-refined-polynomial rate height radius block request target error)) (factor radius) (offset 0) (target 1))
        (:instance lw-complex-euler-refined-coefficient-comparison
         (left-target target) (right-target 1) (index 1) (left-error error) (right-error (lw-euler-local-coefficient-request radius 1 coefficient-error)))
        (:instance lw-reciprocal-positive (value radius))
        (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-euler-refined-coefficient rate height radius block request target 1 error) (lw-complex-euler-polynomial-coefficient rate height radius 1 1 (lw-euler-local-coefficient-request radius 1 coefficient-error)))) (factor (/ radius)) (radius (+ error (lw-euler-local-coefficient-request radius 1 coefficient-error))))
        (:instance lw-erc-unscale-difference (left (lw-complex-coefficient-at (lw-euler-refined-polynomial rate height radius block request target error) 1 0)) (right (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-coefficient-at (lw-euler-refined-polynomial rate height radius block request target error) 1 0) (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error)))
         (radius (* (/ radius) (+ error (lw-euler-local-coefficient-request radius 1 coefficient-error)))) (cap (+ (* error (/ radius)) coefficient-error))))
  :in-theory (union-theories
 '(lw-complex-euler-refined-coefficient lw-erc-power-first abs lw-erc-left-commutes lw-erc-left-distributes lw-erc-fold-constants lw-erc-times-negative lw-erc-negative-times lw-erc-zero-times lw-erc-minus-one lw-erc-double-negative lw-erc-add-cancel lw-erc-double lw-erc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


