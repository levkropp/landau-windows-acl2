(in-package "ACL2")

(include-book "euler-uniform-polynomial")
(include-book "polynomial-coefficient-maps")

; Coefficients of V(s0+r*w), extracted from actual uniform polynomials.
; Rational Cauchy samples and a computed disk gap remove auxiliary error.

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

(local (defthm lw-ecc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecc-times-negative)))))

(local (defthm lw-ecc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecc-left-commutes)))))

(local (defthm lw-ecc-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-euler-coefficient-polynomial (rate height radius target error)
 (lw-polynomial-rescale (lw-euler-uniform-polynomial rate height radius target error) radius 0))

(defun lw-complex-euler-polynomial-coefficient (rate height radius target index error)
 (lw-complex-coefficient-at (lw-euler-coefficient-polynomial rate height radius target error) index 0))

(defun lw-euler-coefficient-comparison-count
 (rate height radius left-target right-target index left-error right-error)
 (+ 1 (max (nfix index)
       (max (len (lw-euler-uniform-polynomial rate height radius left-target left-error)) (len (lw-euler-uniform-polynomial rate height radius right-target right-error))))))

(defun lw-euler-coefficient-comparison-polynomial
 (rate height radius left-target right-target index left-error right-error)
 (lw-polynomial-disk-difference (lw-euler-uniform-polynomial rate height radius left-target left-error) (lw-euler-uniform-polynomial rate height radius right-target right-error) radius (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)))

(local (in-theory (disable lw-euler-coefficient-polynomial lw-complex-euler-polynomial-coefficient
 lw-euler-coefficient-comparison-count lw-euler-coefficient-comparison-polynomial)))

(defthm lw-euler-polynomial-coefficient-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp target) (natp index) (rationalp error) (< 0 error))
  (and (lw-complex-coefficientsp (lw-euler-coefficient-polynomial rate height radius target error))
       (lw-complexp (lw-complex-euler-polynomial-coefficient rate height radius target index error))))
 :hints (("Goal"
  :use (lw-euler-uniform-polynomial-valid
        (:instance lw-polynomial-rescale-valid (offset 0) (factor radius)
         (coefficients (lw-euler-uniform-polynomial rate height radius target error)))
        (:instance lw-complex-coefficient-at-rational (target index) (offset 0)
         (coefficients (lw-euler-coefficient-polynomial rate height radius target error))))
  :in-theory (union-theories
   '(lw-euler-coefficient-polynomial lw-complex-euler-polynomial-coefficient lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-coefficient-comparison-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (and (posp (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)) (< index (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)) (<= (len (lw-euler-uniform-polynomial rate height radius left-target left-error)) (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)) (<= (len (lw-euler-uniform-polynomial rate height radius right-target right-error)) (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error))
       (lw-complex-coefficientsp (lw-euler-coefficient-comparison-polynomial rate height radius left-target right-target index left-error right-error)) (equal (len (lw-euler-coefficient-comparison-polynomial rate height radius left-target right-target index left-error right-error)) (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-euler-uniform-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-ecc-length-natural (coefficients (lw-euler-uniform-polynomial rate height radius left-target left-error)))
        (:instance lw-ecc-length-natural (coefficients (lw-euler-uniform-polynomial rate height radius right-target right-error)))
        (:instance lw-polynomial-disk-difference-valid (left (lw-euler-uniform-polynomial rate height radius left-target left-error)) (right (lw-euler-uniform-polynomial rate height radius right-target right-error)) (count (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error))))
  :in-theory (union-theories
   '(lw-euler-coefficient-comparison-count lw-euler-coefficient-comparison-polynomial nfix max lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ecc-scaled-unit-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point 1) (natp power))
  (lw-complex-diskp (lw-complex-scale radius (lw-complex-power point power)) radius))
 :hints (("Goal"
  :use ((:instance lw-complex-unit-power (index power))
        (:instance lw-complex-scale-disk (point (lw-complex-power point power)) (factor radius) (radius 1)))
  :in-theory (union-theories
   '(abs lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defun lw-ecc-countdown (samples)
 (declare (xargs :measure (nfix samples)))
 (if (zp samples) 0 (lw-ecc-countdown (- samples 1)))))

(defthm lw-euler-coefficient-boundary-check
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (lw-complex-diskp point 1) (natp samples))
  (lw-cauchy-boundary-check (lw-euler-coefficient-comparison-polynomial rate height radius left-target right-target index left-error right-error) point 0 samples (+ left-error right-error)))
 :hints (("Goal" :induct (lw-ecc-countdown samples)
  :in-theory (union-theories
   '((:induction lw-ecc-countdown) lw-cauchy-boundary-check lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-euler-coefficient-comparison-data)
          (:instance lw-euler-uniform-polynomial-valid (target left-target) (error left-error))
          (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
          (:instance lw-complex-unit-power (index (- samples 1)))
          (:instance lw-complex-disk-data (radius 1))
          (:instance lw-complex-disk-data
           (point (lw-complex-power point (- samples 1))) (radius 1))
          (:instance lw-ecc-scaled-unit-point (power (- samples 1)))
          (:instance lw-polynomial-disk-difference-evaluation
           (left (lw-euler-uniform-polynomial rate height radius left-target left-error)) (right (lw-euler-uniform-polynomial rate height radius right-target right-error)) (count (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error))
           (point (lw-complex-power point (- samples 1))))
          (:instance lw-complex-euler-uniform-polynomial-cauchy
           (point (lw-complex-scale radius (lw-complex-power point (- samples 1))))))
    :in-theory (union-theories
   '(lw-euler-coefficient-comparison-polynomial lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
    :nonlinearp nil :do-not-induct t))))

(defthm lw-complex-euler-polynomial-coefficient-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-polynomial-coefficient rate height radius left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error margin)))
 :hints (("Goal"
  :use (lw-euler-coefficient-comparison-data
        (:instance lw-euler-uniform-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-cauchy-orbit-data (degree (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)))
        (:instance lw-cauchy-coefficient-count-natural (coefficients (lw-euler-coefficient-comparison-polynomial rate height radius left-target right-target index left-error right-error)) (degree (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)) (error margin))
        (:instance lw-euler-coefficient-boundary-check
         (point (lw-cauchy-orbit-rotation (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)))
         (samples (lw-cauchy-coefficient-count (lw-euler-coefficient-comparison-polynomial rate height radius left-target right-target index left-error right-error) (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error) margin)))
        (:instance lw-cauchy-finite-coefficient-bound
         (coefficients (lw-euler-coefficient-comparison-polynomial rate height radius left-target right-target index left-error right-error)) (degree (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error)) (target index) (error margin) (cap (+ left-error right-error)))
        (:instance lw-polynomial-disk-difference-coefficient
         (left (lw-euler-uniform-polynomial rate height radius left-target left-error)) (right (lw-euler-uniform-polynomial rate height radius right-target right-error)) (count (lw-euler-coefficient-comparison-count rate height radius left-target right-target index left-error right-error))))
  :in-theory (union-theories
   '(lw-euler-coefficient-comparison-polynomial lw-euler-coefficient-polynomial lw-complex-euler-polynomial-coefficient lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-polynomial-coefficient-cauchy
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp left-target) (natp right-target) (natp index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-polynomial-coefficient rate height radius left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-polynomial-coefficient rate height radius left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error)))
  :use ((:instance lw-euler-polynomial-coefficient-rational (target left-target) (error left-error))
        (:instance lw-euler-polynomial-coefficient-rational (target right-target) (error right-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-polynomial-coefficient rate height radius left-target index left-error)) (right (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-polynomial-coefficient rate height radius left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error))) (radius (+ left-error right-error)) (cost 1))
        (:instance lw-complex-euler-polynomial-coefficient-with-margin
         (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-polynomial-coefficient rate height radius left-target index left-error) (lw-complex-euler-polynomial-coefficient rate height radius right-target index right-error)) (+ left-error right-error) 1))))
  :in-theory (union-theories
   '( lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-euler-coefficient-value (rate height radius index error)
 (lw-complex-euler-polynomial-coefficient rate height radius index index error))

(local (in-theory (disable lw-complex-euler-coefficient-value)))

(defthm lw-complex-euler-coefficient-value-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp index) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-coefficient-value rate height radius index error)))
 :hints (("Goal"
  :use ((:instance lw-euler-polynomial-coefficient-rational (target index)))
  :in-theory (union-theories
   '(lw-complex-euler-coefficient-value lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-coefficient-value-cauchy
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-coefficient-value rate height radius index left-error)
                   (lw-complex-euler-coefficient-value rate height radius index right-error))
   (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-complex-euler-polynomial-coefficient-cauchy (left-target index) (right-target index)))
  :in-theory (union-theories
   '(lw-complex-euler-coefficient-value lw-ecc-left-commutes lw-ecc-left-distributes lw-ecc-fold-constants lw-ecc-times-negative lw-ecc-negative-times lw-ecc-zero-times lw-ecc-minus-one lw-ecc-double-negative lw-ecc-add-cancel lw-ecc-double lw-ecc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

