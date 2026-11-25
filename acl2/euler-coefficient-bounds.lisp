(in-package "ACL2")

(include-book "euler-coefficient-cauchy")

; One coarse polynomial bounds all normalized Euler coefficients.
; The cap is independent of degree, index and requested precision.

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

(local (in-theory (disable lw-euler-uniform-polynomial lw-euler-coefficient-polynomial
 lw-complex-euler-polynomial-coefficient lw-complex-euler-coefficient-value
 lw-complex-coefficient-at lw-complex-coefficient-mass lw-complex-polynomial
 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-orbit-rotation lw-complex-power)))

(local (defthm lw-ecb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecb-times-negative)))))

(local (defthm lw-ecb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecb-left-commutes)))))

(local (defthm lw-ecb-fold-add
 (implies (syntaxp (and (quotep a) (quotep b)))
  (equal (+ a (+ b c)) (+ (+ a b) c)))
 :hints (("Goal" :use ((:instance associativity-of-+ (x a) (y b) (z c)))
                  :in-theory (disable associativity-of-+)))))

(local (defthm lw-ecb-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-euler-uniform-coefficient-cap (rate height radius)
 (+ 2 (lw-complex-coefficient-mass (lw-euler-coefficient-polynomial rate height radius 0 1))))

(local (in-theory (disable lw-euler-uniform-coefficient-cap)))

(defthm lw-euler-uniform-coefficient-cap-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate))
  (and (rationalp (lw-euler-uniform-coefficient-cap rate height radius)) (<= 2 (lw-euler-uniform-coefficient-cap rate height radius))))
 :hints (("Goal"
  :use ((:instance lw-euler-polynomial-coefficient-rational (target 0) (index 0) (error 1))
        (:instance lw-complex-coefficient-mass-valid (coefficients (lw-euler-coefficient-polynomial rate height radius 0 1))))
  :in-theory (union-theories
   '(lw-euler-uniform-coefficient-cap lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ecb-scaled-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complex-diskp point 1))
  (lw-complex-diskp (lw-complex-scale radius point) radius))
 :hints (("Goal"
  :use ((:instance lw-complex-scale-disk (factor radius) (radius 1)))
  :in-theory (union-theories
   '(abs lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-polynomial-uniform-cap
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point 1))
  (lw-complex-diskp (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) point 0) (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
 :hints (("Goal"
  :use (lw-euler-uniform-coefficient-cap-valid
        (:instance lw-euler-polynomial-coefficient-rational (index 0))
        (:instance lw-euler-polynomial-coefficient-rational (index 0) (target 0) (error 1))
        (:instance lw-euler-uniform-polynomial-valid)
        (:instance lw-euler-uniform-polynomial-valid (target 0) (error 1))
        (:instance lw-complex-disk-data (radius 1))
        lw-ecb-scaled-point
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius 0 1)) (offset 0))
        (:instance lw-polynomial-rescale-evaluation
         (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (factor radius) (offset 0))
        (:instance lw-polynomial-rescale-evaluation
         (coefficients (lw-euler-uniform-polynomial rate height radius 0 1)) (factor radius) (offset 0))
        (:instance lw-complex-euler-uniform-polynomial-cauchy
         (left-target target) (left-error error) (right-target 0) (right-error 1)
         (point (lw-complex-scale radius point)))
        (:instance lw-complex-polynomial-unit-mass-bound (coefficients (lw-euler-coefficient-polynomial rate height radius 0 1)) (offset 0))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) point 0)) (middle (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 1) point 0)) (right (cons 0 0))
         (radius (+ error 1)) (other-radius (lw-complex-coefficient-mass (lw-euler-coefficient-polynomial rate height radius 0 1)))))
  :in-theory (union-theories
   '(lw-ecb-fold-add lw-euler-coefficient-polynomial lw-euler-uniform-coefficient-cap lw-complex-sub-zero lw-complexp lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defun lw-ecb-countdown (samples)
 (declare (xargs :measure (nfix samples)))
 (if (zp samples) 0 (lw-ecb-countdown (- samples 1)))))

(defthm lw-euler-polynomial-uniform-boundary-check
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point 1) (natp samples))
  (lw-cauchy-boundary-check (lw-euler-coefficient-polynomial rate height radius target error) point 0 samples (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
 :hints (("Goal" :induct (lw-ecb-countdown samples)
  :in-theory (union-theories
   '((:induction lw-ecb-countdown) lw-cauchy-boundary-check lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-complex-unit-power (index (- samples 1)))
          (:instance lw-complex-euler-polynomial-uniform-cap (point (lw-complex-power point (- samples 1)))))
    :in-theory (union-theories
   '( lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
    :nonlinearp nil :do-not-induct t))))

(defthm lw-complex-euler-polynomial-coefficient-cap-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp target) (natp index) (rationalp error) (< 0 error)
               (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-euler-polynomial-coefficient rate height radius target index error)
   (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error margin)))
 :hints (("Goal"
  :cases ((< index (len (lw-euler-coefficient-polynomial rate height radius target error))))
  :use (lw-euler-polynomial-coefficient-rational lw-euler-uniform-coefficient-cap-valid
        (:instance lw-cauchy-orbit-data (degree (len (lw-euler-coefficient-polynomial rate height radius target error))))
        (:instance lw-cauchy-coefficient-count-natural
         (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (degree (len (lw-euler-coefficient-polynomial rate height radius target error))) (error margin))
        (:instance lw-euler-polynomial-uniform-boundary-check
         (point (lw-cauchy-orbit-rotation (len (lw-euler-coefficient-polynomial rate height radius target error))))
         (samples (lw-cauchy-coefficient-count (lw-euler-coefficient-polynomial rate height radius target error) (len (lw-euler-coefficient-polynomial rate height radius target error)) margin)))
        (:instance lw-cauchy-finite-coefficient-bound
         (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (degree (len (lw-euler-coefficient-polynomial rate height radius target error)))
         (target index) (error margin) (cap (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
        (:instance lw-complex-coefficient-at-nth (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (offset 0) (target index))
        (:instance lw-complex-coefficient-at-outside (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (offset 0) (target index))
        (:instance lw-complex-zero-disk (radius (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error margin))))
  :in-theory (union-theories
   '(lw-ecb-length-natural lw-complex-euler-polynomial-coefficient lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-polynomial-coefficient-cap
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp target) (natp index) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-euler-polynomial-coefficient rate height radius target index error)
   (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-euler-polynomial-coefficient rate height radius target index error)
            (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
  :use (lw-euler-polynomial-coefficient-rational lw-euler-uniform-coefficient-cap-valid
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-euler-polynomial-coefficient rate height radius target index error))
         (radius (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)) (cost 1))
        (:instance lw-complex-euler-polynomial-coefficient-cap-with-margin
         (margin (lw-disk-gap-refinement
          (lw-complex-euler-polynomial-coefficient rate height radius target index error) (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error) 1))))
  :in-theory (union-theories
   '( lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-coefficient-value-cap
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp index) (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-euler-coefficient-value rate height radius index error) (lw-euler-uniform-coefficient-cap rate height radius)))
 :hints (("Goal"
  :use (lw-euler-uniform-coefficient-cap-valid
        (:instance lw-complex-euler-polynomial-coefficient-cap (target index))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-euler-coefficient-value rate height radius index error))
         (radius (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)) (cap (lw-euler-uniform-coefficient-cap rate height radius))))
  :in-theory (union-theories
   '(lw-complex-euler-coefficient-value lw-ecb-left-commutes lw-ecb-left-distributes lw-ecb-fold-constants lw-ecb-times-negative lw-ecb-negative-times lw-ecb-zero-times lw-ecb-minus-one lw-ecb-double-negative lw-ecb-add-cancel lw-ecb-double lw-ecb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

