; Fixed rational bounds for all fine derivative approximants on an inner disk.
; Coarse coefficient mass supplies the constant; no shifted-center cap is assumed.
(in-package "ACL2")
(include-book "euler-uniform-derivative")
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
(local (in-theory (disable lw-polynomial-rescale lw-complex-polynomial
 lw-complex-coefficient-mass lw-euler-uniform-derivative-polynomial
 lw-complex-euler-local-coefficient-value)))
(local (defthm lw-eub-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eub-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eub-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eub-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eub-times-negative (a b) (b a)))
                 :in-theory (disable lw-eub-times-negative)))))

(local (defthm lw-eub-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eub-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eub-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eub-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eub-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eub-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eub-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eub-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eub-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eub-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eub-left-commutes)))))

(local (defthm lw-eub-radius-data
 (implies (and (rationalp radius) (<= 0 radius))
 (and (rationalp (max 1 radius)) (< 0 (max 1 radius)) (rationalp (/ (max 1 radius))) (< 0 (/ (max 1 radius)))
  (rationalp (* radius (/ (max 1 radius)))) (<= 0 (* radius (/ (max 1 radius)))) (<= (* radius (/ (max 1 radius))) 1)
  (equal (* (max 1 radius) (/ (max 1 radius))) 1)))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-positive (value (max 1 radius)))
       (:instance lw-eub-multiply-order (a 0) (b radius) (factor (/ (max 1 radius))))
       (:instance lw-eub-multiply-order (a radius) (b (max 1 radius)) (factor (/ (max 1 radius))))
       (:instance lw-eub-inverse-factor (divisor (max 1 radius)) (coefficient 1)))
 :in-theory (union-theories
 '(max lw-eub-left-commutes lw-eub-left-distributes lw-eub-fold-constants lw-eub-times-negative lw-eub-negative-times lw-eub-zero-times lw-eub-minus-one lw-eub-double-negative lw-eub-add-cancel lw-eub-double lw-eub-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defun lw-polynomial-disk-cap (coefficients radius)
 (lw-complex-coefficient-mass (lw-polynomial-rescale coefficients (max 1 radius) 0)))

(local (in-theory (disable lw-polynomial-disk-cap)))

(defthm lw-polynomial-disk-cap-valid
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp radius) (<= 0 radius))
 (and (rationalp (lw-polynomial-disk-cap coefficients radius)) (<= 0 (lw-polynomial-disk-cap coefficients radius))))
 :hints (("Goal"
 :use (lw-eub-radius-data
       (:instance lw-polynomial-rescale-valid (factor (max 1 radius)) (offset 0))
       (:instance lw-complex-coefficient-mass-valid (coefficients (lw-polynomial-rescale coefficients (max 1 radius) 0))))
 :in-theory (union-theories
 '(lw-polynomial-disk-cap lw-eub-left-commutes lw-eub-left-distributes lw-eub-fold-constants lw-eub-times-negative lw-eub-negative-times lw-eub-zero-times lw-eub-minus-one lw-eub-double-negative lw-eub-add-cancel lw-eub-double lw-eub-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-polynomial-disk-cap-bound
 (implies (and (lw-complex-coefficientsp coefficients)
  (rationalp radius) (<= 0 radius) (lw-complex-diskp point radius))
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) (lw-polynomial-disk-cap coefficients radius)))
 :hints (("Goal"
 :use (lw-eub-radius-data
       (:instance lw-complex-disk-data)
       (:instance lw-complex-scale-rational (factor (/ (max 1 radius))))
       (:instance lw-complex-scale-disk (factor (/ (max 1 radius))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-scale (/ (max 1 radius)) point)) (radius (* radius (/ (max 1 radius)))) (cap 1))
       (:instance lw-polynomial-rescale-valid (factor (max 1 radius)) (offset 0))
       (:instance lw-polynomial-rescale-evaluation (factor (max 1 radius)) (offset 0) (point (lw-complex-scale (/ (max 1 radius)) point)))
       (:instance lw-complex-polynomial-unit-mass-bound
        (coefficients (lw-polynomial-rescale coefficients (max 1 radius) 0)) (point (lw-complex-scale (/ (max 1 radius)) point)) (offset 0)))
 :in-theory (union-theories
 '(lw-polynomial-disk-cap abs lw-complex-scale-compose lw-complex-scale-one lw-eub-left-commutes lw-eub-left-distributes lw-eub-fold-constants lw-eub-times-negative lw-eub-negative-times lw-eub-zero-times lw-eub-minus-one lw-eub-double-negative lw-eub-add-cancel lw-eub-double lw-eub-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-euler-uniform-derivative-cap (rate height outer-radius inner-radius)
 (+ 3 (lw-polynomial-disk-cap (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1) inner-radius)))

(local (in-theory (disable lw-euler-uniform-derivative-cap)))

(defthm lw-euler-uniform-derivative-cap-valid
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< outer-radius rate)
 (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius))
 (and (rationalp (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius)) (< 0 (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius))))
 :hints (("Goal"
 :use ((:instance lw-euler-uniform-derivative-polynomial-valid (target 0) (error 1))
       (:instance lw-polynomial-disk-cap-valid (coefficients (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1)) (radius inner-radius)))
 :in-theory (union-theories
 '(lw-euler-uniform-derivative-cap lw-eub-left-commutes lw-eub-left-distributes lw-eub-fold-constants lw-eub-times-negative lw-eub-negative-times lw-eub-zero-times lw-eub-minus-one lw-eub-double-negative lw-eub-add-cancel lw-eub-double lw-eub-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-local-first-uniform-cap
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< outer-radius rate)
 (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius) (lw-complex-diskp center inner-radius)
  (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car center)))
  (rationalp coefficient-error) (< 0 coefficient-error) (<= coefficient-error 1))
 (lw-complex-diskp (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) coefficient-radius 1 coefficient-error) (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius)))
 :hints (("Goal"
 :use ((:instance lw-euler-shifted-center-data (radius (- outer-radius inner-radius)))
       (:instance lw-euler-uniform-derivative-polynomial-valid (target 0) (error 1))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1)) (point center) (offset 0))
       (:instance lw-complex-polynomial-disk-cap-bound (coefficients (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1)) (point center) (radius inner-radius))
       (:instance lw-polynomial-disk-cap-valid (coefficients (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1)) (radius inner-radius))
       (:instance lw-complex-euler-local-coefficient-rational
        (rate (+ rate (car center))) (height (+ height (cdr center))) (radius coefficient-radius) (index 1) (error coefficient-error))
       (:instance lw-complex-euler-uniform-derivative-comparison (target 0) (error 1))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1) center 0)) (right (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) coefficient-radius 1 coefficient-error)) (radius (+ 1 coefficient-error)))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) coefficient-radius 1 coefficient-error)) (middle (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1) center 0)) (right (cons 0 0))
        (radius (+ 1 coefficient-error)) (other-radius (lw-polynomial-disk-cap (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1) inner-radius)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) coefficient-radius 1 coefficient-error))
        (radius (+ 1 coefficient-error (lw-polynomial-disk-cap (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius 0 1) inner-radius)))
        (cap (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius))))
 :in-theory (union-theories
 '(lw-euler-uniform-derivative-cap lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-eub-left-commutes lw-eub-left-distributes lw-eub-fold-constants lw-eub-times-negative lw-eub-negative-times lw-eub-zero-times lw-eub-minus-one lw-eub-double-negative lw-eub-add-cancel lw-eub-double lw-eub-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-uniform-derivative-polynomial-cap
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< outer-radius rate)
 (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius) (lw-complex-diskp center inner-radius)
  (natp target) (rationalp error) (< 0 error) (<= error 1))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0) (+ 2 (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius))))
 :hints (("Goal"
 :use ((:instance lw-euler-shifted-center-data (radius (- outer-radius inner-radius)))
       lw-euler-uniform-derivative-cap-valid
       lw-euler-uniform-derivative-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error)) (point center) (offset 0))
       (:instance lw-complex-euler-local-coefficient-rational
        (rate (+ rate (car center))) (height (+ height (cdr center))) (radius (- outer-radius inner-radius)) (index 1) (error 1))
       (:instance lw-complex-euler-local-first-uniform-cap (coefficient-radius (- outer-radius inner-radius)) (coefficient-error 1))
       (:instance lw-complex-euler-uniform-derivative-comparison (coefficient-radius (- outer-radius inner-radius)) (coefficient-error 1))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0)) (middle (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) (- outer-radius inner-radius) 1 1)) (right (cons 0 0))
        (radius (+ error 1)) (other-radius (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0))
        (radius (+ error 1 (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius))) (cap (+ 2 (lw-euler-uniform-derivative-cap rate height outer-radius inner-radius)))))
 :in-theory (union-theories
 '(lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-eub-left-commutes lw-eub-left-distributes lw-eub-fold-constants lw-eub-times-negative lw-eub-negative-times lw-eub-zero-times lw-eub-minus-one lw-eub-double-negative lw-eub-add-cancel lw-eub-double lw-eub-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

