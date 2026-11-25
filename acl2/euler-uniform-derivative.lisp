; A single, explicitly generated derivative polynomial works on an inner disk.
; The output coefficient list is independent of the evaluation point.
(in-package "ACL2")
(include-book "euler-coefficient-radii")
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
(local (in-theory (disable lw-polynomial-derivative-coefficients
 lw-complex-polynomial-derivative lw-complex-coefficient-at lw-euler-shifted-polynomial
 lw-complex-euler-local-coefficient-value)))
(local (defthm lw-eud-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eud-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eud-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eud-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eud-times-negative (a b) (b a)))
                 :in-theory (disable lw-eud-times-negative)))))

(local (defthm lw-eud-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eud-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eud-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eud-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eud-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eud-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eud-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eud-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eud-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eud-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eud-left-commutes)))))

(local (defthm lw-eud-power-first
 (implies (rationalp radius) (equal (lw-rational-power radius 1) radius))
 :hints (("Goal" :expand ((lw-rational-power radius 1) (lw-rational-power radius 0))
 :in-theory (enable lw-rational-power)))))

(defthm lw-polynomial-shifted-first-derivative
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp center))
 (equal (lw-complex-coefficient-at (lw-polynomial-affine coefficients center (cons 1 0)) 1 0)
        (lw-complex-polynomial (lw-polynomial-derivative-coefficients coefficients) center 0)))
 :hints (("Goal"
 :use ((:instance lw-polynomial-affine-linear-coefficient (slope (cons 1 0)))
       (:instance lw-polynomial-derivative-coefficients-evaluation (point center))
       (:instance lw-complex-polynomial-derivative-rational (point center)))
 :in-theory (union-theories
 '(lw-complex-mul-one (:executable-counterpart lw-complexp) lw-eud-left-commutes lw-eud-left-distributes lw-eud-fold-constants lw-eud-times-negative lw-eud-negative-times lw-eud-zero-times lw-eud-minus-one lw-eud-double-negative lw-eud-add-cancel lw-eud-double lw-eud-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-eud-request-data
 (implies (and (rationalp outer-radius) (rationalp inner-radius)
  (< inner-radius outer-radius) (rationalp error) (< 0 error))
 (and (rationalp (- outer-radius inner-radius)) (< 0 (- outer-radius inner-radius))
      (rationalp (* 1/2 (- outer-radius inner-radius) error)) (< 0 (* 1/2 (- outer-radius inner-radius) error))
      (equal (* (* 1/2 (- outer-radius inner-radius) error) (/ (- outer-radius inner-radius))) (* 1/2 error))))
 :hints (("Goal"
 :use ((:instance lw-eud-positive-product (a (- outer-radius inner-radius)) (b error))
       (:instance lw-eud-inverse-factor (divisor (- outer-radius inner-radius)) (coefficient error)))
 :in-theory (union-theories
 '( lw-eud-left-commutes lw-eud-left-distributes lw-eud-fold-constants lw-eud-times-negative lw-eud-negative-times lw-eud-zero-times lw-eud-minus-one lw-eud-double-negative lw-eud-add-cancel lw-eud-double lw-eud-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-uniform-derivative-polynomial
 (rate height outer-radius inner-radius target error)
 (lw-polynomial-derivative-coefficients (lw-euler-uniform-polynomial rate height outer-radius target (* 1/2 (- outer-radius inner-radius) error))))

(local (in-theory (disable lw-euler-uniform-derivative-polynomial)))

(defthm lw-euler-uniform-derivative-polynomial-valid
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< outer-radius rate)
 (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius)
 (natp target) (rationalp error) (< 0 error))
 (and (lw-complex-coefficientsp (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error))
      (equal (len (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error)) (len (cdr (lw-euler-uniform-polynomial rate height outer-radius target (* 1/2 (- outer-radius inner-radius) error)))))))
 :hints (("Goal"
 :use (lw-eud-request-data
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (error (* 1/2 (- outer-radius inner-radius) error)))
       (:instance lw-polynomial-derivative-coefficients-valid (coefficients (lw-euler-uniform-polynomial rate height outer-radius target (* 1/2 (- outer-radius inner-radius) error)))))
 :in-theory (union-theories
 '(lw-euler-uniform-derivative-polynomial lw-eud-left-commutes lw-eud-left-distributes lw-eud-fold-constants lw-eud-times-negative lw-eud-negative-times lw-eud-zero-times lw-eud-minus-one lw-eud-double-negative lw-eud-add-cancel lw-eud-double lw-eud-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-uniform-derivative-polynomial-evaluation
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< outer-radius rate)
 (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius)
 (natp target) (rationalp error) (< 0 error) (lw-complexp center))
 (equal (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0) (lw-complex-polynomial-derivative (lw-euler-uniform-polynomial rate height outer-radius target (* 1/2 (- outer-radius inner-radius) error)) center)))
 :hints (("Goal"
 :use (lw-eud-request-data
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (error (* 1/2 (- outer-radius inner-radius) error)))
       (:instance lw-polynomial-derivative-coefficients-evaluation (coefficients (lw-euler-uniform-polynomial rate height outer-radius target (* 1/2 (- outer-radius inner-radius) error))) (point center)))
 :in-theory (union-theories
 '(lw-euler-uniform-derivative-polynomial lw-eud-left-commutes lw-eud-left-distributes lw-eud-fold-constants lw-eud-times-negative lw-eud-negative-times lw-eud-zero-times lw-eud-minus-one lw-eud-double-negative lw-eud-add-cancel lw-eud-double lw-eud-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-uniform-derivative-local-comparison
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< outer-radius rate)
 (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius)
 (natp target) (rationalp error) (< 0 error) (lw-complex-diskp center inner-radius)
  (rationalp coefficient-error) (< 0 coefficient-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0) (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) (- outer-radius inner-radius) 1 coefficient-error)) (+ (* 1/2 error) coefficient-error)))
 :hints (("Goal"
 :use (lw-eud-request-data
       (:instance lw-euler-shifted-center-data (radius (- outer-radius inner-radius)))
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (error (* 1/2 (- outer-radius inner-radius) error)))
       (:instance lw-polynomial-shifted-first-derivative (coefficients (lw-euler-uniform-polynomial rate height outer-radius target (* 1/2 (- outer-radius inner-radius) error))))
       (:instance lw-complex-euler-shifted-local-coefficient-comparison
        (radius (- outer-radius inner-radius)) (index 1) (error (* 1/2 (- outer-radius inner-radius) error))))
 :in-theory (union-theories
 '(lw-euler-shifted-polynomial lw-euler-uniform-derivative-polynomial lw-eud-power-first lw-eud-left-commutes lw-eud-left-distributes lw-eud-fold-constants lw-eud-times-negative lw-eud-negative-times lw-eud-zero-times lw-eud-minus-one lw-eud-double-negative lw-eud-add-cancel lw-eud-double lw-eud-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-uniform-derivative-comparison
 (implies (and (rationalp rate) (rationalp height)
 (rationalp outer-radius) (< outer-radius rate)
 (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius)
 (natp target) (rationalp error) (< 0 error) (lw-complex-diskp center inner-radius)
  (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car center)))
  (rationalp coefficient-error) (< 0 coefficient-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0) (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) coefficient-radius 1 coefficient-error)) (+ error coefficient-error)))
 :hints (("Goal"
 :use (lw-eud-request-data
       (:instance lw-euler-shifted-center-data (radius (- outer-radius inner-radius)))
       lw-euler-uniform-derivative-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error)) (point center) (offset 0))
       (:instance lw-complex-euler-local-coefficient-rational
        (rate (+ rate (car center))) (height (+ height (cdr center))) (radius (- outer-radius inner-radius)) (index 1) (error (* 1/4 error)))
       (:instance lw-complex-euler-local-coefficient-rational
        (rate (+ rate (car center))) (height (+ height (cdr center))) (radius coefficient-radius) (index 1) (error coefficient-error))
       (:instance lw-complex-euler-uniform-derivative-local-comparison (coefficient-error (* 1/4 error)))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0) (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) (- outer-radius inner-radius) 1 (* 1/4 error))))
        (radius (+ (* 1/2 error) (* 1/4 error))) (cap (* 3/4 error)))
       (:instance lw-complex-euler-local-coefficient-radius-comparison
        (rate (+ rate (car center))) (height (+ height (cdr center))) (left-radius (- outer-radius inner-radius)) (right-radius coefficient-radius)
        (index 1) (left-error (* 1/4 error)) (right-error coefficient-error))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0)) (middle (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) (- outer-radius inner-radius) 1 (* 1/4 error))) (right (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) coefficient-radius 1 coefficient-error))
        (radius (* 3/4 error)) (other-radius (+ (* 1/4 error) coefficient-error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius inner-radius target error) center 0) (lw-complex-euler-local-coefficient-value (+ rate (car center)) (+ height (cdr center)) coefficient-radius 1 coefficient-error)))
        (radius (+ (* 3/4 error) (* 1/4 error) coefficient-error)) (cap (+ error coefficient-error))))
 :in-theory (union-theories
 '( lw-eud-left-commutes lw-eud-left-distributes lw-eud-fold-constants lw-eud-times-negative lw-eud-negative-times lw-eud-zero-times lw-eud-minus-one lw-eud-double-negative lw-eud-add-cancel lw-eud-double lw-eud-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

