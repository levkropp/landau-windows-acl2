; Uniform finite polynomial models of the normalized Euler evaluator away from one.
(in-package "ACL2")
(include-book "euler-normalized-disk")
(include-book "euler-removable-extension")
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
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-neighborhood-radius
 lw-euler-normalized-disk-radius lw-euler-normalized-request lw-euler-normalized-gamma
 lw-euler-normalized-total-cost lw-euler-uniform-log-polynomial lw-euler-uniform-log-cap
 lw-normalized-local-polynomial lw-complex-polynomial lw-normalized-local-cap
 lw-normalized-local-inverse-cost lw-normalized-local-transport-cost
 lw-normalized-local-point-cap lw-complex-local-normalization lw-complex-normalized-euler
 lw-complex-euler-log-derivative-value lw-euler-bounds
 lw-mellin-euler-log-request lw-mellin-euler-log-value lw-mellin-euler-log-extended-value
 lw-euler-log-transform)))
(local (defthm lw-enp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enp-times-negative (a b) (b a)))
                 :in-theory (disable lw-enp-times-negative)))))

(local (defthm lw-enp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enp-left-commutes)))))
(defun lw-euler-normalized-polynomial (rate height outer-radius anchor-error target error)
 (lw-normalized-local-polynomial (cons rate height) (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) (lw-euler-normalized-gamma rate height outer-radius anchor-error error) (lw-euler-normalized-request rate height outer-radius anchor-error error)))
(local (in-theory (disable lw-euler-normalized-polynomial)))
(defthm lw-euler-normalized-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error)) (lw-complex-coefficientsp (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-request-data
       (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-normalized-local-polynomial-valid (anchor (cons rate height)) (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) (gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (error (lw-euler-normalized-request rate height outer-radius anchor-error error))))
 :in-theory (union-theories
 '(lw-euler-normalized-polynomial lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-normalized-polynomial-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-normalized-local-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error))))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data lw-euler-normalized-request-data
       (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-euler-uniform-log-polynomial-cap (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-normalized-local-polynomial-bound (anchor (cons rate height)) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) (gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (log-cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (error (lw-euler-normalized-request rate height outer-radius anchor-error error))))
 :in-theory (union-theories
 '(lw-euler-normalized-polynomial lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-normalized-polynomial-model-error
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-local-normalization (cons rate height) point (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) point 0) (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0))
  (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error))))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data lw-euler-normalized-request-data
       (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-euler-uniform-log-polynomial-cap (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-normalized-local-polynomial-error (anchor (cons rate height)) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) (gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (log-cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (error (lw-euler-normalized-request rate height outer-radius anchor-error error))))
 :in-theory (union-theories
 '(lw-euler-normalized-polynomial lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-normalized-transform-identity
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-complexp value) (rationalp sample-gamma))
 (equal (lw-complex-local-normalization (cons rate height) point value sample-gamma)
        (lw-euler-log-transform (+ rate (car point)) (+ height (cdr point)) value sample-gamma)))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data lw-euler-value-clearance-data
       (:instance lw-normalized-local-point-data (anchor (cons rate height)) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-local-normalization-normalized (anchor (cons rate height)) (gamma sample-gamma))
       (:instance lw-complex-normalized-euler-real-anchor (point (lw-complex-add (lw-complex-sub (cons rate height) (cons 1 0)) point)) (gamma sample-gamma)))
 :in-theory (union-theories
 '(lw-complex-add lw-complex-sub lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(local (defthm lw-enp-native-request-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (rationalp margin) (< 0 margin))
 (and (rationalp (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)) (< 0 (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)) (<= (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin) margin)
      (rationalp (car (lw-euler-bounds (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin))))))
 :hints (("Goal"
 :use (lw-euler-normalized-point-data
       (:instance lw-mellin-euler-log-request-data (rate (+ rate (car point))) (height (+ height (cdr point))) (error margin))
       (:instance lw-euler-bounds-interval (epsilon (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin))))
 :in-theory (union-theories
 '(lw-intervalp lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(local (defthm lw-enp-native-gamma-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (cons (car (lw-euler-bounds (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin))) 0) (cons (lw-euler-normalized-gamma rate height outer-radius anchor-error error) 0)) (+ (lw-euler-normalized-request rate height outer-radius anchor-error error) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin))))
 :hints (("Goal"
 :use (lw-enp-native-request-data lw-euler-normalized-request-data
       (:instance lw-euler-lower-cauchy (left-error (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)) (right-error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-real-difference-bound (gamma (car (lw-euler-bounds (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))) (other-gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (error (+ (lw-euler-normalized-request rate height outer-radius anchor-error error) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))))
 :in-theory (union-theories
 '(lw-euler-normalized-gamma lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(local (defthm lw-enp-native-model-transport
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-mellin-euler-log-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor margin) (lw-complex-local-normalization (cons rate height) point (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) point 0) (lw-euler-normalized-gamma rate height outer-radius anchor-error error))) (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (+ (lw-euler-normalized-request rate height outer-radius anchor-error error) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data lw-euler-normalized-request-data
       (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-euler-uniform-log-polynomial-cap (error (lw-euler-normalized-request rate height outer-radius anchor-error error))) lw-enp-native-request-data lw-enp-native-gamma-comparison
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) (offset 0))
       (:instance lw-complex-euler-log-derivative-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))
       (:instance lw-complex-euler-log-polynomial-checked-comparison (error (lw-euler-normalized-request rate height outer-radius anchor-error error)) (value-error (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))
       (:instance lw-euler-normalized-transform-identity (value (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin))) (sample-gamma (car (lw-euler-bounds (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))))
       (:instance lw-complex-local-normalization-transport (anchor (cons rate height)) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))
        (value (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin))) (other-value (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) point 0)) (gamma (car (lw-euler-bounds (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))) (other-gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error))
        (value-error (+ (lw-euler-normalized-request rate height outer-radius anchor-error error) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin))) (gamma-error (+ (lw-euler-normalized-request rate height outer-radius anchor-error error) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))))
 :in-theory (union-theories
 '(lw-mellin-euler-log-value lw-normalized-local-transport-cost lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-enp-native-polynomial-error
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-mellin-euler-log-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor margin) (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0)) (+ (* (lw-euler-normalized-total-cost rate height outer-radius anchor-error) (lw-euler-normalized-request rate height outer-radius anchor-error error)) (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data lw-euler-normalized-request-data lw-enp-native-request-data
       lw-euler-normalized-polynomial-valid
       (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) (offset 0))
       (:instance lw-complex-local-normalization-rational (anchor (cons rate height)) (value (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) point 0)) (gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error)))
       (:instance lw-mellin-euler-log-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error margin)) lw-enp-native-model-transport lw-complex-euler-normalized-polynomial-model-error
       (:instance lw-complex-difference-triangle (left (lw-mellin-euler-log-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor margin)) (middle (lw-complex-local-normalization (cons rate height) point (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) point 0) (lw-euler-normalized-gamma rate height outer-radius anchor-error error))) (right (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0))
        (radius (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (+ (lw-euler-normalized-request rate height outer-radius anchor-error error) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))) (other-radius (* (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (lw-euler-normalized-request rate height outer-radius anchor-error error)))))
 :in-theory (union-theories
 '(lw-euler-normalized-total-cost lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(local (defthm lw-enp-native-polynomial-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-euler-log-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor margin)) (+ (* 1/2 error) (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) margin))))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data lw-euler-normalized-request-data lw-enp-native-request-data
       lw-euler-normalized-polynomial-valid
       (:instance lw-euler-uniform-log-polynomial-valid (error (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error))) (offset 0))
       (:instance lw-complex-local-normalization-rational (anchor (cons rate height)) (value (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target (lw-euler-normalized-request rate height outer-radius anchor-error error)) point 0)) (gamma (lw-euler-normalized-gamma rate height outer-radius anchor-error error)))
       (:instance lw-mellin-euler-log-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error margin)) lw-enp-native-polynomial-error
       (:instance lw-enp-multiply-order (a (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)) (b margin) (factor (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-euler-log-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor margin) (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0)))
        (radius (+ (* (lw-euler-normalized-total-cost rate height outer-radius anchor-error) (lw-euler-normalized-request rate height outer-radius anchor-error error)) (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-mellin-euler-log-request (+ rate (car point)) (+ height (cdr point)) margin)))) (cap (+ (* 1/2 error) (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) margin))))
       (:instance lw-complex-difference-symmetric (left (lw-mellin-euler-log-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor margin)) (right (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0))
        (radius (+ (* 1/2 error) (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) margin)))))
 :in-theory (union-theories
 '( lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-enp-comparison-with-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (rationalp value-error) (< 0 value-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (+ (* 1/2 (+ error value-error)) (* (+ 1/2 (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))) margin))))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data
       lw-euler-normalized-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-mellin-euler-log-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error margin))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error value-error)) lw-enp-native-polynomial-margin
       (:instance lw-mellin-euler-log-value-cauchy (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (left-error margin) (right-error value-error))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0)) (middle (lw-mellin-euler-log-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor margin)) (right (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error))
        (radius (+ (* 1/2 error) (* (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) margin))) (other-radius (* 1/2 (+ margin value-error)))))
 :in-theory (union-theories
 '(lw-mellin-euler-log-extended-away lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-normalized-uniform-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :use (lw-euler-normalized-disk-data lw-euler-normalized-point-data
       lw-euler-normalized-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0)) (right (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error))) (radius (* 1/2 (+ error value-error))) (cost (+ 1/2 (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))))
       (:instance lw-enp-comparison-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-polynomial (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error)) (+ 1/2 (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))))))
 :in-theory (union-theories
 '( lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))



