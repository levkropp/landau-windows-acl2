; A normalized numerator defined uniformly through the apparent pole at one.
; The calibration and neighborhood use the proved coarse check at s=1.
(in-package "ACL2")
(include-book "euler-log-divided-difference")
(include-book "euler-log-derivative-anchor")
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
 lw-euler-uniform-log-cap lw-euler-uniform-log-polynomial lw-euler-log-divided-polynomial
 lw-euler-rounding-precision lw-polynomial-multiply-coefficients lw-polynomial-add-constant
 lw-complex-polynomial)))
(local (defthm lw-ern-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ern-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ern-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ern-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ern-times-negative (a b) (b a)))
                 :in-theory (disable lw-ern-times-negative)))))

(local (defthm lw-ern-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ern-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ern-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ern-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ern-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ern-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ern-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ern-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ern-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ern-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ern-left-commutes)))))

(defun lw-euler-removable-radius () (lw-euler-neighborhood-radius 1 0 1/2 1/64))
(defun lw-euler-removable-log-cap () (lw-euler-uniform-log-cap 1 0 1/2 1/64))
(defun lw-euler-removable-divided-gain () (+ 1 (* 2 (/ (lw-euler-removable-radius)))))
(defun lw-euler-removable-cost () (* 4 (lw-euler-removable-divided-gain)))
(defun lw-euler-removable-numerator-cap ()
 (+ 1 (lw-euler-removable-log-cap)
  (* 2 (lw-euler-removable-log-cap) (/ (lw-euler-removable-radius)))))

(local (in-theory (disable lw-euler-removable-radius lw-euler-removable-log-cap
 lw-euler-removable-divided-gain lw-euler-removable-cost lw-euler-removable-numerator-cap)))

(defthm lw-euler-removable-neighborhood-data
 (and (lw-euler-value-clearance-check 1 0 1/64)
      (rationalp (lw-euler-removable-radius)) (< 0 (lw-euler-removable-radius)) (<= (lw-euler-removable-radius) 1/4)
      (rationalp (lw-euler-removable-log-cap)) (< 0 (lw-euler-removable-log-cap))
      (rationalp (lw-euler-removable-divided-gain)) (< 0 (lw-euler-removable-divided-gain))
      (rationalp (lw-euler-removable-cost)) (< 0 (lw-euler-removable-cost))
      (rationalp (lw-euler-removable-numerator-cap)) (< 0 (lw-euler-removable-numerator-cap)))
 :hints (("Goal"
 :use (lw-euler-log-derivative-anchor-check
       (:instance lw-euler-neighborhood-data (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64))
       (:instance lw-euler-uniform-log-model-data (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error 1))
       (:instance lw-reciprocal-positive (value (lw-euler-removable-radius)))
       (:instance lw-ern-positive-product (a (lw-euler-removable-log-cap)) (b (/ (lw-euler-removable-radius)))))
 :in-theory (union-theories
 '(lw-euler-removable-radius lw-euler-removable-log-cap lw-euler-removable-divided-gain lw-euler-removable-cost lw-euler-removable-numerator-cap lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-euler-removable-request (error)
 (lw-euler-rounding-precision (lw-euler-removable-cost) error))

(local (in-theory (disable lw-euler-removable-request)))

(defthm lw-euler-removable-request-data
 (implies (and (rationalp error) (< 0 error))
 (and (rationalp (lw-euler-removable-request error)) (< 0 (lw-euler-removable-request error)) (<= (lw-euler-removable-request error) 1)
      (<= (* (lw-euler-removable-cost) (lw-euler-removable-request error)) (* 1/2 error))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data
       (:instance lw-euler-rounding-precision-valid (cost (lw-euler-removable-cost))))
 :in-theory (union-theories
 '(lw-euler-removable-request lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-ern-negative-summand
 (implies (and (lw-complexp a) (lw-complexp b))
 (equal (lw-complex-add a (lw-complex-mul (cons -1 0) b)) (lw-complex-sub a b)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ern-numerator-difference
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp h) (lw-complexp k))
 (equal (lw-complex-sub (lw-complex-sub (lw-complex-add (cons 1 0) a) h)
                        (lw-complex-sub (lw-complex-add (cons 1 0) b) k))
        (lw-complex-sub (lw-complex-sub a b) (lw-complex-sub h k))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-euler-removable-numerator (target error)
 (lw-polynomial-add-constant (lw-complex-add (cons 1 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0))
  (lw-polynomial-multiply-coefficients (cons -1 0) (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)))))

(local (in-theory (disable lw-euler-removable-numerator)))

(defthm lw-euler-removable-numerator-valid
 (implies (and (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-removable-numerator target error)))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-request-data
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-euler-log-divided-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (point (cons 0 0)) (offset 0))
       (:instance lw-polynomial-multiply-coefficients-valid (coefficients (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (factor (cons -1 0)))
       (:instance lw-polynomial-add-constant-valid
        (constant (lw-complex-add (cons 1 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0))) (coefficients (lw-polynomial-multiply-coefficients (cons -1 0) (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))))))
 :in-theory (union-theories
 '(lw-euler-removable-numerator lw-complex-ring-rational (:executable-counterpart lw-complexp) lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-removable-numerator-evaluation
 (implies (and (natp target) (rationalp error) (< 0 error) (lw-complexp point))
 (equal (lw-complex-polynomial (lw-euler-removable-numerator target error) point 0) (lw-complex-sub (lw-complex-add (cons 1 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0)) (lw-complex-polynomial (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) point 0))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-request-data
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-euler-log-divided-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (offset 0))
       (:instance lw-polynomial-multiply-coefficients-valid (coefficients (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (factor (cons -1 0)))
       (:instance lw-polynomial-multiply-coefficients-evaluation (coefficients (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (factor (cons -1 0)) (offset 0))
       (:instance lw-polynomial-add-constant-evaluation
        (constant (lw-complex-add (cons 1 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0))) (coefficients (lw-polynomial-multiply-coefficients (cons -1 0) (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))))))
 :in-theory (union-theories
 '(lw-euler-removable-numerator lw-ern-negative-summand lw-complex-ring-rational (:executable-counterpart lw-complexp) lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-numerator-cap
 (implies (and (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-removable-numerator target error) point 0) (lw-euler-removable-numerator-cap)))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-request-data
       (:instance lw-complex-disk-data (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-zero-disk (radius (lw-euler-removable-radius)))
       (:instance lw-complex-euler-uniform-log-polynomial-cap (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)) (point (cons 0 0)))
       (:instance lw-complex-euler-log-divided-polynomial-cap (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       lw-euler-removable-numerator-evaluation
       (:instance lw-complex-add-disk (left (cons 1 0)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0)) (radius 1) (other-radius (lw-euler-removable-log-cap)))
       (:instance lw-complex-sub-disk (left (lw-complex-add (cons 1 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0))) (right (lw-complex-polynomial (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) point 0))
        (radius (+ 1 (lw-euler-removable-log-cap))) (other-radius (* 2 (lw-euler-removable-log-cap) (/ (lw-euler-removable-radius))))))
 :in-theory (union-theories
 '(lw-euler-removable-numerator-cap lw-euler-removable-radius lw-euler-removable-log-cap (:executable-counterpart lw-complex-diskp) lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-numerator-cauchy
 (implies (and (natp left-target) (natp right-target)
  (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
  (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-removable-numerator left-target left-error) point 0) (lw-complex-polynomial (lw-euler-removable-numerator right-target right-error) point 0))
  (* (lw-euler-removable-divided-gain) (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error)))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data
       (:instance lw-euler-removable-request-data (error left-error))
       (:instance lw-euler-removable-request-data (error right-error))
       (:instance lw-complex-disk-data (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-zero-disk (radius (lw-euler-removable-radius)))
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (target left-target) (error (lw-euler-removable-request left-error)))
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (target right-target) (error (lw-euler-removable-request right-error)))
       (:instance lw-euler-log-divided-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (target left-target) (error (lw-euler-removable-request left-error)))
       (:instance lw-euler-log-divided-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (target right-target) (error (lw-euler-removable-request right-error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 left-target (lw-euler-removable-request left-error))) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 right-target (lw-euler-removable-request right-error))) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-log-divided-polynomial 1 0 1/2 1/64 left-target (lw-euler-removable-request left-error))) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-log-divided-polynomial 1 0 1/2 1/64 right-target (lw-euler-removable-request right-error))) (offset 0))
       (:instance lw-euler-removable-numerator-evaluation (target left-target) (error left-error))
       (:instance lw-euler-removable-numerator-evaluation (target right-target) (error right-error))
       (:instance lw-complex-euler-log-polynomial-cauchy (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64)
        (left-error (lw-euler-removable-request left-error)) (right-error (lw-euler-removable-request right-error)) (point (cons 0 0)))
       (:instance lw-complex-euler-log-divided-polynomial-cauchy (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64)
        (left-error (lw-euler-removable-request left-error)) (right-error (lw-euler-removable-request right-error)))
       (:instance lw-complex-sub-disk (left (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 left-target (lw-euler-removable-request left-error)) (cons 0 0) 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 right-target (lw-euler-removable-request right-error)) (cons 0 0) 0))) (right (lw-complex-sub (lw-complex-polynomial (lw-euler-log-divided-polynomial 1 0 1/2 1/64 left-target (lw-euler-removable-request left-error)) point 0) (lw-complex-polynomial (lw-euler-log-divided-polynomial 1 0 1/2 1/64 right-target (lw-euler-removable-request right-error)) point 0)))
        (radius (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error))) (other-radius (* 2 (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error)) (/ (lw-euler-removable-radius)))))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 left-target (lw-euler-removable-request left-error)) (cons 0 0) 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 right-target (lw-euler-removable-request right-error)) (cons 0 0) 0)) (lw-complex-sub (lw-complex-polynomial (lw-euler-log-divided-polynomial 1 0 1/2 1/64 left-target (lw-euler-removable-request left-error)) point 0) (lw-complex-polynomial (lw-euler-log-divided-polynomial 1 0 1/2 1/64 right-target (lw-euler-removable-request right-error)) point 0))))
        (radius (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error) (* 2 (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error)) (/ (lw-euler-removable-radius)))))
        (cap (* (lw-euler-removable-divided-gain) (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error))))))
 :in-theory (union-theories
 '((:executable-counterpart lw-complexp) lw-euler-removable-numerator-evaluation lw-euler-removable-radius lw-euler-removable-divided-gain lw-ern-numerator-difference lw-ern-left-commutes lw-ern-left-distributes lw-ern-fold-constants lw-ern-times-negative lw-ern-negative-times lw-ern-zero-times lw-ern-minus-one lw-ern-double-negative lw-ern-add-cancel lw-ern-double lw-ern-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

