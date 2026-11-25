; Uniform agreement of an actual finite polynomial quotient with the Euler logarithmic derivative.
(in-package "ACL2")
(include-book "euler-circle-global-polynomial")
(include-book "euler-circle-grid")
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
(local (in-theory (disable lw-euler-value-clearance-check
 lw-euler-local-normalized-radius lw-euler-local-normalized-cap lw-euler-local-normalized-anchor
 lw-complex-segment)))
(local (defthm lw-egq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-egq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-egq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-egq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-egq-times-negative (a b) (b a)))
                 :in-theory (disable lw-egq-times-negative)))))

(local (defthm lw-egq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-egq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-egq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-egq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-egq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-egq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-egq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-egq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-egq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-egq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-egq-left-commutes)))))
(defun lw-euler-circle-global-quotient-cost (center radius plus-arcs minus-arcs)
 (+ (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
(defun lw-euler-circle-global-node-cost (center radius plus-arcs minus-arcs)
 (+ (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (* 1/4 (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
(defun lw-euler-circle-global-quotient (center radius point target error)
 (lw-complex-quotient (lw-euler-circle-global-derivative-value center radius point target error) (lw-euler-circle-global-polynomial-value center radius point target error)))
(defun lw-euler-circle-log-value (center radius plus-arcs minus-arcs point value-error)
 (lw-complex-euler-log-derivative-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) value-error))
(local (in-theory (disable lw-euler-circle-global-quotient-cost lw-euler-circle-global-node-cost lw-euler-circle-global-quotient lw-euler-circle-log-value lw-euler-circle-global-polynomial-value lw-euler-circle-global-derivative-value lw-complex-quotient
 lw-euler-circle-coverp lw-euler-circle-anchor-min lw-euler-circle-point-lower lw-euler-circle-outer-radius lw-euler-circle-outer-gap lw-euler-circle-global-derivative-cap
 lw-euler-circle-cover-patch lw-euler-contour-anchor lw-euler-value-clearance-lower lw-euler-value-clearance-size
 lw-euler-log-derivative-cost lw-euler-log-derivative-request lw-complex-euler-log-derivative-value lw-complex-euler-local-coefficient-value lw-euler-rounding-precision)))

(defthm lw-euler-circle-global-quotient-cost-data
 (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (and (rationalp (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (< 0 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (<= (lw-euler-circle-anchor-min plus-arcs minus-arcs) 1)
      (rationalp (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (< 0 (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
      (rationalp (lw-euler-circle-outer-gap center radius)) (< 0 (lw-euler-circle-outer-gap center radius))
      (rationalp (lw-euler-circle-global-derivative-cap center radius)) (< 0 (lw-euler-circle-global-derivative-cap center radius))
      (rationalp (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs)) (< 0 (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs)) (rationalp (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs)) (< 0 (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs))))
 :hints (("Goal"
 :use (lw-euler-circle-outer-data lw-euler-circle-global-derivative-cap-data
       (:instance lw-euler-circle-anchor-min-data (point (cons 1 0)))
       (:instance lw-reciprocal-positive (value (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
       (:instance lw-egq-positive-product (a (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (b (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
       (:instance lw-egq-positive-product (a (lw-euler-circle-outer-gap center radius)) (b (lw-euler-circle-global-derivative-cap center radius)))
       (:instance lw-egq-positive-product (a (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-global-derivative-cap center radius))) (b (* (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
       (:instance lw-egq-positive-product (a (lw-euler-circle-global-derivative-cap center radius)) (b (* (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))))))
 :in-theory (union-theories
 '((:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-norm-square) lw-euler-circle-global-quotient-cost lw-euler-circle-global-node-cost lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(local (defthm lw-egq-rounding-linear
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
 (<= (lw-euler-rounding-precision cost (* 2 error)) error))
 :hints (("Goal"
 :use ((:instance lw-positive-division-bound (numerator (* 2 error)) (divisor (+ 2 (* 2 cost))) (bound error))
       (:instance lw-egq-multiply-order (a 0) (b cost) (factor error)))
 :in-theory (union-theories
 '(lw-euler-rounding-precision min lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-log-derivative-request-linear-bound
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
 (<= (lw-euler-log-derivative-request rate height radius anchor-error error) error))
 :hints (("Goal"
 :use (lw-euler-log-derivative-cost-valid
       (:instance lw-egq-rounding-linear (cost (lw-euler-log-derivative-cost rate height radius anchor-error))))
 :in-theory (union-theories
 '(lw-euler-log-derivative-request min lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-global-quotient-rational
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error))
 (lw-complexp (lw-euler-circle-global-quotient center radius point target error)))
 :hints (("Goal"
 :use (lw-euler-circle-global-values-rational
       (:instance lw-complex-quotient-rational (numerator (lw-euler-circle-global-derivative-value center radius point target error)) (denominator (lw-euler-circle-global-polynomial-value center radius point target error))))
 :in-theory (union-theories
 '(lw-euler-circle-global-quotient lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-log-value-rational
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp value-error) (< 0 value-error))
 (lw-complexp (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check
       (:instance lw-complex-euler-log-derivative-rational (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (error value-error)))
 :in-theory (union-theories
 '(lw-euler-circle-log-value lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-global-quotient-cap
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= error 1) (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
 (lw-complex-diskp (lw-euler-circle-global-quotient center radius point target error) (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
 :hints (("Goal"
 :use (lw-euler-circle-global-quotient-cost-data lw-euler-circle-global-polynomial-clearance lw-euler-circle-global-derivative-bound
       (:instance lw-complex-mul-disk (left (lw-euler-circle-global-derivative-value center radius point target error)) (radius (lw-euler-circle-global-derivative-cap center radius)) (right (lw-complex-reciprocal (lw-euler-circle-global-polynomial-value center radius point target error))) (other-radius (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
 :in-theory (union-theories
 '(lw-euler-circle-global-quotient lw-complex-quotient lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-log-value-cauchy
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub
  (lw-euler-circle-log-value center radius plus-arcs minus-arcs point left-error)
  (lw-euler-circle-log-value center radius plus-arcs minus-arcs point right-error)) (+ left-error right-error)))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check
       (:instance lw-complex-euler-log-derivative-cauchy (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))))
 :in-theory (union-theories
 '(lw-euler-circle-log-value lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))



(local (defthm lw-egq-native-request-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp margin) (< 0 margin))
 (and (rationalp (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)) (< 0 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)) (<= (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin) margin)
      (<= (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin) (* 1/4 (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point)))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check
       (:instance lw-euler-log-derivative-request-data (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (error margin))
       (:instance lw-euler-log-derivative-request-linear-bound (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))) (error margin)))
 :in-theory (union-theories
 '(lw-euler-circle-point-lower lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-egq-native-node-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp margin) (< 0 margin))
 (and (lw-complexp (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) 1 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (lw-complexp (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))
      (<= (* (lw-euler-circle-anchor-min plus-arcs minus-arcs) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-complex-norm-square (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))))))
 :hints (("Goal"
 :use (lw-egq-native-request-data lw-euler-circle-cover-shifted-check
       (:instance lw-complex-euler-local-coefficient-rational (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (index 1) (error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))
       (:instance lw-euler-circle-native-value-clearance (request (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))))
 :in-theory (union-theories
 '( lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-egq-polynomial-node-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= error 1) (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (rationalp margin) (< 0 margin))
 (and (lw-complexp (lw-euler-circle-global-polynomial-value center radius point target error)) (lw-complexp (lw-euler-circle-global-derivative-value center radius point target error))
      (<= (* (lw-euler-circle-anchor-min plus-arcs minus-arcs) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-complex-norm-square (lw-euler-circle-global-polynomial-value center radius point target error)))
      (lw-complex-diskp (lw-euler-circle-global-derivative-value center radius point target error) (lw-euler-circle-global-derivative-cap center radius))
      (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) 1 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)) (lw-euler-circle-global-derivative-value center radius point target error)) (+ error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))
      (lw-complex-diskp (lw-complex-sub (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)) (lw-euler-circle-global-polynomial-value center radius point target error)) (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))))))
 :hints (("Goal"
 :use (lw-egq-native-node-data lw-egq-native-request-data lw-euler-circle-cover-shifted-check
       lw-euler-circle-global-values-rational lw-euler-circle-global-polynomial-clearance lw-euler-circle-global-derivative-bound
       (:instance lw-euler-circle-global-value-comparison (value-error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))
       (:instance lw-euler-circle-global-derivative-comparison (coefficient-radius (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point))))) (coefficient-error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))
       (:instance lw-complex-difference-symmetric (left (lw-euler-circle-global-derivative-value center radius point target error)) (right (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) 1 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (radius (+ error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))))
       (:instance lw-complex-difference-symmetric (left (lw-euler-circle-global-polynomial-value center radius point target error)) (right (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (radius (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))))))
 :in-theory (union-theories
 '( lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-egq-raw-quotient-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= error 1) (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-quotient (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) 1 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)) (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (lw-euler-circle-global-quotient center radius point target error)) (+ (* (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (+ error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))))))
 :hints (("Goal"
 :use (lw-egq-native-node-data lw-egq-polynomial-node-data lw-euler-circle-global-quotient-cost-data
       (:instance lw-complex-quotient-difference-bound (numerator (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) 1 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (denominator (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))
        (approximate-numerator (lw-euler-circle-global-derivative-value center radius point target error)) (approximate-denominator (lw-euler-circle-global-polynomial-value center radius point target error)) (left-clearance (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (right-clearance (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (numerator-cap (lw-euler-circle-global-derivative-cap center radius))
        (numerator-error (+ error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (denominator-error (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))))))
 :in-theory (union-theories
 '(lw-euler-circle-global-quotient lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-egq-native-margin-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= error 1) (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point margin)) (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) (* (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs) margin))))
 :hints (("Goal"
 :use (lw-egq-native-node-data lw-euler-circle-global-quotient-rational
       (:instance lw-complex-quotient-rational (numerator (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) 1 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (denominator (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))))
       lw-egq-native-request-data lw-egq-raw-quotient-comparison lw-euler-circle-global-quotient-cost-data
       (:instance lw-complex-difference-symmetric (left (lw-complex-quotient (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) 1 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)) (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))) (right (lw-euler-circle-global-quotient center radius point target error)) (radius (+ (* (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (+ error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))))))
       (:instance lw-egq-multiply-order (a (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)) (b margin) (factor (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point margin))) (radius (+ (* (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (+ error (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin))) (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 (lw-euler-log-derivative-request (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (* 1/2 (car (lw-complex-add center (lw-complex-scale radius point)))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)) margin)))))) (cap (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) (* (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs) margin)))))
 :in-theory (union-theories
 '(lw-euler-circle-log-value lw-complex-euler-log-derivative-value lw-euler-circle-global-quotient-cost lw-euler-circle-global-node-cost lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-egq-final-with-margin
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= error 1) (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (rationalp value-error) (< 0 value-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (+ (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error) (* (+ 1 (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs)) margin))))
 :hints (("Goal"
 :use (lw-euler-circle-global-quotient-rational lw-euler-circle-log-value-rational
       (:instance lw-euler-circle-log-value-rational (value-error margin))
       lw-euler-circle-global-quotient-cost-data lw-egq-native-margin-comparison
       (:instance lw-euler-circle-log-value-cauchy (left-error margin) (right-error value-error))
       (:instance lw-complex-difference-triangle (left (lw-euler-circle-global-quotient center radius point target error)) (middle (lw-euler-circle-log-value center radius plus-arcs minus-arcs point margin)) (right (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (radius (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) (* (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs) margin))) (other-radius (+ margin value-error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))) (radius (+ (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) (* (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs) margin)) margin value-error)) (cap (+ (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error) (* (+ 1 (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs)) margin)))))
 :in-theory (union-theories
 '( lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-circle-global-log-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= error 1) (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error)))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error)))
 :use (lw-euler-circle-global-quotient-cost-data lw-euler-circle-global-quotient-rational lw-euler-circle-log-value-rational
       (:instance lw-egq-positive-product (a (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs)) (b error))
       (:instance lw-complex-operations-rational (left (lw-euler-circle-global-quotient center radius point target error)) (right (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))) (radius (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error)) (cost (+ 1 (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs))))
       (:instance lw-egq-final-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-euler-circle-global-quotient center radius point target error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error) (+ 1 (lw-euler-circle-global-node-cost center radius plus-arcs minus-arcs))))))
 :in-theory (union-theories
 '( lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defun lw-euler-circle-global-request (center radius plus-arcs minus-arcs output-error)
 (min 1 (min (* (lw-euler-circle-anchor-min plus-arcs minus-arcs) (/ (+ 1 (lw-euler-circle-outer-gap center radius)))) (* output-error (/ (* 2 (+ 1 (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs))))))))
(defun lw-euler-circle-global-log-model (center radius plus-arcs minus-arcs point target output-error)
 (lw-euler-circle-global-quotient center radius point target (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error)))
(local (in-theory (disable lw-euler-circle-global-request lw-euler-circle-global-log-model)))

(local (defthm lw-egq-request-aux
 (implies (and (rationalp m) (< 0 m) (rationalp gap) (< 0 gap) (rationalp cost) (< 0 cost)
 (rationalp output-error) (< 0 output-error))
 (let ((request (min 1 (min (* m (/ (+ 1 gap))) (* output-error (/ (* 2 (+ 1 cost))))))))
 (and (rationalp request) (< 0 request) (<= request 1)
      (<= (* gap request) m) (<= (* cost request) (* 1/2 output-error)))))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-positive (value (+ 1 gap)))
       (:instance lw-reciprocal-positive (value (* 2 (+ 1 cost))))
       (:instance lw-egq-positive-product (a m) (b (/ (+ 1 gap))))
       (:instance lw-egq-positive-product (a output-error) (b (/ (* 2 (+ 1 cost)))))
       (:instance lw-positive-division-bound (numerator (* gap m)) (divisor (+ 1 gap)) (bound m))
       (:instance lw-positive-division-bound (numerator (* cost output-error)) (divisor (* 2 (+ 1 cost))) (bound (* 1/2 output-error)))
       (:instance lw-egq-multiply-order (a (min 1 (min (* m (/ (+ 1 gap))) (* output-error (/ (* 2 (+ 1 cost))))))) (b (* m (/ (+ 1 gap)))) (factor gap))
       (:instance lw-egq-multiply-order (a (min 1 (min (* m (/ (+ 1 gap))) (* output-error (/ (* 2 (+ 1 cost))))))) (b (* output-error (/ (* 2 (+ 1 cost))))) (factor cost)))
 :in-theory (union-theories
 '(min lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-circle-global-request-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (rationalp output-error) (< 0 output-error))
 (and (rationalp (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error)) (< 0 (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error)) (<= (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error) 1)
      (<= (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error)) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (<= (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error)) (* 1/2 output-error))))
 :hints (("Goal"
 :use (lw-euler-circle-global-quotient-cost-data
       (:instance lw-egq-request-aux (m (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (gap (lw-euler-circle-outer-gap center radius)) (cost (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs))))
 :in-theory (union-theories
 '(lw-euler-circle-global-request lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-global-log-model-rational
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp output-error) (< 0 output-error))
 (lw-complexp (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point target output-error)))
 :hints (("Goal" :use (lw-euler-circle-global-request-data
       (:instance lw-euler-circle-global-quotient-rational (error (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error))))
 :in-theory (union-theories
 '(lw-euler-circle-global-log-model lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-global-log-model-cap
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp output-error) (< 0 output-error))
 (lw-complex-diskp (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point target output-error) (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
 :hints (("Goal" :use (lw-euler-circle-global-request-data
       (:instance lw-euler-circle-global-quotient-cap (error (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error))))
 :in-theory (union-theories
 '(lw-euler-circle-global-log-model lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-global-log-model-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp output-error) (< 0 output-error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point target output-error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (+ (* 1/2 output-error) value-error)))
 :hints (("Goal"
 :use (lw-euler-circle-global-request-data lw-euler-circle-global-quotient-cost-data
       (:instance lw-euler-circle-global-log-comparison (error (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point target output-error) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))) (radius (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) (lw-euler-circle-global-request center radius plus-arcs minus-arcs output-error)) value-error)) (cap (+ (* 1/2 output-error) value-error))))
 :in-theory (union-theories
 '(lw-euler-circle-global-log-model lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-global-log-model-computed-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp output-error) (< 0 output-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point target output-error)
 (lw-euler-circle-log-value center radius plus-arcs minus-arcs point (* 1/2 output-error))) output-error))
 :hints (("Goal"
 :use ((:instance lw-euler-circle-global-log-model-comparison (value-error (* 1/2 output-error))))
 :in-theory (union-theories
 '( lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(local (defthm lw-egq-models-with-margin
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp left-target) (natp right-target) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error) (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error)) (+ (* 1/2 (+ left-error right-error)) (* 2 margin))))
 :hints (("Goal"
 :use ((:instance lw-euler-circle-global-log-model-rational (target left-target) (output-error left-error))
       (:instance lw-euler-circle-global-log-model-rational (target right-target) (output-error right-error))
       (:instance lw-euler-circle-log-value-rational (value-error margin))
       (:instance lw-euler-circle-global-log-model-comparison (target left-target) (output-error left-error) (value-error margin))
       (:instance lw-euler-circle-global-log-model-comparison (target right-target) (output-error right-error) (value-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error)) (right (lw-euler-circle-log-value center radius plus-arcs minus-arcs point margin)) (radius (+ (* 1/2 right-error) margin)))
       (:instance lw-complex-difference-triangle (left (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error)) (middle (lw-euler-circle-log-value center radius plus-arcs minus-arcs point margin)) (right (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error)) (radius (+ (* 1/2 left-error) margin)) (other-radius (+ (* 1/2 right-error) margin)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error) (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error))) (radius (+ (* 1/2 left-error) margin (* 1/2 right-error) margin)) (cap (+ (* 1/2 (+ left-error right-error)) (* 2 margin)))))
 :in-theory (union-theories
 '( lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-circle-global-log-model-cauchy
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp left-target) (natp right-target) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error) (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error) (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error)) (* 1/2 (+ left-error right-error))))
 :use ((:instance lw-euler-circle-global-log-model-rational (target left-target) (output-error left-error))
       (:instance lw-euler-circle-global-log-model-rational (target right-target) (output-error right-error))
       (:instance lw-complex-operations-rational (left (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error)) (right (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error) (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error))) (radius (* 1/2 (+ left-error right-error))) (cost 2))
       (:instance lw-egq-models-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point left-target left-error) (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point right-target right-error)) (* 1/2 (+ left-error right-error)) 2))))
 :in-theory (union-theories
 '( lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-euler-circle-global-log-cap (center radius plus-arcs minus-arcs)
 (+ 2 (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
(local (in-theory (disable lw-euler-circle-global-log-cap)))

(defthm lw-euler-circle-log-value-global-cap
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp value-error) (< 0 value-error) (<= value-error 1))
 (and (rationalp (lw-euler-circle-global-log-cap center radius plus-arcs minus-arcs)) (< 0 (lw-euler-circle-global-log-cap center radius plus-arcs minus-arcs)) (lw-complex-diskp (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error) (lw-euler-circle-global-log-cap center radius plus-arcs minus-arcs))))
 :hints (("Goal"
 :use (lw-euler-circle-global-quotient-cost-data lw-euler-circle-log-value-rational
       (:instance lw-egq-positive-product (a (lw-euler-circle-global-derivative-cap center radius)) (b (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
       (:instance lw-euler-circle-global-log-model-rational (target 0) (output-error 1))
       (:instance lw-euler-circle-global-log-model-cap (target 0) (output-error 1))
       (:instance lw-euler-circle-global-log-model-comparison (target 0) (output-error 1))
       (:instance lw-complex-difference-symmetric (left (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point 0 1)) (right (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (radius (+ 1/2 value-error)))
       (:instance lw-complex-difference-triangle (left (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (middle (lw-euler-circle-global-log-model center radius plus-arcs minus-arcs point 0 1)) (right (cons 0 0)) (radius (+ 1/2 value-error)) (other-radius (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
       (:instance lw-complex-disk-enlarge (point (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (radius (+ 1/2 value-error (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))))) (cap (lw-euler-circle-global-log-cap center radius plus-arcs minus-arcs))))
 :in-theory (union-theories
 '(lw-euler-circle-global-log-cap lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)


(defun lw-euler-circle-grid-global-polynomial (center radius count coarse-error target output-error)
 (lw-euler-circle-global-polynomial center radius target (lw-euler-circle-global-request center radius (car (lw-euler-circle-grid center radius count coarse-error)) (cadr (lw-euler-circle-grid center radius count coarse-error)) output-error)))
(defun lw-euler-circle-grid-global-log-model (center radius count coarse-error degree sample target output-error)
 (lw-euler-circle-global-log-model center radius (car (lw-euler-circle-grid center radius count coarse-error)) (cadr (lw-euler-circle-grid center radius count coarse-error)) (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) target output-error))
(local (in-theory (disable lw-euler-circle-grid-global-polynomial lw-euler-circle-grid-global-log-model)))

(defthm lw-euler-circle-grid-global-log-model-identity
 (equal (lw-euler-circle-grid-global-log-model center radius count coarse-error degree sample target output-error)
 (lw-complex-quotient
  (lw-complex-polynomial (lw-polynomial-derivative-coefficients (lw-euler-circle-grid-global-polynomial center radius count coarse-error target output-error)) (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)) 0)
  (lw-complex-polynomial (lw-euler-circle-grid-global-polynomial center radius count coarse-error target output-error) (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)) 0)))
 :hints (("Goal"
 :use ((:instance lw-euler-circle-global-derivative-identity (error (lw-euler-circle-global-request center radius (car (lw-euler-circle-grid center radius count coarse-error)) (cadr (lw-euler-circle-grid center radius count coarse-error)) output-error))))
 :in-theory (union-theories
 '(lw-euler-circle-grid-global-log-model lw-euler-circle-grid-global-polynomial lw-euler-circle-global-log-model lw-euler-circle-global-quotient lw-euler-circle-global-polynomial-value lw-euler-circle-global-derivative-value lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-circle-grid-global-log-model-comparison
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius) (posp count)
 (lw-euler-circle-grid-check center radius 1 count coarse-error 0 count)
 (lw-euler-circle-grid-check center radius -1 count coarse-error 0 count)
 (natp degree) (natp sample) (natp target)
 (rationalp output-error) (< 0 output-error) (rationalp value-error) (< 0 value-error))
 (and (lw-complex-coefficientsp (lw-euler-circle-grid-global-polynomial center radius count coarse-error target output-error))
      (lw-complexp (lw-euler-circle-grid-global-log-model center radius count coarse-error degree sample target output-error))
      (lw-complex-diskp (lw-euler-circle-grid-global-log-model center radius count coarse-error degree sample target output-error) (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min (car (lw-euler-circle-grid center radius count coarse-error)) (cadr (lw-euler-circle-grid center radius count coarse-error))))))
      (lw-complex-diskp (lw-complex-sub (lw-euler-circle-grid-global-log-model center radius count coarse-error degree sample target output-error)
       (lw-euler-circle-log-value center radius (car (lw-euler-circle-grid center radius count coarse-error)) (cadr (lw-euler-circle-grid center radius count coarse-error)) (lw-complex-power (lw-cauchy-orbit-rotation degree) sample) value-error))
       (+ (* 1/2 output-error) value-error))))
 :hints (("Goal"
 :use ((:instance lw-euler-circle-grid-valid (error coarse-error))
       lw-cauchy-orbit-data
       (:instance lw-cauchy-orbit-power-norm-one (index sample))
       (:instance lw-complex-power-rational (point (lw-cauchy-orbit-rotation degree)) (index sample))
       (:instance lw-euler-circle-global-request-data (plus-arcs (car (lw-euler-circle-grid center radius count coarse-error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count coarse-error))))
       (:instance lw-euler-circle-global-polynomials-valid (plus-arcs (car (lw-euler-circle-grid center radius count coarse-error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count coarse-error))) (error (lw-euler-circle-global-request center radius (car (lw-euler-circle-grid center radius count coarse-error)) (cadr (lw-euler-circle-grid center radius count coarse-error)) output-error)))
       (:instance lw-euler-circle-global-log-model-rational (plus-arcs (car (lw-euler-circle-grid center radius count coarse-error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count coarse-error))) (point (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))
       (:instance lw-euler-circle-global-log-model-cap (plus-arcs (car (lw-euler-circle-grid center radius count coarse-error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count coarse-error))) (point (lw-complex-power (lw-cauchy-orbit-rotation degree) sample)))
       (:instance lw-euler-circle-global-log-model-comparison (plus-arcs (car (lw-euler-circle-grid center radius count coarse-error))) (minus-arcs (cadr (lw-euler-circle-grid center radius count coarse-error))) (point (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))
 :in-theory (union-theories
 '(lw-euler-circle-grid-global-log-model lw-euler-circle-grid-global-polynomial lw-egq-left-commutes lw-egq-left-distributes lw-egq-fold-constants lw-egq-times-negative lw-egq-negative-times lw-egq-zero-times lw-egq-minus-one lw-egq-double-negative lw-egq-add-cancel lw-egq-double lw-egq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)





