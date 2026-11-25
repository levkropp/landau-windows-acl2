; One actual global Euler polynomial supplies its own formal derivative on the circle.
(in-package "ACL2")
(include-book "euler-circle-clearance")
(include-book "euler-uniform-derivative-bounds")
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
(local (defthm lw-egp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-egp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-egp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-egp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-egp-times-negative (a b) (b a)))
                 :in-theory (disable lw-egp-times-negative)))))

(local (defthm lw-egp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-egp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-egp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-egp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-egp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-egp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-egp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-egp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-egp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-egp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-egp-left-commutes)))))
(defun lw-euler-circle-global-polynomial (center radius target error)
 (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) target (* (lw-euler-circle-outer-gap center radius) error)))
(defun lw-euler-circle-global-derivative (center radius target error)
 (lw-euler-uniform-derivative-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) radius target error))
(defun lw-euler-circle-global-polynomial-value (center radius point target error)
 (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) (lw-complex-scale radius point) 0))
(defun lw-euler-circle-global-derivative-value (center radius point target error)
 (lw-complex-polynomial (lw-euler-circle-global-derivative center radius target error) (lw-complex-scale radius point) 0))
(defun lw-euler-circle-global-derivative-cap (center radius)
 (+ 2 (lw-euler-uniform-derivative-cap (car center) (cdr center) (lw-euler-circle-outer-radius center radius) radius)))
(local (in-theory (disable lw-euler-circle-global-polynomial lw-euler-circle-global-derivative lw-euler-circle-global-polynomial-value lw-euler-circle-global-derivative-value lw-euler-circle-global-derivative-cap
 lw-euler-circle-coverp lw-euler-circle-anchor-min lw-euler-circle-point-lower lw-euler-circle-outer-radius lw-euler-circle-outer-gap
 lw-euler-circle-cover-patch lw-euler-contour-anchor lw-euler-value-clearance-lower lw-euler-value-clearance-size
 lw-euler-uniform-derivative-polynomial lw-euler-uniform-derivative-cap lw-polynomial-derivative-coefficients)))

(defthm lw-euler-circle-global-derivative-identity
 (equal (lw-euler-circle-global-derivative center radius target error) (lw-polynomial-derivative-coefficients (lw-euler-circle-global-polynomial center radius target error)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-euler-circle-global-derivative lw-euler-circle-global-polynomial lw-euler-circle-outer-gap lw-euler-uniform-derivative-polynomial lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-circle-global-shift-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (and (lw-complexp (lw-complex-scale radius point)) (lw-complex-diskp (lw-complex-scale radius point) radius) (lw-complex-diskp (lw-complex-scale radius point) (lw-euler-circle-outer-radius center radius))
      (lw-complexp (lw-complex-add center (lw-complex-scale radius point))) (rationalp (car (lw-complex-add center (lw-complex-scale radius point)))) (< 0 (car (lw-complex-add center (lw-complex-scale radius point)))) (rationalp (cdr (lw-complex-add center (lw-complex-scale radius point))))))
 :hints (("Goal"
 :use (lw-euler-circle-cover-shifted-check lw-euler-circle-outer-data
       (:instance lw-complex-disk-norm-square (radius 1))
       (:instance lw-complex-scale-disk (factor radius) (radius 1))
       (:instance lw-complex-disk-data (point (lw-complex-scale radius point)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-scale radius point)) (cap (lw-euler-circle-outer-radius center radius))))
 :in-theory (union-theories
 '(abs lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-global-polynomials-valid
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (natp target) (rationalp error) (< 0 error))
 (and (lw-complex-coefficientsp (lw-euler-circle-global-polynomial center radius target error)) (lw-complex-coefficientsp (lw-euler-circle-global-derivative center radius target error))))
 :hints (("Goal"
 :use (lw-euler-circle-outer-data
       (:instance lw-egp-positive-product (a (lw-euler-circle-outer-gap center radius)) (b error))
       (:instance lw-euler-uniform-polynomial-valid (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius)) (error (* (lw-euler-circle-outer-gap center radius) error)))
       (:instance lw-euler-uniform-derivative-polynomial-valid (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (inner-radius radius)))
 :in-theory (union-theories
 '(lw-euler-circle-global-polynomial lw-euler-circle-global-derivative lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-global-values-rational
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error))
 (and (lw-complexp (lw-euler-circle-global-polynomial-value center radius point target error)) (lw-complexp (lw-euler-circle-global-derivative-value center radius point target error))))
 :hints (("Goal"
 :use (lw-euler-circle-global-shift-data lw-euler-circle-global-polynomials-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-global-polynomial center radius target error)) (point (lw-complex-scale radius point)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-global-derivative center radius target error)) (point (lw-complex-scale radius point)) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-circle-global-polynomial-value lw-euler-circle-global-derivative-value lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-global-value-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-polynomial-value center radius point target error)
 (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) value-error))
 (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 value-error))))
 :hints (("Goal"
 :use (lw-euler-circle-outer-data lw-euler-circle-global-shift-data
       (:instance lw-egp-positive-product (a (lw-euler-circle-outer-gap center radius)) (b error))
       (:instance lw-complex-euler-uniform-polynomial-comparison (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius)) (point (lw-complex-scale radius point)) (error (* (lw-euler-circle-outer-gap center radius) error))))
 :in-theory (union-theories
 '(lw-euler-circle-global-polynomial-value lw-euler-circle-global-polynomial lw-complexp lw-complex-add lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-global-derivative-comparison
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (car (lw-complex-add center (lw-complex-scale radius point))))
 (rationalp coefficient-error) (< 0 coefficient-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-circle-global-derivative-value center radius point target error)
 (lw-complex-euler-local-coefficient-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) coefficient-radius 1 coefficient-error))
 (+ error coefficient-error)))
 :hints (("Goal"
 :use (lw-euler-circle-outer-data lw-euler-circle-global-shift-data
       (:instance lw-complex-euler-uniform-derivative-comparison (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (inner-radius radius) (center (lw-complex-scale radius point))))
 :in-theory (union-theories
 '(lw-euler-circle-global-derivative-value lw-euler-circle-global-derivative lw-complexp lw-complex-add lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-global-derivative-cap-data
 (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (and (rationalp (lw-euler-circle-global-derivative-cap center radius)) (< 0 (lw-euler-circle-global-derivative-cap center radius))))
 :hints (("Goal"
 :use (lw-euler-circle-outer-data
       (:instance lw-euler-uniform-derivative-cap-valid (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (inner-radius radius)))
 :in-theory (union-theories
 '(lw-euler-circle-global-derivative-cap lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-euler-circle-global-derivative-bound
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= error 1))
 (lw-complex-diskp (lw-euler-circle-global-derivative-value center radius point target error) (lw-euler-circle-global-derivative-cap center radius)))
 :hints (("Goal"
 :use (lw-euler-circle-outer-data lw-euler-circle-global-shift-data
       (:instance lw-complex-euler-uniform-derivative-polynomial-cap (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (inner-radius radius) (center (lw-complex-scale radius point))))
 :in-theory (union-theories
 '(lw-euler-circle-global-derivative-value lw-euler-circle-global-derivative lw-euler-circle-global-derivative-cap lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-egp-square-order
 (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right))
 (<= (* left left) (* right right)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-circle-global-polynomial-clearance
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
 (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp target) (rationalp error) (< 0 error) (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
 (and (lw-complexp (lw-euler-circle-global-polynomial-value center radius point target error)) (not (equal (lw-euler-circle-global-polynomial-value center radius point target error) (cons 0 0)))
      (<= (* (lw-euler-circle-anchor-min plus-arcs minus-arcs) (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-complex-norm-square (lw-euler-circle-global-polynomial-value center radius point target error)))
      (lw-complex-diskp (lw-complex-reciprocal (lw-euler-circle-global-polynomial-value center radius point target error)) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
 :hints (("Goal"
 :use (lw-euler-circle-global-values-rational lw-euler-circle-anchor-min-data lw-euler-circle-point-lower-data
       (:instance lw-euler-circle-global-value-comparison (value-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))
       (:instance lw-euler-value-clearance-data (rate (car (lw-complex-add center (lw-complex-scale radius point)))) (height (cdr (lw-complex-add center (lw-complex-scale radius point)))) (anchor-error (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-circle-global-polynomial-value center radius point target error) (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))) (radius (+ (* (lw-euler-circle-outer-gap center radius) error) (* 1/4 (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs))))) (cap (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point)))
       (:instance lw-complex-disk-anchor-clearance (anchor (lw-complex-euler-continuation-value (car (lw-complex-add center (lw-complex-scale radius point))) (cdr (lw-complex-add center (lw-complex-scale radius point))) (lw-euler-contour-anchor (lw-euler-circle-cover-patch point plus-arcs minus-arcs)))) (point (lw-euler-circle-global-polynomial-value center radius point target error)))
       (:instance lw-egp-square-order (left (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (right (lw-euler-circle-point-lower center radius plus-arcs minus-arcs point)))
       (:instance lw-complex-reciprocal-disk-bound (point (lw-euler-circle-global-polynomial-value center radius point target error)) (lower (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
 :in-theory (union-theories
 '(lw-euler-circle-point-lower lw-euler-value-clearance-lower lw-euler-value-clearance-size lw-egp-left-commutes lw-egp-left-distributes lw-egp-fold-constants lw-egp-times-negative lw-egp-negative-times lw-egp-zero-times lw-egp-minus-one lw-egp-double-negative lw-egp-add-cancel lw-egp-double lw-egp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

