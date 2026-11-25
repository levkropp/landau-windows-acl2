; Actual polynomial models of the normalized Euler family through one.
(in-package "ACL2")
(include-book "linear-inverse-polynomials")
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
(local (in-theory (disable lw-euler-removable-radius lw-euler-removable-numerator-cap
 lw-euler-removable-numerator lw-euler-removable-model-value lw-linear-inverse-polynomial
 lw-linear-inverse-cap lw-euler-rounding-precision lw-polynomial-product
 lw-complex-polynomial lw-complex-quotient lw-euler-value-clearance-check
 lw-mellin-euler-log-extended-value)))
(local (defthm lw-erp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erp-times-negative (a b) (b a)))
                 :in-theory (disable lw-erp-times-negative)))))

(local (defthm lw-erp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erp-left-commutes)))))

(defun lw-euler-removable-inverse-request (error)
 (lw-euler-rounding-precision (lw-euler-removable-numerator-cap) (* 1/2 error)))
(local (in-theory (disable lw-euler-removable-inverse-request)))

(defthm lw-euler-removable-inverse-request-data
 (implies (and (rationalp error) (< 0 error))
 (and (rationalp (lw-euler-removable-inverse-request error)) (< 0 (lw-euler-removable-inverse-request error)) (<= (lw-euler-removable-inverse-request error) 1)
      (<= (* (lw-euler-removable-numerator-cap) (lw-euler-removable-inverse-request error)) (* 1/4 error))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data
       (:instance lw-euler-rounding-precision-valid (cost (lw-euler-removable-numerator-cap)) (error (* 1/2 error))))
 :in-theory (union-theories
 '(lw-euler-removable-inverse-request lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-euler-removable-polynomial (target error)
 (lw-polynomial-product (lw-euler-removable-numerator target (* 1/2 error)) (lw-linear-inverse-polynomial (cons 1 0) (lw-euler-removable-inverse-request error))))
(local (in-theory (disable lw-euler-removable-polynomial)))

(defthm lw-euler-removable-polynomial-valid
 (implies (and (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-removable-polynomial target error)))
 :hints (("Goal"
 :use ((:instance lw-euler-removable-numerator-valid (error (* 1/2 error)))
       (:instance lw-linear-inverse-polynomial-valid (anchor (cons 1 0)) (error (lw-euler-removable-inverse-request error)))
       (:instance lw-polynomial-product-valid (left (lw-euler-removable-numerator target (* 1/2 error))) (right (lw-linear-inverse-polynomial (cons 1 0) (lw-euler-removable-inverse-request error)))))
 :in-theory (union-theories
 '(lw-euler-removable-polynomial (:executable-counterpart lw-complexp) lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-polynomial-cap
 (implies (and (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-removable-polynomial target error) point 0) (* 8 (lw-euler-removable-numerator-cap))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-denominator-clearance
       (:instance lw-euler-removable-numerator-valid (error (* 1/2 error)))
       (:instance lw-complex-euler-removable-numerator-cap (error (* 1/2 error)))
       (:instance lw-linear-inverse-polynomial-valid (anchor (cons 1 0)) (error (lw-euler-removable-inverse-request error)))
       (:instance lw-linear-inverse-polynomial-cap (anchor (cons 1 0)) (radius (* 1/2 (lw-euler-removable-radius))) (error (lw-euler-removable-inverse-request error)))
       (:instance lw-polynomial-product-evaluation (left (lw-euler-removable-numerator target (* 1/2 error))) (right (lw-linear-inverse-polynomial (cons 1 0) (lw-euler-removable-inverse-request error))))
       (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-euler-removable-numerator target (* 1/2 error)) point 0)) (right (lw-complex-polynomial (lw-linear-inverse-polynomial (cons 1 0) (lw-euler-removable-inverse-request error)) point 0)) (radius (lw-euler-removable-numerator-cap)) (other-radius 8)))
 :in-theory (union-theories
 '(lw-euler-removable-polynomial (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-l1) (:executable-counterpart lw-linear-inverse-cap) lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-polynomial-model-error
 (implies (and (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-model-value point target (* 1/2 error)) (lw-complex-polynomial (lw-euler-removable-polynomial target error) point 0)) (* 1/4 error)))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-denominator-clearance lw-euler-removable-inverse-request-data
       (:instance lw-euler-removable-numerator-valid (error (* 1/2 error)))
       (:instance lw-complex-euler-removable-numerator-cap (error (* 1/2 error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-removable-numerator target (* 1/2 error))) (offset 0))
       (:instance lw-linear-inverse-polynomial-valid (anchor (cons 1 0)) (error (lw-euler-removable-inverse-request error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-linear-inverse-polynomial (cons 1 0) (lw-euler-removable-inverse-request error))) (offset 0))
       (:instance lw-linear-inverse-polynomial-error (anchor (cons 1 0)) (radius (* 1/2 (lw-euler-removable-radius))) (error (lw-euler-removable-inverse-request error)))
       (:instance lw-polynomial-product-evaluation (left (lw-euler-removable-numerator target (* 1/2 error))) (right (lw-linear-inverse-polynomial (cons 1 0) (lw-euler-removable-inverse-request error))))
       (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-euler-removable-numerator target (* 1/2 error)) point 0)) (right (lw-complex-sub (lw-complex-reciprocal (lw-complex-add (cons 1 0) point)) (lw-complex-polynomial (lw-linear-inverse-polynomial (cons 1 0) (lw-euler-removable-inverse-request error)) point 0))) (radius (lw-euler-removable-numerator-cap)) (other-radius (lw-euler-removable-inverse-request error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-removable-model-value point target (* 1/2 error)) (lw-complex-polynomial (lw-euler-removable-polynomial target error) point 0))) (radius (* (lw-euler-removable-numerator-cap) (lw-euler-removable-inverse-request error))) (cap (* 1/4 error))))
 :in-theory (union-theories
 '(lw-euler-removable-polynomial lw-euler-removable-model-value lw-complex-quotient lw-complex-mul-subtract lw-complex-ring-rational lw-complex-reciprocal-rational (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-l1) lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-polynomial-comparison
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius)))
 (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point))) (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-removable-polynomial target error) point 0) (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use (lw-euler-removable-denominator-clearance lw-euler-removable-polynomial-valid
       lw-complex-euler-removable-polynomial-model-error
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-removable-polynomial target error)) (offset 0))
       (:instance lw-euler-removable-model-value-rational (error (* 1/2 error)))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ 1 (car point))) (height (cdr point)) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-euler-removable-extended-model-comparison (error (* 1/2 error)))
       (:instance lw-complex-difference-symmetric (left (lw-euler-removable-model-value point target (* 1/2 error))) (right (lw-complex-polynomial (lw-euler-removable-polynomial target error) point 0)) (radius (* 1/4 error)))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-removable-polynomial target error) point 0)) (middle (lw-euler-removable-model-value point target (* 1/2 error))) (right (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error))
        (radius (* 1/4 error)) (other-radius (* 1/2 (+ (* 1/2 error) value-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-removable-polynomial target error) point 0) (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)))
        (radius (+ (* 1/4 error) (* 1/2 (+ (* 1/2 error) value-error))))
        (cap (* 1/2 (+ error value-error)))))
 :in-theory (union-theories
 '( lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-mellin-euler-log-extended-local-cap
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius)))
 (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point))) (rationalp value-error) (< 0 value-error) (<= value-error 1))
 (lw-complex-diskp (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error) (+ 1 (* 4 (lw-euler-removable-numerator-cap)))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-denominator-clearance
       (:instance lw-euler-removable-model-value-rational (target 0) (error 1))
       (:instance lw-complex-euler-removable-model-value-cap (target 0) (error 1))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ 1 (car point))) (height (cdr point)) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-euler-removable-extended-model-comparison (target 0) (error 1))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-removable-model-value point 0 1) (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)))
        (radius (* 1/2 (+ 1 value-error))) (cap 1))
       (:instance lw-complex-difference-symmetric (left (lw-euler-removable-model-value point 0 1)) (right (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (radius 1))
       (:instance lw-complex-difference-triangle (left (lw-mellin-euler-log-extended-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (middle (lw-euler-removable-model-value point 0 1)) (right (cons 0 0))
        (radius 1) (other-radius (* 4 (lw-euler-removable-numerator-cap)))))
 :in-theory (union-theories
 '(lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

