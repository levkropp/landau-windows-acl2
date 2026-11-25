; One computed local polynomial interface, including the removable center.
(in-package "ACL2")
(include-book "euler-normalized-polynomial")
(include-book "euler-removable-polynomial")
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
 lw-euler-normalized-disk-radius lw-euler-normalized-polynomial
 lw-euler-removable-radius lw-euler-removable-numerator-cap lw-euler-removable-polynomial
 lw-normalized-local-cap lw-euler-uniform-log-cap lw-complex-polynomial
 lw-mellin-euler-log-extended-value)))
(local (defthm lw-eln-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eln-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eln-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eln-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eln-times-negative (a b) (b a)))
                 :in-theory (disable lw-eln-times-negative)))))

(local (defthm lw-eln-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eln-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eln-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eln-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eln-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eln-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eln-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eln-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eln-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eln-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eln-left-commutes)))))
(defun lw-euler-local-normalized-radius (rate height outer-radius anchor-error)
 (if (and (equal rate 1) (equal height 0)) (* 1/2 (lw-euler-removable-radius)) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
(defun lw-euler-local-normalized-cap (rate height outer-radius anchor-error)
 (if (and (equal rate 1) (equal height 0)) (* 8 (lw-euler-removable-numerator-cap)) (lw-normalized-local-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error))))
(defun lw-euler-local-normalized-anchor (rate height anchor-error)
 (if (and (equal rate 1) (equal height 0)) 1/128 (* 1/2 anchor-error)))
(defun lw-euler-local-normalized-polynomial (rate height outer-radius anchor-error target error)
 (if (and (equal rate 1) (equal height 0)) (lw-euler-removable-polynomial target error)
  (lw-euler-normalized-polynomial rate height outer-radius anchor-error target error)))
(local (in-theory (disable lw-euler-local-normalized-radius lw-euler-local-normalized-cap
 lw-euler-local-normalized-anchor lw-euler-local-normalized-polynomial)))
(defthm lw-euler-local-normalized-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate))
 (and (rationalp rate) (< 0 rate) (rationalp height)
      (rationalp (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (< 0 (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (< (lw-euler-local-normalized-radius rate height outer-radius anchor-error) rate) (<= (lw-euler-local-normalized-radius rate height outer-radius anchor-error) 1)
      (rationalp (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (< 0 (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (rationalp (lw-euler-local-normalized-anchor rate height anchor-error)) (< 0 (lw-euler-local-normalized-anchor rate height anchor-error))))
 :hints (("Goal" :cases ((and (equal rate 1) (equal height 0)))
 :use (lw-euler-removable-neighborhood-data lw-euler-value-clearance-data lw-euler-normalized-disk-data)
 :in-theory (union-theories
 '(lw-euler-local-normalized-radius lw-euler-local-normalized-cap lw-euler-local-normalized-anchor lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
(local (defthm lw-eln-removable-point-data
 (implies (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius)))
 (and (lw-complexp point) (rationalp (+ 1 (car point))) (< 0 (+ 1 (car point))) (rationalp (cdr point))
      (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) 1/128)))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data
       (:instance lw-complex-disk-data (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-disk-enlarge (radius (* 1/2 (lw-euler-removable-radius))) (cap (lw-euler-removable-radius)))
       (:instance lw-euler-disk-point-data (rate 1) (height 0) (radius (* 1/2 (lw-euler-removable-radius))) (offset point))
       (:instance lw-euler-neighborhood-shifted-check (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64)))
 :in-theory (union-theories
 '(lw-euler-removable-radius lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-euler-local-normalized-point-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-local-normalized-radius rate height outer-radius anchor-error)))
 (and (lw-complexp point) (rationalp (+ rate (car point))) (< 0 (+ rate (car point))) (rationalp (+ height (cdr point)))
      (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) (lw-euler-local-normalized-anchor rate height anchor-error))))
 :hints (("Goal" :cases ((and (equal rate 1) (equal height 0)))
 :use (lw-eln-removable-point-data lw-euler-normalized-point-data lw-euler-neighborhood-shifted-check)
 :in-theory (union-theories
 '(lw-euler-local-normalized-radius lw-euler-local-normalized-anchor lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-local-normalized-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error)))
 :hints (("Goal" :cases ((and (equal rate 1) (equal height 0)))
 :use (lw-euler-removable-polynomial-valid lw-euler-normalized-polynomial-valid)
 :in-theory (union-theories
 '(lw-euler-local-normalized-polynomial lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-local-normalized-polynomial-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-local-normalized-radius rate height outer-radius anchor-error)))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
 :hints (("Goal" :cases ((and (equal rate 1) (equal height 0)))
 :use (lw-complex-euler-removable-polynomial-cap lw-complex-euler-normalized-polynomial-cap)
 :in-theory (union-theories
 '(lw-euler-local-normalized-radius lw-euler-local-normalized-cap lw-euler-local-normalized-polynomial lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-local-normalized-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-local-normalized-radius rate height outer-radius anchor-error))
 (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point)))
 (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error))
  (* 1/2 (+ error value-error))))
 :hints (("Goal" :cases ((and (equal rate 1) (equal height 0)))
 :use (lw-euler-local-normalized-point-data lw-complex-euler-removable-polynomial-comparison lw-complex-euler-normalized-uniform-comparison)
 :in-theory (union-theories
 '(lw-complexp lw-euler-local-normalized-radius lw-euler-local-normalized-polynomial lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(local (defthm lw-eln-polynomial-cauchy-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (+ (* 1/2 (+ left-error right-error)) margin)))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data lw-euler-local-normalized-point-data
       (:instance lw-euler-local-normalized-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-local-normalized-polynomial-valid (target right-target) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)) (offset 0))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car point))) (height (+ height (cdr point)))
        (radius (* 1/2 (+ rate (car point)))) (anchor-error (lw-euler-local-normalized-anchor rate height anchor-error)) (error margin))
       (:instance lw-complex-euler-local-normalized-comparison (target left-target) (error left-error)
        (local-anchor (lw-euler-local-normalized-anchor rate height anchor-error)) (coefficient-radius (* 1/2 (+ rate (car point)))) (value-error margin))
       (:instance lw-complex-euler-local-normalized-comparison (target right-target) (error right-error)
        (local-anchor (lw-euler-local-normalized-anchor rate height anchor-error)) (coefficient-radius (* 1/2 (+ rate (car point)))) (value-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (right (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) (* 1/2 (+ rate (car point))) (lw-euler-local-normalized-anchor rate height anchor-error) margin)) (radius (* 1/2 (+ right-error margin))))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) point 0)) (middle (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) (* 1/2 (+ rate (car point))) (lw-euler-local-normalized-anchor rate height anchor-error) margin)) (right (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0))
        (radius (* 1/2 (+ left-error margin))) (other-radius (* 1/2 (+ right-error margin)))))
 :in-theory (union-theories
 '(lw-complexp lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-local-normalized-polynomial-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (* 1/2 (+ left-error right-error))))
 :use (lw-euler-local-normalized-point-data
       (:instance lw-euler-local-normalized-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-local-normalized-polynomial-valid (target right-target) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)) (offset 0))
       (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) point 0)) (right (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0))) (radius (* 1/2 (+ left-error right-error))) (cost 1))
       (:instance lw-eln-polynomial-cauchy-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (* 1/2 (+ left-error right-error)) 1))))
 :in-theory (union-theories
 '( lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-mellin-euler-log-extended-neighborhood-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-local-normalized-radius rate height outer-radius anchor-error))
 (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point)))
 (rationalp value-error) (< 0 value-error) (<= value-error 1))
 (lw-complex-diskp (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error) (+ 1 (lw-euler-local-normalized-cap rate height outer-radius anchor-error))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data lw-euler-local-normalized-point-data
       (:instance lw-euler-local-normalized-polynomial-valid (target 0) (error 1))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error 0 1)) (offset 0))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car point))) (height (+ height (cdr point)))
        (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-euler-local-normalized-polynomial-cap (target 0) (error 1))
       (:instance lw-complex-euler-local-normalized-comparison (target 0) (error 1))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error 0 1) point 0) (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)))
        (radius (* 1/2 (+ 1 value-error))) (cap 1))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error 0 1) point 0)) (right (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (radius 1))
       (:instance lw-complex-difference-triangle (left (lw-mellin-euler-log-extended-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (middle (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error 0 1) point 0)) (right (cons 0 0))
        (radius 1) (other-radius (lw-euler-local-normalized-cap rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-eln-left-commutes lw-eln-left-distributes lw-eln-fold-constants lw-eln-times-negative lw-eln-negative-times lw-eln-zero-times lw-eln-minus-one lw-eln-double-negative lw-eln-add-cancel lw-eln-double lw-eln-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


