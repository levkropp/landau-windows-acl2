; Canonical Cauchy coefficients of the actual normalized Euler models.
(in-package "ACL2")
(include-book "euler-local-normalized-coefficients")
(include-book "polynomial-capped-coefficients")
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
 lw-euler-local-normalized-radius lw-euler-local-normalized-cap lw-euler-local-normalized-polynomial
 lw-euler-local-normalized-coefficient-polynomial lw-euler-local-normalized-difference-count
 lw-euler-local-normalized-difference-polynomial lw-polynomial-rescale
 lw-complex-coefficient-at lw-polynomial-coefficient-caps)))
(local (defthm lw-ncv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ncv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ncv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ncv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ncv-times-negative (a b) (b a)))
                 :in-theory (disable lw-ncv-times-negative)))))

(local (defthm lw-ncv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ncv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ncv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ncv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ncv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ncv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ncv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ncv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ncv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ncv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ncv-left-commutes)))))
(defun lw-complex-euler-local-normalized-polynomial-coefficient
 (rate height outer-radius anchor-error target index error)
 (lw-complex-coefficient-at (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error) index 0))
(local (in-theory (disable lw-complex-euler-local-normalized-polynomial-coefficient)))
(defthm lw-complex-euler-local-normalized-polynomial-coefficient-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (natp index) (rationalp error) (< 0 error))
 (lw-complexp (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error target index error)))
 :hints (("Goal"
 :use (lw-euler-local-normalized-coefficient-polynomial-valid
       (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (target index) (offset 0)))
 :in-theory (union-theories
 '(lw-complex-euler-local-normalized-polynomial-coefficient lw-ncv-left-commutes lw-ncv-left-distributes lw-ncv-fold-constants lw-ncv-times-negative lw-ncv-negative-times lw-ncv-zero-times lw-ncv-minus-one lw-ncv-double-negative lw-ncv-add-cancel lw-ncv-double lw-ncv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-local-normalized-polynomial-coefficient-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (natp index) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error target index error) (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data lw-euler-local-normalized-coefficient-polynomial-valid
       lw-euler-local-normalized-polynomial-coefficient-caps
       (:instance lw-polynomial-capped-coefficient-at (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (target index) (offset 0)))
 :in-theory (union-theories
 '(lw-complex-euler-local-normalized-polynomial-coefficient lw-ncv-left-commutes lw-ncv-left-distributes lw-ncv-fold-constants lw-ncv-times-negative lw-ncv-negative-times lw-ncv-zero-times lw-ncv-minus-one lw-ncv-double-negative lw-ncv-add-cancel lw-ncv-double lw-ncv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-local-normalized-polynomial-coefficient-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error left-target index left-error) (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error right-target index right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data lw-euler-local-normalized-difference-polynomial-data
       lw-euler-local-normalized-polynomial-difference-coefficient-caps
       (:instance lw-euler-local-normalized-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-local-normalized-polynomial-valid (target right-target) (error right-error))
       (:instance lw-polynomial-disk-difference-capped-coefficient
        (left (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error left-target left-error)) (right (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error right-target right-error)) (radius (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (count (lw-euler-local-normalized-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (cap (* 1/2 (+ left-error right-error)))))
 :in-theory (union-theories
 '(lw-complex-euler-local-normalized-polynomial-coefficient lw-euler-local-normalized-coefficient-polynomial lw-euler-local-normalized-difference-polynomial lw-ncv-left-commutes lw-ncv-left-distributes lw-ncv-fold-constants lw-ncv-times-negative lw-ncv-negative-times lw-ncv-zero-times lw-ncv-minus-one lw-ncv-double-negative lw-ncv-add-cancel lw-ncv-double lw-ncv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
(defun lw-complex-euler-local-normalized-coefficient-value
 (rate height outer-radius anchor-error index error)
 (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error index index error))
(local (in-theory (disable lw-complex-euler-local-normalized-coefficient-value)))
(defthm lw-complex-euler-local-normalized-coefficient-value-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp error) (< 0 error))
 (lw-complexp (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index error)))
 :hints (("Goal"
 :use ((:instance lw-complex-euler-local-normalized-polynomial-coefficient-rational (target index)))
 :in-theory (union-theories
 '(lw-complex-euler-local-normalized-coefficient-value lw-ncv-left-commutes lw-ncv-left-distributes lw-ncv-fold-constants lw-ncv-times-negative lw-ncv-negative-times lw-ncv-zero-times lw-ncv-minus-one lw-ncv-double-negative lw-ncv-add-cancel lw-ncv-double lw-ncv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-local-normalized-coefficient-value-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index error) (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
 :hints (("Goal"
 :use ((:instance lw-complex-euler-local-normalized-polynomial-coefficient-cap (target index)))
 :in-theory (union-theories
 '(lw-complex-euler-local-normalized-coefficient-value lw-ncv-left-commutes lw-ncv-left-distributes lw-ncv-fold-constants lw-ncv-times-negative lw-ncv-negative-times lw-ncv-zero-times lw-ncv-minus-one lw-ncv-double-negative lw-ncv-add-cancel lw-ncv-double lw-ncv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-local-normalized-coefficient-value-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use ((:instance lw-complex-euler-local-normalized-polynomial-coefficient-cauchy (left-target index) (right-target index)))
 :in-theory (union-theories
 '(lw-complex-euler-local-normalized-coefficient-value lw-ncv-left-commutes lw-ncv-left-distributes lw-ncv-fold-constants lw-ncv-times-negative lw-ncv-negative-times lw-ncv-zero-times lw-ncv-minus-one lw-ncv-double-negative lw-ncv-add-cancel lw-ncv-double lw-ncv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-local-normalized-coefficient-polynomial-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (natp target) (rationalp coefficient-error) (< 0 coefficient-error) (rationalp polynomial-error) (< 0 polynomial-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error target index polynomial-error))
  (* 1/2 (+ coefficient-error polynomial-error))))
 :hints (("Goal"
 :use ((:instance lw-complex-euler-local-normalized-polynomial-coefficient-cauchy
        (left-target index) (right-target target) (left-error coefficient-error) (right-error polynomial-error)))
 :in-theory (union-theories
 '(lw-complex-euler-local-normalized-coefficient-value lw-ncv-left-commutes lw-ncv-left-distributes lw-ncv-fold-constants lw-ncv-times-negative lw-ncv-negative-times lw-ncv-zero-times lw-ncv-minus-one lw-ncv-double-negative lw-ncv-add-cancel lw-ncv-double lw-ncv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
