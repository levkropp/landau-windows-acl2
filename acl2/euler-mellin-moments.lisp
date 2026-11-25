; Identify every actual Mellin moment with its normalized Euler coefficient.
(in-package "ACL2")
(include-book "euler-mellin-coefficient-comparison")
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
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-local-normalized-radius lw-euler-mellin-radius
 lw-euler-local-normalized-polynomial lw-euler-mellin-polynomial lw-mellin-improper-polynomial
 lw-complex-euler-normalized-physical-coefficient-value lw-complex-coefficient-at
 lw-mellin-integral lw-rational-power lw-euler-mellin-comparison-error)))
(local (defthm lw-emm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emm-times-negative (a b) (b a)))
                 :in-theory (disable lw-emm-times-negative)))))

(local (defthm lw-emm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-emm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-emm-left-commutes)))))
(defun lw-complex-euler-mellin-coefficient-value (rate height outer-radius anchor-error index error)
 (lw-complex-scale (lw-rational-power -1 index) (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index error)))
(defun lw-euler-mellin-moment-cost (rate height outer-radius anchor-error index)
 (+ 1 (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (* 2 (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)))))
(local (in-theory (disable lw-complex-euler-mellin-coefficient-value lw-euler-mellin-moment-cost)))
(defthm lw-complex-euler-mellin-coefficient-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp error) (< 0 error))
 (lw-complexp (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index error)))
 :hints (("Goal"
 :use (lw-euler-mellin-sign-data lw-complex-euler-normalized-physical-coefficient-rational
       (:instance lw-complex-scale-rational (point (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index error)) (factor (lw-rational-power -1 index))))
 :in-theory (union-theories
 '(lw-complex-euler-mellin-coefficient-value lw-emm-left-commutes lw-emm-left-distributes lw-emm-fold-constants lw-emm-times-negative lw-emm-negative-times lw-emm-zero-times lw-emm-minus-one lw-emm-double-negative lw-emm-add-cancel lw-emm-double lw-emm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-mellin-coefficient-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-mellin-sign-data lw-complex-euler-normalized-physical-coefficient-cauchy
       (:instance lw-complex-euler-normalized-physical-coefficient-rational (error left-error))
       (:instance lw-complex-euler-normalized-physical-coefficient-rational (error right-error))
       (:instance lw-complex-scale-disk
        (point (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index right-error)))
        (factor (lw-rational-power -1 index)) (radius (* 1/2 (+ left-error right-error)))))
 :in-theory (union-theories
 '(lw-complex-euler-mellin-coefficient-value lw-complex-sub-scales lw-emm-left-commutes lw-emm-left-distributes lw-emm-fold-constants lw-emm-times-negative lw-emm-negative-times lw-emm-zero-times lw-emm-minus-one lw-emm-double-negative lw-emm-add-cancel lw-emm-double lw-emm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-mellin-moment-cost-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp index))
 (and (rationalp (lw-euler-mellin-moment-cost rate height outer-radius anchor-error index)) (< 0 (lw-euler-mellin-moment-cost rate height outer-radius anchor-error index))))
 :hints (("Goal" :use (lw-euler-mellin-coefficient-gains-data)
 :in-theory (union-theories
 '(lw-euler-mellin-moment-cost lw-emm-left-commutes lw-emm-left-distributes lw-emm-fold-constants lw-emm-times-negative lw-emm-negative-times lw-emm-zero-times lw-emm-minus-one lw-emm-double-negative lw-emm-add-cancel lw-emm-double lw-emm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(local (defthm lw-emm-physical-reflected-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp coefficient-error) (< 0 coefficient-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-coefficient-at (lw-euler-mellin-polynomial rate height outer-radius anchor-error index margin) index 0))
  (+ (* 1/2 coefficient-error) (* 1/2 margin (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))))))
 :hints (("Goal"
 :use (lw-euler-mellin-sign-data
       (:instance lw-euler-local-normalized-polynomial-valid (target index) (error margin))
       (:instance lw-complex-euler-normalized-physical-coefficient-rational (error coefficient-error))
       (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error index margin)) (target index) (offset 0))
       (:instance lw-complex-euler-normalized-physical-polynomial-comparison (target index) (polynomial-error margin))
       (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error index margin) index 0))) (factor (lw-rational-power -1 index))
        (radius (+ (* 1/2 coefficient-error) (* 1/2 margin (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))))))
 :in-theory (union-theories
 '(lw-complex-euler-mellin-coefficient-value lw-euler-mellin-polynomial-coefficient lw-complex-sub-scales lw-complex-scale-rational lw-emm-left-commutes lw-emm-left-distributes lw-emm-fold-constants lw-emm-times-negative lw-emm-negative-times lw-emm-zero-times lw-emm-minus-one lw-emm-double-negative lw-emm-add-cancel lw-emm-double lw-emm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-emm-moment-with-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp index) (rationalp coefficient-error) (< 0 coefficient-error) (rationalp integral-error) (< 0 integral-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height index integral-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (+ (+ (* 5 integral-error) (* 1/2 coefficient-error)) (* (lw-euler-mellin-moment-cost rate height outer-radius anchor-error index) margin))))
 :hints (("Goal"
 :use (lw-euler-mellin-radius-data lw-euler-mellin-coefficient-gains-data lw-euler-mellin-moment-cost-data
       (:instance lw-complex-euler-mellin-coefficient-rational (error coefficient-error))
       (:instance lw-euler-mellin-polynomial-valid (target index) (error margin))
       (:instance lw-mellin-improper-polynomial-valid (sigma rate) (target index) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (error margin))
       (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-mellin-polynomial rate height outer-radius anchor-error index margin)) (target index) (offset 0))
       (:instance lw-complex-coefficient-at-rational (coefficients (lw-mellin-improper-polynomial rate height index (lw-euler-mellin-radius rate height outer-radius anchor-error) margin)) (target index) (offset 0))
       (:instance lw-mellin-integral-rational (sigma rate) (error integral-error))
       (:instance lw-mellin-integral-rational (sigma rate) (error (* 1/64 margin)))
       (:instance lw-complex-coefficient-at-nth (coefficients (lw-mellin-improper-polynomial rate height index (lw-euler-mellin-radius rate height outer-radius anchor-error) margin)) (target index) (offset 0))
       lw-emm-physical-reflected-comparison
       (:instance lw-euler-mellin-comparison-error-data (left-error margin) (right-error margin))
       (:instance lw-complex-euler-mellin-polynomial-coefficient-comparison (left-target index) (right-target index) (left-error margin) (right-error margin))
       (:instance lw-mellin-improper-polynomial-moment-comparison (sigma rate) (target index) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (error margin))
       (:instance lw-mellin-integral-cauchy (sigma rate) (left-error integral-error) (right-error (* 1/64 margin)))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (middle (lw-complex-coefficient-at (lw-euler-mellin-polynomial rate height outer-radius anchor-error index margin) index 0)) (right (lw-complex-coefficient-at (lw-mellin-improper-polynomial rate height index (lw-euler-mellin-radius rate height outer-radius anchor-error) margin) index 0))
        (radius (+ (* 1/2 coefficient-error) (* 1/2 margin (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))))) (other-radius (* (lw-euler-mellin-comparison-error margin margin) (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)))))
       (:instance lw-complex-difference-symmetric (left (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (right (lw-complex-coefficient-at (lw-mellin-improper-polynomial rate height index (lw-euler-mellin-radius rate height outer-radius anchor-error) margin) index 0)) (radius (+ (+ (* 1/2 coefficient-error) (* 1/2 margin (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))) (* (lw-euler-mellin-comparison-error margin margin) (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index))))))
       (:instance lw-complex-difference-triangle (left (lw-mellin-integral rate height index integral-error)) (middle (lw-mellin-integral rate height index (* 1/64 margin))) (right (lw-complex-coefficient-at (lw-mellin-improper-polynomial rate height index (lw-euler-mellin-radius rate height outer-radius anchor-error) margin) index 0))
        (radius (* 5 (+ integral-error (* 1/64 margin)))) (other-radius (* 1/2 margin)))
       (:instance lw-complex-difference-triangle (left (lw-mellin-integral rate height index integral-error)) (middle (lw-complex-coefficient-at (lw-mellin-improper-polynomial rate height index (lw-euler-mellin-radius rate height outer-radius anchor-error) margin) index 0)) (right (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error))
        (radius (+ (* 5 (+ integral-error (* 1/64 margin))) (* 1/2 margin))) (other-radius (+ (+ (* 1/2 coefficient-error) (* 1/2 margin (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))) (* (lw-euler-mellin-comparison-error margin margin) (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index))))))
       (:instance lw-emm-multiply-order (a (+ 37/64 (* 1/2 (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))) (* 101/64 (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index))))) (b (lw-euler-mellin-moment-cost rate height outer-radius anchor-error index)) (factor margin))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-integral rate height index integral-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)))
        (radius (+ (+ (* 5 (+ integral-error (* 1/64 margin))) (* 1/2 margin)) (+ (* 1/2 coefficient-error) (* 1/2 margin (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))) (* (lw-euler-mellin-comparison-error margin margin) (/ (lw-rational-power (lw-euler-mellin-radius rate height outer-radius anchor-error) index)))))
        (cap (+ (+ (* 5 integral-error) (* 1/2 coefficient-error)) (* (lw-euler-mellin-moment-cost rate height outer-radius anchor-error index) margin)))))
 :in-theory (union-theories
 '(lw-complex-coefficient-at-nth lw-euler-mellin-moment-cost lw-euler-mellin-comparison-error lw-emm-left-commutes lw-emm-left-distributes lw-emm-fold-constants lw-emm-times-negative lw-emm-negative-times lw-emm-zero-times lw-emm-minus-one lw-emm-double-negative lw-emm-add-cancel lw-emm-double lw-emm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-mellin-euler-moment-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp index) (rationalp coefficient-error) (< 0 coefficient-error) (rationalp integral-error) (< 0 integral-error))
 (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height index integral-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (+ (* 5 integral-error) (* 1/2 coefficient-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height index integral-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (+ (* 5 integral-error) (* 1/2 coefficient-error))))
 :use (lw-euler-mellin-radius-data lw-euler-mellin-moment-cost-data
       (:instance lw-complex-euler-mellin-coefficient-rational (error coefficient-error))
       (:instance lw-mellin-integral-rational (sigma rate) (error integral-error))
       (:instance lw-complex-operations-rational (left (lw-mellin-integral rate height index integral-error)) (right (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-mellin-integral rate height index integral-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error))) (radius (+ (* 5 integral-error) (* 1/2 coefficient-error))) (cost (lw-euler-mellin-moment-cost rate height outer-radius anchor-error index)))
       (:instance lw-emm-moment-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-mellin-integral rate height index integral-error) (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index coefficient-error)) (+ (* 5 integral-error) (* 1/2 coefficient-error)) (lw-euler-mellin-moment-cost rate height outer-radius anchor-error index)))))
 :in-theory (union-theories
 '( lw-emm-left-commutes lw-emm-left-distributes lw-emm-fold-constants lw-emm-times-negative lw-emm-negative-times lw-emm-zero-times lw-emm-minus-one lw-emm-double-negative lw-emm-add-cancel lw-emm-double lw-emm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-mellin-euler-moment-computed-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp index) (rationalp error) (< 0 error))
 (lw-complex-diskp
  (lw-complex-sub (lw-mellin-integral rate height index (* 1/10 error))
    (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index error)) error))
 :hints (("Goal"
 :use ((:instance lw-mellin-euler-moment-comparison (integral-error (* 1/10 error)) (coefficient-error error)))
 :in-theory (union-theories
 '( lw-emm-left-commutes lw-emm-left-distributes lw-emm-fold-constants lw-emm-times-negative lw-emm-negative-times lw-emm-zero-times lw-emm-minus-one lw-emm-double-negative lw-emm-add-cancel lw-emm-double lw-emm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

