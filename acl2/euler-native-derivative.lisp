(in-package "ACL2")

(include-book "euler-derivative-alignment")

; Identify the canonical physical Euler slope with the native
; ordinary-minus-logweighted series, with independent requests.

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

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-exp-mixturep lw-exp-mixture-common-value
 lw-exp-mixture-affine-polynomial lw-euler-dirichlet-nodes lw-euler-boundary-nodes
 lw-complex-polynomial lw-polynomial-add lw-polynomial-add-constant
 lw-polynomial-multiply-linear lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope)))

(local (in-theory (disable lw-euler-polynomial-argument-cap lw-euler-polynomial-factor-cap
 lw-euler-polynomial-ordinary-error lw-euler-polynomial-rounding-cost lw-euler-polynomial-precision)))

(local (in-theory (disable lw-euler-uniform-polynomial-block lw-euler-uniform-polynomial-count
 lw-euler-uniform-polynomial-request lw-euler-uniform-polynomial)))
(local (in-theory
 (disable lw-euler-refined-polynomial lw-euler-refined-polynomial-request
          lw-euler-derivative-alignment-block lw-euler-derivative-alignment-request
          lw-euler-derivative-alignment-target lw-euler-block-prefix-count
          lw-euler-derivative-value-budget lw-euler-derivative-slope-budget
          lw-euler-derivative-native-budget lw-euler-native-derivative-gain
          lw-complex-euler-local-coefficient-value
          lw-complex-zeta-pole-removed-derivative-series-value)))

(local (defthm lw-end-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-end-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-end-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-end-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-end-times-negative (a b) (b a)))
                 :in-theory (disable lw-end-times-negative)))))

(local (defthm lw-end-zero-times (equal (* 0 a) 0)))

(local (defthm lw-end-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-end-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-end-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-end-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-end-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-end-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-end-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-end-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-end-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-end-left-commutes)))))

(defun lw-euler-derivative-alignment-polynomial (rate height radius native-error margin)
 (lw-euler-refined-polynomial rate height radius (lw-euler-derivative-alignment-block rate height radius native-error margin) (lw-euler-derivative-alignment-request rate height radius native-error margin) (lw-euler-derivative-alignment-target rate height radius native-error margin) (lw-euler-derivative-value-budget radius margin)))

(local (in-theory (disable lw-euler-derivative-alignment-polynomial)))

(defthm lw-euler-derivative-alignment-polynomial-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error) (rationalp margin) (< 0 margin))
  (and (lw-complex-coefficientsp (lw-euler-derivative-alignment-polynomial rate height radius native-error margin)) (lw-complexp (lw-complex-coefficient-at (lw-euler-derivative-alignment-polynomial rate height radius native-error margin) 1 0))))
 :hints (("Goal"
  :use (lw-euler-derivative-parameter-budgets lw-euler-derivative-alignment-block-data
        lw-euler-derivative-alignment-request-data lw-euler-derivative-alignment-target-data
        (:instance lw-euler-refined-polynomial-valid (block (lw-euler-derivative-alignment-block rate height radius native-error margin)) (request (lw-euler-derivative-alignment-request rate height radius native-error margin)) (target (lw-euler-derivative-alignment-target rate height radius native-error margin)) (error (lw-euler-derivative-value-budget radius margin)))
        (:instance lw-complex-coefficient-at-rational
         (coefficients (lw-euler-refined-polynomial rate height radius (lw-euler-derivative-alignment-block rate height radius native-error margin) (lw-euler-derivative-alignment-request rate height radius native-error margin) (lw-euler-derivative-alignment-target rate height radius native-error margin) (lw-euler-derivative-value-budget radius margin))) (target 1) (offset 0)))
  :in-theory (union-theories
 '(lw-euler-derivative-alignment-polynomial lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-end-add-multiple
 (implies (and (syntaxp (quotep coefficient)) (rationalp coefficient) (rationalp value) (rationalp rest))
  (equal (+ value (* coefficient value) rest) (+ (* (+ 1 coefficient) value) rest)))
 :hints (("Goal" :use ((:instance distributivity (x value) (y 1) (z coefficient)))
                 :in-theory (union-theories
 '( lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-end-native-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error) (rationalp margin) (< 0 margin))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-coefficient-at (lw-euler-derivative-alignment-polynomial rate height radius native-error margin) 1 0) (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error))
   (+ (+ (* (+ rate (abs height) 1) (+ (* 3/2 (lw-euler-derivative-slope-budget rate height margin)) (* (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-alignment-request rate height radius native-error margin))))
            (* 3/2 (lw-euler-polynomial-ordinary-error rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2))) (* (- (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) 1) (lw-euler-derivative-alignment-request rate height radius native-error margin)) (* 3/2 (lw-euler-derivative-slope-budget rate height margin))
            (* (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (lw-euler-derivative-alignment-request rate height radius native-error margin))) (+ (* (lw-euler-native-derivative-gain rate height) (+ (* 3/8 native-error) (lw-euler-derivative-native-budget rate height margin)))
            (* 2 (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))))) (* (lw-euler-derivative-boundary-cost rate height (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))) (lw-euler-derivative-alignment-request rate height radius native-error margin))))))
 :hints (("Goal"
  :use (lw-euler-derivative-parameter-budgets lw-euler-derivative-alignment-block-data
        lw-euler-derivative-alignment-request-data lw-euler-derivative-alignment-target-data
        lw-euler-polynomial-caps-positive lw-euler-disk-envelope-data
        (:instance lw-euler-derivative-boundary-cost-valid (index (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))))
        (:instance lw-euler-polynomial-budget-valid (count (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (error (/ (lw-euler-derivative-value-budget radius margin) 2)))
        (:instance lw-complex-zero-disk)
        (:instance lw-euler-polynomial-point-caps (point (cons 0 0)))
        (:instance lw-euler-prefix-polynomial-native-derivative-comparison
         (count (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (request (lw-euler-derivative-alignment-request rate height radius native-error margin)) (argument-cap (lw-euler-polynomial-argument-cap rate height radius)) (target (lw-euler-derivative-alignment-target rate height radius native-error margin))
         (ordinary-error (lw-euler-polynomial-ordinary-error rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2))) (boundary-error (/ (lw-euler-derivative-value-budget radius margin) 8)) (derivative-error (lw-euler-derivative-slope-budget rate height margin))
         (error native-error) (target-error (lw-euler-derivative-native-budget rate height margin))))
  :in-theory (union-theories
 '(lw-end-add-multiple lw-euler-derivative-alignment-polynomial lw-euler-refined-polynomial lw-euler-native-derivative-gain lw-complex-laplace-point lw-complexp lw-complex-mul-zero lw-complex-add-zero lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-native-derivative-with-margin
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error) (rationalp margin) (< 0 margin)) (rationalp coefficient-error) (< 0 coefficient-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error) (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error)) (+ (+ coefficient-error (* 3/8 (lw-euler-native-derivative-gain rate height) native-error)) margin)))
 :hints (("Goal"
  :use (lw-euler-derivative-alignment-polynomial-data lw-end-native-comparison
        lw-euler-derivative-parameter-budgets lw-euler-derivative-alignment-block-data
        lw-euler-derivative-alignment-request-data lw-euler-derivative-alignment-target-data
        lw-euler-derivative-alignment-total-budget lw-euler-native-derivative-gain-valid
        lw-euler-disk-envelope-data
        (:instance lw-euler-derivative-boundary-cost-valid (index (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))))
        (:instance lw-euler-polynomial-budget-valid (count (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (error (/ (lw-euler-derivative-value-budget radius margin) 2)))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error coefficient-error))
        (:instance lw-complex-zeta-pole-removed-derivative-series-rational (error native-error))
        (:instance lw-complex-euler-refined-first-local-comparison
         (block (lw-euler-derivative-alignment-block rate height radius native-error margin)) (request (lw-euler-derivative-alignment-request rate height radius native-error margin)) (target (lw-euler-derivative-alignment-target rate height radius native-error margin)) (error (lw-euler-derivative-value-budget radius margin)))
        (:instance lw-complex-difference-symmetric (left (lw-complex-coefficient-at (lw-euler-derivative-alignment-polynomial rate height radius native-error margin) 1 0)) (right (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error)) (radius (+ coefficient-error (* (lw-euler-derivative-value-budget radius margin) (/ radius)))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error)) (middle (lw-complex-coefficient-at (lw-euler-derivative-alignment-polynomial rate height radius native-error margin) 1 0)) (right (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error))
         (radius (+ coefficient-error (* (lw-euler-derivative-value-budget radius margin) (/ radius)))) (other-radius (+ (+ (* (+ rate (abs height) 1) (+ (* 3/2 (lw-euler-derivative-slope-budget rate height margin)) (* (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-alignment-request rate height radius native-error margin))))
            (* 3/2 (lw-euler-polynomial-ordinary-error rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2))) (* (- (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) 1) (lw-euler-derivative-alignment-request rate height radius native-error margin)) (* 3/2 (lw-euler-derivative-slope-budget rate height margin))
            (* (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (lw-euler-derivative-alignment-request rate height radius native-error margin))) (+ (* (lw-euler-native-derivative-gain rate height) (+ (* 3/8 native-error) (lw-euler-derivative-native-budget rate height margin)))
            (* 2 (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))))) (* (lw-euler-derivative-boundary-cost rate height (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))) (lw-euler-derivative-alignment-request rate height radius native-error margin))))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error) (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error)))
         (radius (+ coefficient-error (* (lw-euler-derivative-value-budget radius margin) (/ radius)) (+ (* (+ rate (abs height) 1) (+ (* 3/2 (lw-euler-derivative-slope-budget rate height margin)) (* (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-alignment-request rate height radius native-error margin))))
            (* 3/2 (lw-euler-polynomial-ordinary-error rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2))) (* (- (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) 1) (lw-euler-derivative-alignment-request rate height radius native-error margin)) (* 3/2 (lw-euler-derivative-slope-budget rate height margin))
            (* (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (lw-euler-derivative-alignment-request rate height radius native-error margin))) (+ (* (lw-euler-native-derivative-gain rate height) (+ (* 3/8 native-error) (lw-euler-derivative-native-budget rate height margin)))
            (* 2 (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))))) (* (lw-euler-derivative-boundary-cost rate height (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))) (lw-euler-derivative-alignment-request rate height radius native-error margin)))))
         (cap (+ (+ coefficient-error (* 3/8 (lw-euler-native-derivative-gain rate height) native-error)) margin))))
  :in-theory (union-theories
 '(lw-euler-derivative-alignment-polynomial lw-euler-native-derivative-gain lw-end-add-multiple lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-native-derivative-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error)
               (rationalp coefficient-error) (< 0 coefficient-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error) (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error)) (+ coefficient-error (* 3/8 (lw-euler-native-derivative-gain rate height) native-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error) (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error)) (+ coefficient-error (* 3/8 (lw-euler-native-derivative-gain rate height) native-error))))
  :use (lw-euler-native-derivative-gain-valid
        (:instance lw-end-positive-product (a (lw-euler-native-derivative-gain rate height)) (b native-error))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error coefficient-error))
        (:instance lw-complex-zeta-pole-removed-derivative-series-rational (error native-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error)) (right (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error) (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error))) (radius (+ coefficient-error (* 3/8 (lw-euler-native-derivative-gain rate height) native-error))) (cost 1))
        (:instance lw-complex-euler-native-derivative-with-margin
         (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 coefficient-error) (lw-complex-zeta-pole-removed-derivative-series-value rate height native-error)) (+ coefficient-error (* 3/8 (lw-euler-native-derivative-gain rate height) native-error)) 1))))
  :in-theory (union-theories
 '( lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-native-derivative-request (rate height error)
 (min (/ error 2) (lw-euler-rounding-precision (lw-euler-native-derivative-gain rate height) error)))

(local (in-theory (disable lw-euler-native-derivative-request)))

(defthm lw-euler-native-derivative-request-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-native-derivative-request rate height error)) (< 0 (lw-euler-native-derivative-request rate height error)) (<= (lw-euler-native-derivative-request rate height error) (/ error 2))
       (<= (* (lw-euler-native-derivative-gain rate height) (lw-euler-native-derivative-request rate height error)) (/ error 2))))
 :hints (("Goal"
  :use (lw-euler-native-derivative-gain-valid
        (:instance lw-euler-rounding-precision-valid (cost (lw-euler-native-derivative-gain rate height)))
        (:instance lw-end-multiply-order (a (lw-euler-native-derivative-request rate height error)) (b (lw-euler-rounding-precision (lw-euler-native-derivative-gain rate height) error)) (factor (lw-euler-native-derivative-gain rate height))))
  :in-theory (union-theories
 '(lw-euler-native-derivative-request min lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-native-derivative-computed-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-euler-native-derivative-request rate height error)) (lw-complex-zeta-pole-removed-derivative-series-value rate height (lw-euler-native-derivative-request rate height error))) error))
 :hints (("Goal"
  :use (lw-euler-native-derivative-request-data
        (:instance lw-complex-euler-native-derivative-agreement (coefficient-error (lw-euler-native-derivative-request rate height error)) (native-error (lw-euler-native-derivative-request rate height error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-euler-native-derivative-request rate height error)) (lw-complex-zeta-pole-removed-derivative-series-value rate height (lw-euler-native-derivative-request rate height error))))
         (radius (+ (lw-euler-native-derivative-request rate height error) (* 3/8 (lw-euler-native-derivative-gain rate height) (lw-euler-native-derivative-request rate height error)))) (cap error)))
  :in-theory (union-theories
 '( lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



