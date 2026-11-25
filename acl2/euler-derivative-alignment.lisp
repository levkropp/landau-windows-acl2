(in-package "ACL2")

(include-book "euler-refined-coefficients")
(include-book "euler-derivative-series")
(include-book "euler-zeta-budget")

; Choose truncation first, shared precision second, and degree last.
; The budgets control both uniform values and native derivatives.

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
          lw-euler-block-prefix-count lw-dirichlet-series-count lw-dirichlet-native-refinement
          lw-euler-zeta-comparison-cutoff lw-euler-derivative-boundary-cost
          lw-euler-disk-block-cutoff lw-euler-disk-transport-cost lw-euler-rounding-precision
          lw-euler-derivative-target)))

(local (defthm lw-eda-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eda-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eda-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eda-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eda-times-negative (a b) (b a)))
                 :in-theory (disable lw-eda-times-negative)))))

(local (defthm lw-eda-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eda-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eda-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eda-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eda-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eda-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eda-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eda-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eda-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eda-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eda-left-commutes)))))

(local (defthm lw-eda-abs-data
 (implies (rationalp height) (and (rationalp (abs height)) (<= 0 (abs height))))
 :hints (("Goal" :in-theory (enable abs)))))

(defun lw-euler-native-derivative-gain (rate height)
 (+ 2 rate (abs height)))

(local (in-theory (disable lw-euler-native-derivative-gain)))

(defthm lw-euler-native-derivative-gain-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (rationalp (lw-euler-native-derivative-gain rate height)) (< 1 (lw-euler-native-derivative-gain rate height))))
 :hints (("Goal" :use (lw-eda-abs-data)
  :in-theory (union-theories
 '(lw-euler-native-derivative-gain lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defun lw-euler-derivative-value-budget (radius margin)
 (lw-euler-rounding-precision (+ 1 (/ radius)) (/ margin 4)))

(defun lw-euler-derivative-slope-budget (rate height margin)
 (lw-euler-rounding-precision (* 3/2 (lw-euler-native-derivative-gain rate height)) (/ margin 4)))

(defun lw-euler-derivative-native-budget (rate height margin)
 (lw-euler-rounding-precision (lw-euler-native-derivative-gain rate height) (/ margin 4)))

(local (in-theory (disable lw-euler-derivative-value-budget lw-euler-derivative-slope-budget lw-euler-derivative-native-budget)))

(defthm lw-euler-derivative-parameter-budgets
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (rationalp margin) (< 0 margin))
  (and (rationalp (lw-euler-derivative-value-budget radius margin)) (< 0 (lw-euler-derivative-value-budget radius margin)) (<= (lw-euler-derivative-value-budget radius margin) 1)
       (rationalp (lw-euler-derivative-slope-budget rate height margin)) (< 0 (lw-euler-derivative-slope-budget rate height margin)) (<= (lw-euler-derivative-slope-budget rate height margin) 1)
       (rationalp (lw-euler-derivative-native-budget rate height margin)) (< 0 (lw-euler-derivative-native-budget rate height margin)) (<= (lw-euler-derivative-native-budget rate height margin) 1)
       (<= (+ (lw-euler-derivative-value-budget radius margin) (* (lw-euler-derivative-value-budget radius margin) (/ radius))) (/ margin 8))
       (<= (* 3/2 (lw-euler-native-derivative-gain rate height) (lw-euler-derivative-slope-budget rate height margin)) (/ margin 8))
       (<= (* (lw-euler-native-derivative-gain rate height) (lw-euler-derivative-native-budget rate height margin)) (/ margin 8))))
 :hints (("Goal"
  :use (lw-euler-native-derivative-gain-valid
        (:instance lw-reciprocal-positive (value radius))
        (:instance lw-euler-rounding-precision-valid (cost (+ 1 (/ radius))) (error (/ margin 4)))
        (:instance lw-euler-rounding-precision-valid (cost (* 3/2 (lw-euler-native-derivative-gain rate height))) (error (/ margin 4)))
        (:instance lw-euler-rounding-precision-valid (cost (lw-euler-native-derivative-gain rate height)) (error (/ margin 4))))
  :in-theory (union-theories
 '(lw-euler-derivative-value-budget lw-euler-derivative-slope-budget lw-euler-derivative-native-budget lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eda-reciprocal-small
 (implies (and (rationalp margin) (< 0 margin) (rationalp index) (< 0 index)
               (<= (* 2 (/ margin)) index))
  (<= (* 2 (/ index)) margin))
 :hints (("Goal"
  :use ((:instance lw-eda-inverse-factor (divisor margin) (coefficient 2))
        (:instance lw-eda-multiply-order (a (* 2 (/ margin))) (b index) (factor margin))
        (:instance lw-positive-division-bound (numerator 2) (divisor index) (bound margin)))
  :in-theory (union-theories
 '( lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-derivative-alignment-block (rate height radius native-error margin)
 (max (lw-euler-disk-block-cutoff rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2))
      (lw-euler-zeta-comparison-cutoff rate height native-error native-error (/ margin 8))))

(local (in-theory (disable lw-euler-derivative-alignment-block)))

(defthm lw-euler-derivative-alignment-block-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error) (rationalp margin) (< 0 margin))
  (and (natp (lw-euler-derivative-alignment-block rate height radius native-error margin)) (<= 2 (lw-euler-derivative-alignment-block rate height radius native-error margin))
       (<= (lw-euler-disk-block-cutoff rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2)) (lw-euler-derivative-alignment-block rate height radius native-error margin))
       (posp (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (<= (lw-dirichlet-series-count native-error) (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))
       (<= (* 2 (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))))) (/ margin 8))))
 :hints (("Goal"
  :use (lw-euler-derivative-parameter-budgets
        (:instance lw-euler-disk-constructors-valid (block 2) (error (/ (lw-euler-derivative-value-budget radius margin) 2)))
        (:instance lw-euler-zeta-comparison-cutoff-brackets (euler-error native-error) (series-error native-error) (margin (/ margin 8)))
        (:instance lw-euler-block-prefix-count-data (block (lw-euler-derivative-alignment-block rate height radius native-error margin)))
        (:instance lw-eda-reciprocal-small (index (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))) (margin (/ margin 8))))
  :in-theory (union-theories
 '(lw-euler-derivative-alignment-block lw-euler-block-prefix-count max lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-derivative-alignment-cost (rate height count)
 (+ (* (+ rate (abs height) 1) count count) (- count 1) (* (+ 1 count) (+ 1 count))
    (lw-euler-derivative-boundary-cost rate height (+ 1 count))))

(local (in-theory (disable lw-euler-derivative-alignment-cost)))

(defthm lw-euler-derivative-alignment-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count))
  (and (rationalp (lw-euler-derivative-alignment-cost rate height count))
       (< 0 (lw-euler-derivative-alignment-cost rate height count))))
 :hints (("Goal"
  :use (lw-eda-abs-data (:instance lw-euler-derivative-boundary-cost-valid (index (+ 1 count))))
  :in-theory (union-theories
 '(lw-euler-derivative-alignment-cost lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defun lw-euler-derivative-alignment-request (rate height radius native-error margin)
 (min (lw-euler-refined-polynomial-request rate height radius (lw-euler-derivative-alignment-block rate height radius native-error margin) (lw-euler-derivative-value-budget radius margin))
  (min (lw-dirichlet-native-refinement rate height (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-native-budget rate height margin))
       (lw-euler-rounding-precision (lw-euler-derivative-alignment-cost rate height (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (/ margin 4)))))

(local (in-theory (disable lw-euler-derivative-alignment-request)))

(defthm lw-euler-derivative-alignment-request-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error) (rationalp margin) (< 0 margin))
  (and (rationalp (lw-euler-derivative-alignment-request rate height radius native-error margin)) (< 0 (lw-euler-derivative-alignment-request rate height radius native-error margin)) (<= (lw-euler-derivative-alignment-request rate height radius native-error margin) 1)
       (<= (lw-euler-derivative-alignment-request rate height radius native-error margin) (lw-euler-refined-polynomial-request rate height radius (lw-euler-derivative-alignment-block rate height radius native-error margin) (lw-euler-derivative-value-budget radius margin)))
       (<= (lw-euler-derivative-alignment-request rate height radius native-error margin) (lw-dirichlet-native-refinement rate height (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-native-budget rate height margin)))
       (<= (* (lw-euler-derivative-alignment-cost rate height (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (lw-euler-derivative-alignment-request rate height radius native-error margin)) (/ margin 8))))
 :hints (("Goal"
  :use (lw-euler-derivative-parameter-budgets lw-euler-derivative-alignment-block-data
        (:instance lw-euler-refined-polynomial-request-data (block (lw-euler-derivative-alignment-block rate height radius native-error margin)) (error (lw-euler-derivative-value-budget radius margin)))
        (:instance lw-dirichlet-native-refinement-valid (count (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (error (lw-euler-derivative-native-budget rate height margin)))
        (:instance lw-euler-derivative-alignment-cost-valid (count (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))))
        (:instance lw-euler-rounding-precision-valid (cost (lw-euler-derivative-alignment-cost rate height (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))) (error (/ margin 4)))
        (:instance lw-eda-multiply-order (a (lw-euler-derivative-alignment-request rate height radius native-error margin)) (b (lw-euler-rounding-precision (lw-euler-derivative-alignment-cost rate height (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (/ margin 4))) (factor (lw-euler-derivative-alignment-cost rate height (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))))))
  :in-theory (union-theories
 '(lw-euler-derivative-alignment-request min lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-derivative-alignment-target (rate height radius native-error margin)
 (lw-euler-derivative-target (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-alignment-request rate height radius native-error margin) (lw-euler-polynomial-argument-cap rate height radius) (lw-euler-derivative-slope-budget rate height margin)))

(local (in-theory (disable lw-euler-derivative-alignment-target)))

(defthm lw-euler-derivative-alignment-target-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error) (rationalp margin) (< 0 margin))
  (and (posp (lw-euler-derivative-alignment-target rate height radius native-error margin))
       (equal (lw-euler-derivative-alignment-target rate height radius native-error margin) (lw-euler-derivative-target (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-alignment-request rate height radius native-error margin) (lw-euler-polynomial-argument-cap rate height radius) (lw-euler-derivative-slope-budget rate height margin)))))
 :hints (("Goal"
  :use (lw-euler-derivative-parameter-budgets lw-euler-derivative-alignment-block-data
        lw-euler-derivative-alignment-request-data lw-euler-polynomial-caps-positive
        (:instance lw-euler-derivative-target-data
         (count (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (request (lw-euler-derivative-alignment-request rate height radius native-error margin)) (argument-cap (lw-euler-polynomial-argument-cap rate height radius)) (error (lw-euler-derivative-slope-budget rate height margin))))
  :in-theory (union-theories
 '(lw-euler-derivative-alignment-target lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eda-ordinary-budget
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate) (rationalp margin) (< 0 margin))
  (<= (* 3/2 (lw-euler-polynomial-ordinary-error rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2))) (lw-euler-derivative-value-budget radius margin)))
 :hints (("Goal"
  :use (lw-euler-derivative-parameter-budgets lw-euler-polynomial-caps-positive
        (:instance lw-eda-multiply-order
         (a 1) (b (lw-euler-polynomial-factor-cap rate height radius)) (factor (lw-euler-derivative-value-budget radius margin)))
        (:instance lw-positive-division-bound (numerator (* 3/16 (lw-euler-derivative-value-budget radius margin)))
         (divisor (lw-euler-polynomial-factor-cap rate height radius)) (bound (lw-euler-derivative-value-budget radius margin))))
  :in-theory (union-theories
 '(lw-euler-polynomial-ordinary-error lw-euler-polynomial-factor-cap lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-derivative-alignment-total-budget
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp native-error) (< 0 native-error) (rationalp margin) (< 0 margin))
  (<=
   (+ (* (lw-euler-derivative-value-budget radius margin) (/ radius))
      (* (+ rate (abs height) 1) (+ (* 3/2 (lw-euler-derivative-slope-budget rate height margin)) (* (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) (lw-euler-derivative-alignment-request rate height radius native-error margin))))
      (* 3/2 (lw-euler-polynomial-ordinary-error rate height radius (/ (lw-euler-derivative-value-budget radius margin) 2))) (* (- (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)) 1) (lw-euler-derivative-alignment-request rate height radius native-error margin)) (* 3/2 (lw-euler-derivative-slope-budget rate height margin))
      (* (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (lw-euler-derivative-alignment-request rate height radius native-error margin))
      (* (lw-euler-native-derivative-gain rate height) (lw-euler-derivative-native-budget rate height margin)) (* 2 (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))))
      (* (lw-euler-derivative-boundary-cost rate height (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))) (lw-euler-derivative-alignment-request rate height radius native-error margin)))
   margin))
 :hints (("Goal"
  :use (lw-euler-derivative-parameter-budgets lw-euler-derivative-alignment-block-data
        lw-euler-derivative-alignment-request-data lw-eda-ordinary-budget lw-eda-abs-data
        (:instance lw-euler-derivative-boundary-cost-valid (index (+ 1 (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin)))))
        (:instance lw-euler-polynomial-budget-valid (count (lw-euler-block-prefix-count (lw-euler-derivative-alignment-block rate height radius native-error margin))) (error (/ (lw-euler-derivative-value-budget radius margin) 2))))
  :in-theory (union-theories
 '(lw-euler-native-derivative-gain lw-euler-derivative-alignment-cost lw-eda-left-commutes lw-eda-left-distributes lw-eda-fold-constants lw-eda-times-negative lw-eda-negative-times lw-eda-zero-times lw-eda-minus-one lw-eda-double-negative lw-eda-add-cancel lw-eda-double lw-eda-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


