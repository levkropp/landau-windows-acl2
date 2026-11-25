(in-package "ACL2")

(include-book "euler-anchor-prefix")
(include-book "euler-refined-coefficients")

; Compute one common finite model for the coefficient and gamma names.
; Select the block first, then the common precision, then the degree.

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

(local (defthm lw-eab-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eab-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eab-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eab-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eab-times-negative (a b) (b a)))
                 :in-theory (disable lw-eab-times-negative)))))

(local (defthm lw-eab-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eab-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eab-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eab-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eab-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eab-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eab-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eab-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eab-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eab-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eab-left-commutes)))))

(defun lw-euler-anchor-coefficient-budget (radius margin)
 (lw-euler-rounding-precision (+ 1 (/ radius)) (/ margin 4)))

(defun lw-euler-anchor-slope-budget (margin)
 (lw-euler-rounding-precision 9/2 (/ margin 4)))

(local (in-theory (disable lw-euler-anchor-coefficient-budget lw-euler-anchor-slope-budget)))

(defthm lw-euler-anchor-parameter-budgets
 (implies (and (rationalp radius) (< 0 radius) (rationalp margin) (< 0 margin))
  (and (rationalp (lw-euler-anchor-coefficient-budget radius margin))
       (< 0 (lw-euler-anchor-coefficient-budget radius margin))
       (<= (lw-euler-anchor-coefficient-budget radius margin) 1)
       (rationalp (lw-euler-anchor-slope-budget margin))
       (< 0 (lw-euler-anchor-slope-budget margin))
       (<= (lw-euler-anchor-slope-budget margin) 1)
       (<= (+ (lw-euler-anchor-coefficient-budget radius margin)
              (* (lw-euler-anchor-coefficient-budget radius margin) (/ radius))) (/ margin 8))
       (<= (* 9/2 (lw-euler-anchor-slope-budget margin)) (/ margin 8))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value radius))
        (:instance lw-euler-rounding-precision-valid (cost (+ 1 (/ radius))) (error (/ margin 4)))
        (:instance lw-euler-rounding-precision-valid (cost 9/2) (error (/ margin 4))))
  :in-theory (union-theories
 '(lw-euler-anchor-coefficient-budget lw-euler-anchor-slope-budget lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eab-reciprocal-small
 (implies (and (rationalp margin) (< 0 margin) (rationalp index) (< 0 index)
               (<= (* 8 (/ margin)) index))
  (<= (/ index) (/ margin 8)))
 :hints (("Goal"
  :use ((:instance lw-eab-inverse-factor (divisor margin) (coefficient 8))
        (:instance lw-eab-multiply-order (a (* 8 (/ margin))) (b index) (factor margin))
        (:instance lw-positive-division-bound (numerator 1) (divisor index) (bound (/ margin 8))))
  :in-theory (union-theories
 '( lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-anchor-block (radius margin)
 (max
  (lw-euler-disk-block-cutoff 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2))
  (+ 2 (lw-ceiling-rational (* 8 (/ margin))))))

(local (in-theory (disable lw-euler-anchor-block)))

(defthm lw-euler-anchor-block-data
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp margin) (< 0 margin))
  (and (natp (lw-euler-anchor-block radius margin)) (<= 2 (lw-euler-anchor-block radius margin))
       (<= (lw-euler-disk-block-cutoff 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2))
           (lw-euler-anchor-block radius margin))
       (posp (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))
       (<= (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) (/ margin 8))))
 :hints (("Goal"
  :use (lw-euler-anchor-parameter-budgets
        (:instance lw-euler-disk-constructors-valid (rate 1) (height 0) (block 2)
         (error (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
        (:instance lw-ceiling-rational-bracket (value (* 8 (/ margin))))
        (:instance lw-ceiling-rational-natural (value (* 8 (/ margin))))
        (:instance lw-euler-block-prefix-count-data (block (lw-euler-anchor-block radius margin)))
        (:instance lw-eab-reciprocal-small
         (index (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))))
         (margin margin)))
  :in-theory (union-theories
 '(lw-euler-anchor-block lw-euler-block-prefix-count max lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-anchor-alignment-cost (count)
 (+ (* 2 count count) (- count 1) (* (+ 1 count) (+ 1 count))
    1 (lw-euler-anchor-derivative-cost count)))

(local (in-theory (disable lw-euler-anchor-alignment-cost)))

(defthm lw-euler-anchor-alignment-cost-valid
 (implies (posp count)
  (and (rationalp (lw-euler-anchor-alignment-cost count))
       (< 0 (lw-euler-anchor-alignment-cost count))))
 :hints (("Goal"
  :use (lw-euler-anchor-derivative-cost-valid)
  :in-theory (union-theories
 '(lw-euler-anchor-alignment-cost lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defun lw-euler-anchor-derivative-request (radius margin)
 (min
  (lw-euler-refined-polynomial-request 1 0 radius (lw-euler-anchor-block radius margin)
   (lw-euler-anchor-coefficient-budget radius margin))
  (lw-euler-rounding-precision
   (lw-euler-anchor-alignment-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))
   (/ margin 4))))

(local (in-theory (disable lw-euler-anchor-derivative-request)))

(defthm lw-euler-anchor-derivative-request-data
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp margin) (< 0 margin))
  (and (rationalp (lw-euler-anchor-derivative-request radius margin))
       (< 0 (lw-euler-anchor-derivative-request radius margin))
       (<= (lw-euler-anchor-derivative-request radius margin) 1)
       (<= (lw-euler-anchor-derivative-request radius margin)
           (lw-euler-refined-polynomial-request 1 0 radius (lw-euler-anchor-block radius margin)
            (lw-euler-anchor-coefficient-budget radius margin)))
       (<= (* (lw-euler-anchor-alignment-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))
              (lw-euler-anchor-derivative-request radius margin)) (/ margin 8))))
 :hints (("Goal"
  :use (lw-euler-anchor-parameter-budgets lw-euler-anchor-block-data
        (:instance lw-euler-anchor-alignment-cost-valid
         (count (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))))
        (:instance lw-euler-refined-polynomial-request-data
         (rate 1) (height 0) (block (lw-euler-anchor-block radius margin))
         (error (lw-euler-anchor-coefficient-budget radius margin)))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-anchor-alignment-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))))
         (error (/ margin 4)))
        (:instance lw-eab-multiply-order
         (a (lw-euler-anchor-derivative-request radius margin))
         (b (lw-euler-rounding-precision
          (lw-euler-anchor-alignment-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (/ margin 4)))
         (factor (lw-euler-anchor-alignment-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))))))
  :in-theory (union-theories
 '(lw-euler-anchor-derivative-request min lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(defun lw-euler-anchor-derivative-target (radius margin)
 (lw-euler-derivative-target (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin)
  (lw-euler-polynomial-argument-cap 1 0 radius) (lw-euler-anchor-slope-budget margin)))

(local (in-theory (disable lw-euler-anchor-derivative-target)))

(defthm lw-euler-anchor-derivative-target-data
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp margin) (< 0 margin))
  (and (posp (lw-euler-anchor-derivative-target radius margin))
       (equal (lw-euler-anchor-derivative-target radius margin)
        (lw-euler-derivative-target (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin)
         (lw-euler-polynomial-argument-cap 1 0 radius) (lw-euler-anchor-slope-budget margin)))))
 :hints (("Goal"
  :use (lw-euler-anchor-parameter-budgets lw-euler-anchor-block-data
        lw-euler-anchor-derivative-request-data
        (:instance lw-euler-polynomial-caps-positive (rate 1) (height 0))
        (:instance lw-euler-derivative-target-data
         (count (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (request (lw-euler-anchor-derivative-request radius margin))
         (argument-cap (lw-euler-polynomial-argument-cap 1 0 radius)) (error (lw-euler-anchor-slope-budget margin))))
  :in-theory (union-theories
 '(lw-euler-anchor-derivative-target lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eab-ordinary-budget
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp error) (< 0 error))
  (<= (* 3/2 (lw-euler-polynomial-ordinary-error 1 0 radius (/ error 2))) error))
 :hints (("Goal"
  :use ((:instance lw-euler-polynomial-caps-positive (rate 1) (height 0))
        (:instance lw-eab-multiply-order
         (a 1) (b (lw-euler-polynomial-factor-cap 1 0 radius)) (factor error))
        (:instance lw-positive-division-bound (numerator (* 3/16 error))
         (divisor (lw-euler-polynomial-factor-cap 1 0 radius)) (bound error)))
  :in-theory (union-theories
 '(lw-euler-polynomial-ordinary-error lw-euler-polynomial-factor-cap lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-anchor-total-budget
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp margin) (< 0 margin))
  (<=
   (+ (* (lw-euler-anchor-coefficient-budget radius margin) (/ radius))
      (* 2 (+ (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin))))
      (* 3/2 (lw-euler-polynomial-ordinary-error 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
      (* (- (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) 1) (lw-euler-anchor-derivative-request radius margin)) (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (lw-euler-anchor-derivative-request radius margin))
      (* (+ 1 (lw-euler-anchor-derivative-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) (lw-euler-anchor-derivative-request radius margin)) (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))))
   margin))
 :hints (("Goal"
  :use (lw-euler-anchor-parameter-budgets lw-euler-anchor-block-data
        lw-euler-anchor-derivative-request-data
        (:instance lw-eab-ordinary-budget (error (lw-euler-anchor-coefficient-budget radius margin)))
        (:instance lw-euler-anchor-derivative-cost-valid (count (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))))
  :in-theory (union-theories
 '(lw-euler-anchor-alignment-cost lw-eab-left-commutes lw-eab-left-distributes lw-eab-fold-constants lw-eab-times-negative lw-eab-negative-times lw-eab-zero-times lw-eab-minus-one lw-eab-double-negative lw-eab-add-cancel lw-eab-double lw-eab-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


