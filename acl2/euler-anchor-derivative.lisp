(in-package "ACL2")

(include-book "euler-anchor-budget")

; The first physical local coefficient at one is the Euler constant.
; This identifies two already computed rational Cauchy names.

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

(local (defthm lw-ead-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ead-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ead-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ead-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ead-times-negative (a b) (b a)))
                 :in-theory (disable lw-ead-times-negative)))))

(local (defthm lw-ead-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ead-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ead-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ead-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ead-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ead-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ead-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ead-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ead-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ead-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ead-left-commutes)))))

(defun lw-euler-anchor-derivative-polynomial (radius margin)
 (lw-euler-refined-polynomial 1 0 radius (lw-euler-anchor-block radius margin) (lw-euler-anchor-derivative-request radius margin) (lw-euler-anchor-derivative-target radius margin) (lw-euler-anchor-coefficient-budget radius margin)))

(local (in-theory (disable lw-euler-anchor-derivative-polynomial)))

(defthm lw-euler-anchor-derivative-polynomial-data
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp margin) (< 0 margin))
  (and (lw-complex-coefficientsp (lw-euler-anchor-derivative-polynomial radius margin)) (lw-complexp (lw-complex-coefficient-at (lw-euler-anchor-derivative-polynomial radius margin) 1 0))))
 :hints (("Goal"
  :use (lw-euler-anchor-parameter-budgets lw-euler-anchor-block-data
        lw-euler-anchor-derivative-request-data lw-euler-anchor-derivative-target-data
        (:instance lw-euler-refined-polynomial-valid
         (rate 1) (height 0) (block (lw-euler-anchor-block radius margin)) (request (lw-euler-anchor-derivative-request radius margin)) (target (lw-euler-anchor-derivative-target radius margin)) (error (lw-euler-anchor-coefficient-budget radius margin)))
        (:instance lw-complex-coefficient-at-rational
         (coefficients (lw-euler-refined-polynomial 1 0 radius (lw-euler-anchor-block radius margin) (lw-euler-anchor-derivative-request radius margin) (lw-euler-anchor-derivative-target radius margin) (lw-euler-anchor-coefficient-budget radius margin)))
         (target 1) (offset 0)))
  :in-theory (union-theories
 '(lw-euler-anchor-derivative-polynomial lw-ead-left-commutes lw-ead-left-distributes lw-ead-fold-constants lw-ead-times-negative lw-ead-negative-times lw-ead-zero-times lw-ead-minus-one lw-ead-double-negative lw-ead-add-cancel lw-ead-double lw-ead-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ead-point-cap
 (implies (and (rationalp radius) (< 0 radius) (< radius 1))
  (lw-complex-diskp (lw-complex-laplace-point 1 0) (lw-euler-polynomial-argument-cap 1 0 radius)))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complex-laplace-point lw-complex-diskp lw-complexp lw-diskp lw-euler-polynomial-argument-cap abs lw-ead-left-commutes lw-ead-left-distributes lw-ead-fold-constants lw-ead-times-negative lw-ead-negative-times lw-ead-zero-times lw-ead-minus-one lw-ead-double-negative lw-ead-add-cancel lw-ead-double lw-ead-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))))

(local (defthm lw-ead-prefix-comparison
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-coefficient-at (lw-euler-anchor-derivative-polynomial radius margin) 1 0) (lw-complex-euler-prefix-derivative 1 0 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin))) (+ (* 2 (+ (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin))))
      (* 3/2 (lw-euler-polynomial-ordinary-error 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
      (* (- (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) 1) (lw-euler-anchor-derivative-request radius margin)) (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (lw-euler-anchor-derivative-request radius margin)))))
 :hints (("Goal"
  :use (lw-euler-anchor-parameter-budgets lw-euler-anchor-block-data
        lw-euler-anchor-derivative-request-data lw-euler-anchor-derivative-target-data
        lw-ead-point-cap
        (:instance lw-euler-polynomial-budget-valid
         (rate 1) (height 0) (count (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (error (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
        (:instance lw-euler-prefix-polynomial-first-common-comparison
         (rate 1) (height 0) (count (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (request (lw-euler-anchor-derivative-request radius margin))
         (argument-cap (lw-euler-polynomial-argument-cap 1 0 radius)) (target (lw-euler-anchor-derivative-target radius margin))
         (ordinary-error (lw-euler-polynomial-ordinary-error 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
         (boundary-error (/ (lw-euler-anchor-coefficient-budget radius margin) 8)) (error (lw-euler-anchor-slope-budget margin))))
  :in-theory (union-theories
 '(lw-euler-anchor-derivative-polynomial lw-euler-refined-polynomial (:executable-counterpart abs) lw-ead-left-commutes lw-ead-left-distributes lw-ead-fold-constants lw-ead-times-negative lw-ead-negative-times lw-ead-zero-times lw-ead-minus-one lw-ead-double-negative lw-ead-add-cancel lw-ead-double lw-ead-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))


(defthm lw-complex-euler-anchor-derivative-with-margin
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp gamma-error) (< 0 gamma-error)
               (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error) (cons (car (lw-euler-bounds gamma-error)) 0))
   (+ coefficient-error gamma-error margin)))
 :hints (("Goal"
  :use (lw-euler-anchor-parameter-budgets lw-euler-anchor-block-data
        lw-euler-anchor-derivative-request-data lw-euler-anchor-derivative-target-data
        lw-euler-anchor-derivative-polynomial-data lw-euler-anchor-total-budget
        lw-ead-prefix-comparison
        (:instance lw-euler-anchor-prefix-derivative-rational (count (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (request (lw-euler-anchor-derivative-request radius margin)))
        (:instance lw-euler-anchor-prefix-gamma (count (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (request (lw-euler-anchor-derivative-request radius margin)))
        (:instance lw-euler-bounds-interval (epsilon gamma-error))
        (:instance lw-complex-euler-local-coefficient-rational
         (rate 1) (height 0) (index 1) (error coefficient-error))
        (:instance lw-complex-euler-refined-first-local-comparison
         (rate 1) (height 0) (block (lw-euler-anchor-block radius margin)) (request (lw-euler-anchor-derivative-request radius margin)) (target (lw-euler-anchor-derivative-target radius margin)) (error (lw-euler-anchor-coefficient-budget radius margin)))
        (:instance lw-complex-difference-symmetric (left (lw-complex-coefficient-at (lw-euler-anchor-derivative-polynomial radius margin) 1 0)) (right (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error)) (radius (+ coefficient-error (* (lw-euler-anchor-coefficient-budget radius margin) (/ radius)))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-coefficient-at (lw-euler-anchor-derivative-polynomial radius margin) 1 0)) (middle (lw-complex-euler-prefix-derivative 1 0 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin))) (right (cons (car (lw-euler-bounds gamma-error)) 0))
         (radius (+ (* 2 (+ (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin))))
      (* 3/2 (lw-euler-polynomial-ordinary-error 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
      (* (- (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) 1) (lw-euler-anchor-derivative-request radius margin)) (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (lw-euler-anchor-derivative-request radius margin)))) (other-radius (+ (* (+ 1 (lw-euler-anchor-derivative-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) (lw-euler-anchor-derivative-request radius margin)) (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) gamma-error)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error)) (middle (lw-complex-coefficient-at (lw-euler-anchor-derivative-polynomial radius margin) 1 0)) (right (cons (car (lw-euler-bounds gamma-error)) 0))
         (radius (+ coefficient-error (* (lw-euler-anchor-coefficient-budget radius margin) (/ radius)))) (other-radius (+ (+ (* 2 (+ (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin))))
      (* 3/2 (lw-euler-polynomial-ordinary-error 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
      (* (- (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) 1) (lw-euler-anchor-derivative-request radius margin)) (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (lw-euler-anchor-derivative-request radius margin))) (+ (* (+ 1 (lw-euler-anchor-derivative-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) (lw-euler-anchor-derivative-request radius margin)) (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) gamma-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error) (cons (car (lw-euler-bounds gamma-error)) 0)))
         (radius (+ (+ coefficient-error (* (lw-euler-anchor-coefficient-budget radius margin) (/ radius))) (+ (* 2 (+ (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) (lw-euler-anchor-derivative-request radius margin))))
      (* 3/2 (lw-euler-polynomial-ordinary-error 1 0 radius (/ (lw-euler-anchor-coefficient-budget radius margin) 2)))
      (* (- (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)) 1) (lw-euler-anchor-derivative-request radius margin)) (* 3/2 (lw-euler-anchor-slope-budget margin)) (* (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin))) (lw-euler-anchor-derivative-request radius margin))) (+ (* (+ 1 (lw-euler-anchor-derivative-cost (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) (lw-euler-anchor-derivative-request radius margin)) (/ (+ 1 (lw-euler-block-prefix-count (lw-euler-anchor-block radius margin)))) gamma-error)))
         (cap (+ coefficient-error gamma-error margin))))
  :in-theory (union-theories
 '(lw-euler-anchor-derivative-polynomial lw-complexp lw-intervalp lw-ead-left-commutes lw-ead-left-distributes lw-ead-fold-constants lw-ead-times-negative lw-ead-negative-times lw-ead-zero-times lw-ead-minus-one lw-ead-double-negative lw-ead-add-cancel lw-ead-double lw-ead-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-anchor-derivative
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp gamma-error) (< 0 gamma-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error) (cons (car (lw-euler-bounds gamma-error)) 0))
   (+ coefficient-error gamma-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error) (cons (car (lw-euler-bounds gamma-error)) 0)) (+ coefficient-error gamma-error)))
  :use ((:instance lw-complex-euler-local-coefficient-rational
         (rate 1) (height 0) (index 1) (error coefficient-error))
        (:instance lw-euler-bounds-interval (epsilon gamma-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error)) (right (cons (car (lw-euler-bounds gamma-error)) 0)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error) (cons (car (lw-euler-bounds gamma-error)) 0))) (radius (+ coefficient-error gamma-error)) (cost 1))
        (:instance lw-complex-euler-anchor-derivative-with-margin
         (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-coefficient-value 1 0 radius 1 coefficient-error) (cons (car (lw-euler-bounds gamma-error)) 0)) (+ coefficient-error gamma-error) 1))))
  :in-theory (union-theories
 '(lw-complexp lw-intervalp lw-ead-left-commutes lw-ead-left-distributes lw-ead-fold-constants lw-ead-times-negative lw-ead-negative-times lw-ead-zero-times lw-ead-minus-one lw-ead-double-negative lw-ead-add-cancel lw-ead-double lw-ead-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-anchor-derivative-computed
 (implies (and (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-local-coefficient-value 1 0 radius 1 (/ error 2))
    (cons (car (lw-euler-bounds (/ error 2))) 0))
   error))
 :hints (("Goal"
  :use ((:instance lw-complex-euler-anchor-derivative (coefficient-error (/ error 2)) (gamma-error (/ error 2))))
  :in-theory (union-theories
 '( lw-ead-left-commutes lw-ead-left-distributes lw-ead-fold-constants lw-ead-times-negative lw-ead-negative-times lw-ead-zero-times lw-ead-minus-one lw-ead-double-negative lw-ead-add-cancel lw-ead-double lw-ead-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


