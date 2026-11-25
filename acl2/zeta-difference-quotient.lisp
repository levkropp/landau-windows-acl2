(in-package "ACL2")

(include-book "zeta-euler-derivative")

; Difference quotients of the actual reciprocal-normalized evaluator.
; Both endpoint requests are computed from one shared Euler request.

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

(local (in-theory (disable lw-euler-derivative-alignment-polynomial)))

(local (in-theory (disable lw-euler-native-derivative-request)))

(local (in-theory
 (disable lw-complex-l1 lw-complex-norm-square lw-complex-quotient
          lw-zeta-euler-inverse-cap lw-complex-zeta-euler-value lw-zeta-euler-point-error
          lw-euler-uniform-coefficient-cap lw-euler-local-coefficient-request)))

(local (in-theory (disable lw-zeta-derivative-anchor-size lw-zeta-derivative-left-gain
 lw-zeta-derivative-right-gain lw-zeta-derivative-request-cost)))

(local (in-theory (disable lw-zeta-derivative-request)))

(local (in-theory (disable lw-complex-zeta-euler-derivative-value)))

(local (in-theory (disable lw-zeta-euler-coarse-cap)))

(local (in-theory (disable lw-zeta-derivative-numerator-cap)))

(local (defthm lw-zdq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zdq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zdq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zdq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zdq-times-negative (a b) (b a)))
                 :in-theory (disable lw-zdq-times-negative)))))

(local (defthm lw-zdq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zdq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zdq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zdq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zdq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zdq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zdq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zdq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zdq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zdq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zdq-left-commutes)))))

(local (defthm lw-zdq-pair-equality
 (implies (equal left right)
  (and (equal (car left) (car right)) (equal (cdr left) (cdr right))))
 :rule-classes nil))

(local (defthm lw-zdq-cons-equality
 (equal (equal (cons a b) (cons c d)) (and (equal a c) (equal b d)))
 :hints (("Goal" :use ((:instance lw-zdq-pair-equality (left (cons a b)) (right (cons c d))))
                 :in-theory (union-theories
 '( lw-zdq-left-commutes lw-zdq-left-distributes lw-zdq-fold-constants lw-zdq-times-negative lw-zdq-negative-times lw-zdq-zero-times lw-zdq-minus-one lw-zdq-double-negative lw-zdq-add-cancel lw-zdq-double lw-zdq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))))

(local (defthm lw-zdq-point-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0))))
  (and (lw-complexp (cons (- rate 1) height)) (not (equal (cons (- rate 1) height) (cons 0 0)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-zdq-cons-equality lw-complexp lw-zdq-left-commutes lw-zdq-left-distributes lw-zdq-fold-constants lw-zdq-times-negative lw-zdq-negative-times lw-zdq-zero-times lw-zdq-minus-one lw-zdq-double-negative lw-zdq-add-cancel lw-zdq-double lw-zdq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-euler-reparameterized-value
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp request) (< 0 request))
  (equal (lw-complex-zeta-euler-value rate height (* (lw-zeta-euler-inverse-cap rate height) request))
         (lw-complex-quotient (lw-complex-euler-continuation-value rate height request) (cons (- rate 1) height))))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-zdq-inverse-factor (divisor (lw-zeta-euler-inverse-cap rate height)) (coefficient request))
        (:instance lw-complex-euler-continuation-value-rational (error request))
        (:instance lw-complex-mul-commutative (left (lw-complex-reciprocal (cons (- rate 1) height)))
         (right (lw-complex-euler-continuation-value rate height request))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-value lw-zeta-euler-point-error lw-complex-quotient lw-zdq-left-commutes lw-zdq-left-distributes lw-zdq-fold-constants lw-zdq-times-negative lw-zdq-negative-times lw-zdq-zero-times lw-zdq-minus-one lw-zdq-double-negative lw-zdq-add-cancel lw-zdq-double lw-zdq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-zeta-difference-quotient-gain (rate height radius)
 (* (lw-zeta-derivative-numerator-cap rate height radius) (lw-zeta-derivative-left-gain rate height) (lw-zeta-derivative-right-gain rate height)))

(defun lw-zeta-difference-quotient-modulus (rate height radius error)
 (min 1 (min (* 1/2 (lw-zeta-derivative-anchor-size rate height))
  (min (lw-euler-derivative-modulus rate height radius (* 4 (lw-zeta-derivative-request rate height error)))
       (lw-euler-rounding-precision (lw-zeta-difference-quotient-gain rate height radius) error)))))

(defun lw-zeta-difference-quotient-request (rate height offset error)
 (* 4 (lw-zeta-derivative-request rate height error) (lw-complex-l1 offset)))

(local (in-theory (disable lw-zeta-difference-quotient-gain lw-zeta-difference-quotient-modulus lw-zeta-difference-quotient-request)))

(defthm lw-zeta-difference-quotient-modulus-data
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-difference-quotient-gain rate height radius)) (< 0 (lw-zeta-difference-quotient-gain rate height radius))
       (rationalp (lw-zeta-difference-quotient-modulus rate height radius error)) (< 0 (lw-zeta-difference-quotient-modulus rate height radius error)) (<= (lw-zeta-difference-quotient-modulus rate height radius error) 1)
       (<= (lw-zeta-difference-quotient-modulus rate height radius error) (* 1/2 (lw-zeta-derivative-anchor-size rate height)))
       (<= (lw-zeta-difference-quotient-modulus rate height radius error) (lw-euler-derivative-modulus rate height radius (* 4 (lw-zeta-derivative-request rate height error))))
       (<= (lw-zeta-difference-quotient-modulus rate height radius error) (/ radius 2))
       (<= (* (lw-zeta-difference-quotient-gain rate height radius) (lw-zeta-difference-quotient-modulus rate height radius error)) (/ error 2))))
 :hints (("Goal"
  :use (lw-zeta-derivative-cost-data lw-zeta-derivative-request-data lw-zeta-derivative-numerator-cap-data
        (:instance lw-zdq-positive-product (a (lw-zeta-derivative-numerator-cap rate height radius)) (b (lw-zeta-derivative-left-gain rate height)))
        (:instance lw-zdq-positive-product (a (* (lw-zeta-derivative-numerator-cap rate height radius) (lw-zeta-derivative-left-gain rate height))) (b (lw-zeta-derivative-right-gain rate height)))
        (:instance lw-euler-derivative-modulus-valid (error (* 4 (lw-zeta-derivative-request rate height error))))
        (:instance lw-euler-rounding-precision-valid (cost (lw-zeta-difference-quotient-gain rate height radius)))
        (:instance lw-zdq-multiply-order (a (lw-zeta-difference-quotient-modulus rate height radius error)) (b (lw-euler-rounding-precision (lw-zeta-difference-quotient-gain rate height radius) error)) (factor (lw-zeta-difference-quotient-gain rate height radius))))
  :in-theory (union-theories
 '(lw-zeta-difference-quotient-gain lw-zeta-difference-quotient-modulus min lw-zdq-left-commutes lw-zdq-left-distributes lw-zdq-fold-constants lw-zdq-times-negative lw-zdq-negative-times lw-zdq-zero-times lw-zdq-minus-one lw-zdq-double-negative lw-zdq-add-cancel lw-zdq-double lw-zdq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-zeta-difference-quotient-point-data
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error)
               (lw-complexp offset) (not (equal offset (cons 0 0)))
               (<= (lw-complex-l1 offset) (lw-zeta-difference-quotient-modulus rate height radius error)))
  (and (rationalp (+ rate (car offset))) (< 0 (+ rate (car offset))) (rationalp (+ height (cdr offset)))
       (not (and (equal (+ rate (car offset)) 1) (equal (+ height (cdr offset)) 0)))
       (rationalp (lw-complex-l1 offset)) (< 0 (lw-complex-l1 offset))
       (rationalp (lw-zeta-difference-quotient-request rate height offset error)) (< 0 (lw-zeta-difference-quotient-request rate height offset error))
       (rationalp (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error))) (< 0 (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error)))
       (rationalp (* (lw-zeta-euler-inverse-cap (+ rate (car offset)) (+ height (cdr offset))) (lw-zeta-difference-quotient-request rate height offset error))) (< 0 (* (lw-zeta-euler-inverse-cap (+ rate (car offset)) (+ height (cdr offset))) (lw-zeta-difference-quotient-request rate height offset error)))))
 :hints (("Goal"
  :use (lw-zdq-point-data lw-zeta-derivative-cost-data lw-zeta-derivative-request-data
        lw-zeta-difference-quotient-modulus-data lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-l1-clearance (point offset))
        (:instance lw-complex-small-shift-clearance (anchor (cons (- rate 1) height)))
        (:instance lw-complex-disk-enlarge (point offset) (radius (lw-complex-l1 offset)) (cap radius))
        (:instance lw-euler-disk-point-data)
        (:instance lw-zeta-euler-inverse-cap-data (rate (+ rate (car offset))) (height (+ height (cdr offset))))
        (:instance lw-zdq-positive-product (a (* 4 (lw-zeta-derivative-request rate height error))) (b (lw-complex-l1 offset)))
        (:instance lw-zdq-positive-product (a (lw-zeta-euler-inverse-cap rate height)) (b (lw-zeta-difference-quotient-request rate height offset error)))
        (:instance lw-zdq-positive-product (a (lw-zeta-euler-inverse-cap (+ rate (car offset)) (+ height (cdr offset)))) (b (lw-zeta-difference-quotient-request rate height offset error))))
  :in-theory (union-theories
 '(lw-zeta-difference-quotient-request lw-zeta-derivative-anchor-size lw-complex-add lw-complexp lw-zdq-cons-equality lw-zdq-left-commutes lw-zdq-left-distributes lw-zdq-fold-constants lw-zdq-times-negative lw-zdq-negative-times lw-zdq-zero-times lw-zdq-minus-one lw-zdq-double-negative lw-zdq-add-cancel lw-zdq-double lw-zdq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-zeta-difference-quotient-total-budget
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error)
               (lw-complexp offset) (not (equal offset (cons 0 0)))
               (<= (lw-complex-l1 offset) (lw-zeta-difference-quotient-modulus rate height radius error))) (<= (+ (* (lw-zeta-derivative-left-gain rate height) (+ (* 8 (lw-zeta-derivative-request rate height error)) (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error)) (lw-zeta-derivative-request rate height error))) (* (lw-zeta-difference-quotient-gain rate height radius) (lw-complex-l1 offset))) error))
 :hints (("Goal"
  :use (lw-zeta-difference-quotient-point-data lw-zeta-difference-quotient-modulus-data
        lw-zeta-derivative-request-data lw-zeta-derivative-cost-data lw-zeta-euler-inverse-cap-data
        (:instance lw-zdq-multiply-order (a (lw-complex-l1 offset)) (b 1) (factor (* 4 (lw-zeta-derivative-request rate height error))))
        (:instance lw-zdq-multiply-order (a (lw-zeta-difference-quotient-request rate height offset error)) (b (* 4 (lw-zeta-derivative-request rate height error))) (factor (lw-zeta-euler-inverse-cap rate height)))
        (:instance lw-zdq-multiply-order
         (a (+ (* 8 (lw-zeta-derivative-request rate height error)) (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error)) (lw-zeta-derivative-request rate height error))) (b (* (+ 9 (* 4 (lw-zeta-euler-inverse-cap rate height))) (lw-zeta-derivative-request rate height error))) (factor (lw-zeta-derivative-left-gain rate height)))
        (:instance lw-zdq-multiply-order (a (lw-complex-l1 offset)) (b (lw-zeta-difference-quotient-modulus rate height radius error)) (factor (lw-zeta-difference-quotient-gain rate height radius))))
  :in-theory (union-theories
 '(lw-zeta-difference-quotient-request lw-zdq-left-commutes lw-zdq-left-distributes lw-zdq-fold-constants lw-zdq-times-negative lw-zdq-negative-times lw-zdq-zero-times lw-zdq-minus-one lw-zdq-double-negative lw-zdq-add-cancel lw-zdq-double lw-zdq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-zeta-euler-computed-difference-quotient
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error)
               (lw-complexp offset) (not (equal offset (cons 0 0)))
               (<= (lw-complex-l1 offset) (lw-zeta-difference-quotient-modulus rate height radius error))) (lw-complex-diskp (lw-complex-sub (lw-complex-quotient (lw-complex-sub (lw-complex-zeta-euler-value (+ rate (car offset)) (+ height (cdr offset)) (* (lw-zeta-euler-inverse-cap (+ rate (car offset)) (+ height (cdr offset))) (lw-zeta-difference-quotient-request rate height offset error))) (lw-complex-zeta-euler-value rate height (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error)))) offset) (lw-complex-zeta-euler-derivative-value rate height radius error)) error))
 :hints (("Goal"
  :use (lw-zdq-point-data lw-zeta-difference-quotient-point-data
        lw-zeta-difference-quotient-modulus-data lw-zeta-difference-quotient-total-budget
        lw-zeta-derivative-cost-data lw-zeta-derivative-request-data lw-zeta-derivative-numerator-cap-data
        lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-euler-continuation-value-rational (error (lw-zeta-difference-quotient-request rate height offset error)))
        (:instance lw-complex-euler-continuation-value-rational (rate (+ rate (car offset))) (height (+ height (cdr offset))) (error (lw-zeta-difference-quotient-request rate height offset error)))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-zeta-euler-value-rational (error (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error))))
        (:instance lw-complex-zeta-euler-value-rational (rate (+ rate (car offset))) (height (+ height (cdr offset))) (error (* (lw-zeta-euler-inverse-cap (+ rate (car offset)) (+ height (cdr offset))) (lw-zeta-difference-quotient-request rate height offset error))))
        (:instance lw-complex-euler-computed-difference-quotient (error (* 8 (lw-zeta-derivative-request rate height error))))
        (:instance lw-complex-zeta-euler-value-cauchy (left-error (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error))) (right-error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-zeta-euler-reparameterized-value (request (lw-zeta-difference-quotient-request rate height offset error)))
        (:instance lw-complex-zeta-euler-reparameterized-value (rate (+ rate (car offset))) (height (+ height (cdr offset))) (request (lw-zeta-difference-quotient-request rate height offset error)))
        (:instance lw-complex-quotient-increment-bound (value (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) (lw-zeta-difference-quotient-request rate height offset error))) (anchor (lw-complex-euler-continuation-value rate height (lw-zeta-difference-quotient-request rate height offset error))) (denominator (cons (- rate 1) height))
         (slope (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error))) (approximate-anchor (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error))) (derivative-error (* 8 (lw-zeta-derivative-request rate height error)))
         (anchor-error (+ (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error)) (lw-zeta-derivative-request rate height error))) (numerator-cap (lw-zeta-derivative-numerator-cap rate height radius)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-quotient (lw-complex-sub (lw-complex-zeta-euler-value (+ rate (car offset)) (+ height (cdr offset)) (* (lw-zeta-euler-inverse-cap (+ rate (car offset)) (+ height (cdr offset))) (lw-zeta-difference-quotient-request rate height offset error))) (lw-complex-zeta-euler-value rate height (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error)))) offset) (lw-complex-zeta-euler-derivative-value rate height radius error))) (radius (+ (* (lw-zeta-derivative-left-gain rate height) (+ (* 8 (lw-zeta-derivative-request rate height error)) (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-difference-quotient-request rate height offset error)) (lw-zeta-derivative-request rate height error))) (* (lw-zeta-difference-quotient-gain rate height radius) (lw-complex-l1 offset)))) (cap error)))
  :in-theory (union-theories
 '(lw-zeta-difference-quotient-request lw-zeta-difference-quotient-gain lw-zeta-derivative-anchor-size lw-zeta-derivative-left-gain lw-zeta-derivative-right-gain lw-complex-zeta-euler-derivative-value lw-complex-quotient lw-complex-mul-commutative lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-add lw-complexp lw-zdq-left-commutes lw-zdq-left-distributes lw-zdq-fold-constants lw-zdq-times-negative lw-zdq-negative-times lw-zdq-zero-times lw-zdq-minus-one lw-zdq-double-negative lw-zdq-add-cancel lw-zdq-double lw-zdq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


