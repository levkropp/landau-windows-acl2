(in-package "ACL2")

(include-book "zeta-euler-clearance")

; Evaluate the actual negative logarithmic derivative with a
; checked nonzero denominator and a computed Cauchy precision.

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

(local (in-theory (disable lw-zeta-native-derivative-gain)))

(local (in-theory (disable lw-zeta-native-derivative-request)))

(local (in-theory (disable lw-complex-zeta-series-value lw-complex-norm-square)))

(local (in-theory (disable lw-zeta-euler-clearance-cost)))

(local (defthm lw-zeld-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zeld-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zeld-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zeld-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zeld-times-negative (a b) (b a)))
                 :in-theory (disable lw-zeld-times-negative)))))

(local (defthm lw-zeld-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zeld-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zeld-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zeld-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zeld-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zeld-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zeld-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zeld-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zeld-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zeld-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zeld-left-commutes)))))

(defun lw-zeta-euler-log-derivative-cap (rate height radius)
 (* (lw-zeta-euler-inverse-cap rate height) (lw-zeta-derivative-numerator-cap rate height radius)))

(local (in-theory (disable lw-zeta-euler-log-derivative-cap)))

(defthm lw-zeta-euler-log-derivative-cap-data
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-euler-log-derivative-cap rate height radius)) (<= 2 (lw-zeta-euler-log-derivative-cap rate height radius)) (lw-complex-diskp (lw-complex-zeta-euler-derivative-value rate height radius error) (lw-zeta-euler-log-derivative-cap rate height radius))))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data lw-zeta-derivative-numerator-cap-data
        lw-euler-uniform-coefficient-cap-valid
        (:instance lw-complex-zeta-euler-coarse-bound (request 1))
        (:instance lw-reciprocal-positive (value radius))
        (:instance lw-zeld-positive-product (a (lw-euler-uniform-coefficient-cap rate height radius)) (b (/ radius)))
        (:instance lw-zeld-multiply-order (a 1) (b (lw-zeta-euler-inverse-cap rate height)) (factor (lw-zeta-derivative-numerator-cap rate height radius)))
        (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error)) (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error)))) (radius (lw-zeta-euler-inverse-cap rate height)) (other-radius (lw-zeta-derivative-numerator-cap rate height radius))))
  :in-theory (union-theories
 '(lw-zeta-euler-log-derivative-cap lw-zeta-derivative-numerator-cap lw-complex-zeta-euler-derivative-value lw-zeld-left-commutes lw-zeld-left-distributes lw-zeld-fold-constants lw-zeld-times-negative lw-zeld-negative-times lw-zeld-zero-times lw-zeld-minus-one lw-zeld-double-negative lw-zeld-add-cancel lw-zeld-double lw-zeld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-zeta-euler-log-derivative-cost (rate height radius)
 (+ 4 (* 16 (lw-zeta-euler-log-derivative-cap rate height radius))))

(local (in-theory (disable lw-zeta-euler-log-derivative-cost)))

(defthm lw-zeta-euler-log-derivative-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate))
  (and (rationalp (lw-zeta-euler-log-derivative-cost rate height radius)) (<= 36 (lw-zeta-euler-log-derivative-cost rate height radius))))
 :hints (("Goal"
  :use ((:instance lw-zeta-euler-log-derivative-cap-data (error 1)))
  :in-theory (union-theories
 '(lw-zeta-euler-log-derivative-cost lw-zeld-left-commutes lw-zeld-left-distributes lw-zeld-fold-constants lw-zeld-times-negative lw-zeld-negative-times lw-zeld-zero-times lw-zeld-minus-one lw-zeld-double-negative lw-zeld-add-cancel lw-zeld-double lw-zeld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-zeta-euler-log-derivative-request (rate height radius error)
 (lw-euler-rounding-precision (lw-zeta-euler-log-derivative-cost rate height radius) (* 2 error)))

(local (in-theory (disable lw-zeta-euler-log-derivative-request)))

(defthm lw-zeta-euler-log-derivative-request-data
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-euler-log-derivative-request rate height radius error)) (< 0 (lw-zeta-euler-log-derivative-request rate height radius error)) (<= (lw-zeta-euler-log-derivative-request rate height radius error) 1)
       (<= (* (lw-zeta-euler-log-derivative-cost rate height radius) (lw-zeta-euler-log-derivative-request rate height radius error)) error) (<= (* 16 (lw-zeta-euler-log-derivative-request rate height radius error)) error)))
 :hints (("Goal"
  :use (lw-zeta-euler-log-derivative-cost-valid
        (:instance lw-euler-rounding-precision-valid (cost (lw-zeta-euler-log-derivative-cost rate height radius)) (error (* 2 error)))
        (:instance lw-zeld-multiply-order (a 16) (b (lw-zeta-euler-log-derivative-cost rate height radius)) (factor (lw-zeta-euler-log-derivative-request rate height radius error))))
  :in-theory (union-theories
 '(lw-zeta-euler-log-derivative-request lw-zeld-left-commutes lw-zeld-left-distributes lw-zeld-fold-constants lw-zeld-times-negative lw-zeld-negative-times lw-zeld-zero-times lw-zeld-minus-one lw-zeld-double-negative lw-zeld-add-cancel lw-zeld-double lw-zeld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-zeta-euler-log-derivative-value (rate height radius error)
 (lw-complex-quotient (lw-complex-scale -1 (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius error))) (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error))))

(local (in-theory (disable lw-complex-zeta-euler-log-derivative-value)))

(defthm lw-complex-zeta-euler-log-derivative-rational
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-euler-log-derivative-value rate height radius error)))
 :hints (("Goal"
  :use (lw-zeta-euler-log-derivative-request-data
        (:instance lw-complex-zeta-euler-derivative-rational (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-euler-clearance (error (lw-zeta-euler-log-derivative-request rate height radius error))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-log-derivative-value lw-complex-scale-rational lw-complex-quotient-rational lw-zeld-left-commutes lw-zeld-left-distributes lw-zeld-fold-constants lw-zeld-times-negative lw-zeld-negative-times lw-zeld-zero-times lw-zeld-minus-one lw-zeld-double-negative lw-zeld-add-cancel lw-zeld-double lw-zeld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-zeld-negated-difference
 (implies (and (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-scale -1 left) (lw-complex-scale -1 right))
         (lw-complex-scale -1 (lw-complex-sub left right))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-zeld-left-commutes lw-zeld-left-distributes lw-zeld-fold-constants lw-zeld-times-negative lw-zeld-negative-times lw-zeld-zero-times lw-zeld-minus-one lw-zeld-double-negative lw-zeld-add-cancel lw-zeld-double lw-zeld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-zeta-euler-log-derivative-cauchy
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius left-error) (lw-complex-zeta-euler-log-derivative-value rate height radius right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-zeta-euler-log-derivative-request-data (error left-error))
        (:instance lw-zeta-euler-log-derivative-request-data (error right-error))
        (:instance lw-zeta-euler-log-derivative-cap-data (error (lw-zeta-euler-log-derivative-request rate height radius right-error)))
        (:instance lw-complex-zeta-euler-derivative-rational (error (lw-zeta-euler-log-derivative-request rate height radius left-error)))
        (:instance lw-complex-zeta-euler-derivative-rational (error (lw-zeta-euler-log-derivative-request rate height radius right-error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-euler-log-derivative-request rate height radius left-error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-euler-log-derivative-request rate height radius right-error)))
        (:instance lw-complex-zeta-euler-clearance (error (lw-zeta-euler-log-derivative-request rate height radius left-error)))
        (:instance lw-complex-zeta-euler-clearance (error (lw-zeta-euler-log-derivative-request rate height radius right-error)))
        (:instance lw-complex-zeta-euler-derivative-cauchy (left-error (lw-zeta-euler-log-derivative-request rate height radius left-error)) (right-error (lw-zeta-euler-log-derivative-request rate height radius right-error)))
        (:instance lw-complex-zeta-euler-value-cauchy (left-error (lw-zeta-euler-log-derivative-request rate height radius left-error)) (right-error (lw-zeta-euler-log-derivative-request rate height radius right-error)))
        (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius left-error)) (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius right-error)))) (factor -1) (radius (+ (lw-zeta-euler-log-derivative-request rate height radius left-error) (lw-zeta-euler-log-derivative-request rate height radius right-error))))
        (:instance lw-complex-scale-disk (point (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius right-error))) (factor -1) (radius (lw-zeta-euler-log-derivative-cap rate height radius)))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-scale -1 (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius left-error)))) (denominator (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius left-error)))
         (approximate-numerator (lw-complex-scale -1 (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius right-error)))) (approximate-denominator (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius right-error)))
         (left-clearance 1/4) (right-clearance 1/4) (numerator-cap (lw-zeta-euler-log-derivative-cap rate height radius))
         (numerator-error (+ (lw-zeta-euler-log-derivative-request rate height radius left-error) (lw-zeta-euler-log-derivative-request rate height radius right-error))) (denominator-error (+ (lw-zeta-euler-log-derivative-request rate height radius left-error) (lw-zeta-euler-log-derivative-request rate height radius right-error))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius left-error) (lw-complex-zeta-euler-log-derivative-value rate height radius right-error)))
         (radius (* (lw-zeta-euler-log-derivative-cost rate height radius) (+ (lw-zeta-euler-log-derivative-request rate height radius left-error) (lw-zeta-euler-log-derivative-request rate height radius right-error)))) (cap (+ left-error right-error))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-log-derivative-value lw-zeta-euler-log-derivative-cost lw-zeld-negated-difference lw-complex-scale-rational abs lw-zeld-left-commutes lw-zeld-left-distributes lw-zeld-fold-constants lw-zeld-times-negative lw-zeld-negative-times lw-zeld-zero-times lw-zeld-minus-one lw-zeld-double-negative lw-zeld-add-cancel lw-zeld-double lw-zeld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


