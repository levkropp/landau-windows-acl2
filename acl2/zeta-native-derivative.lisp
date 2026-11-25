(in-package "ACL2")

(include-book "zeta-difference-quotient")

; The derivative of the normalized evaluator is the negative
; log-weighted native zeta series on their common half-plane.

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

(local (defthm lw-znd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-znd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-znd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-znd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-znd-times-negative (a b) (b a)))
                 :in-theory (disable lw-znd-times-negative)))))

(local (defthm lw-znd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-znd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-znd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-znd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-znd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-znd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-znd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-znd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-znd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-znd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-znd-left-commutes)))))

(local (defthm lw-znd-pair-equality
 (implies (equal left right)
  (and (equal (car left) (car right)) (equal (cdr left) (cdr right))))
 :rule-classes nil))

(local (defthm lw-znd-cons-equality
 (equal (equal (cons a b) (cons c d)) (and (equal a c) (equal b d)))
 :hints (("Goal" :use ((:instance lw-znd-pair-equality (left (cons a b)) (right (cons c d))))
                 :in-theory (union-theories
 '( lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))))

(local (defthm lw-znd-point-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0))))
  (and (lw-complexp (cons (- rate 1) height)) (not (equal (cons (- rate 1) height) (cons 0 0)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-znd-cons-equality lw-complexp lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-znd-derivative-residual
 (implies (and (lw-complexp factor) (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
  (equal
   (lw-complex-sub (lw-complex-mul factor (lw-complex-sub a b))
                   (lw-complex-mul factor (lw-complex-sub c d)))
   (lw-complex-mul factor (lw-complex-sub (lw-complex-sub a c) (lw-complex-sub b d)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-mul lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-zeta-native-derivative-gain (rate height)
 (* (lw-zeta-euler-inverse-cap rate height) (+ (lw-euler-native-derivative-gain rate height) (* (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1)))))

(local (in-theory (disable lw-zeta-native-derivative-gain)))

(defthm lw-zeta-native-derivative-gain-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (rationalp (lw-zeta-native-derivative-gain rate height)) (< 0 (lw-zeta-native-derivative-gain rate height))))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data lw-euler-native-derivative-gain-valid
        (:instance lw-euler-disk-envelope-data (radius 0))
        (:instance lw-znd-positive-product (a (lw-zeta-euler-inverse-cap rate height)) (b (+ rate (abs height) 1)))
        (:instance lw-znd-positive-product (a (lw-zeta-euler-inverse-cap rate height)) (b (+ (lw-euler-native-derivative-gain rate height) (* (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1))))))
  :in-theory (union-theories
 '(lw-zeta-native-derivative-gain lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-znd-native-normalization
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp series-error) (< 0 series-error))
  (equal (lw-complex-mul (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-sub (lw-complex-zeta-pole-removed-derivative-series-value rate height series-error) (lw-complex-zeta-series-value nil rate height series-error))) (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height series-error))))
 :hints (("Goal"
  :use (lw-znd-point-data lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error series-error))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error series-error))
        (:instance lw-complex-reciprocal-cancel-product (a (cons (- rate 1) height)) (b (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height series-error)))))
  :in-theory (union-theories
 '(lw-complex-zeta-pole-removed-derivative-series-value lw-complex-sub-add-cancel lw-complex-scale-rational lw-complex-ring-rational lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-native-derivative-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error) (rationalp series-error) (< 0 series-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius error) (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height series-error))) (+ error (* 3/8 (lw-zeta-native-derivative-gain rate height) series-error))))
 :hints (("Goal"
  :use (lw-zeta-derivative-request-data lw-zeta-euler-inverse-cap-data
        lw-zeta-native-derivative-gain-valid lw-euler-native-derivative-gain-valid
        lw-euler-disk-envelope-data lw-znd-native-normalization
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error series-error))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error series-error))
        (:instance lw-complex-zeta-pole-removed-derivative-series-rational (error series-error))
        (:instance lw-complex-euler-native-derivative-agreement (coefficient-error (lw-zeta-derivative-request rate height error)) (native-error series-error))
        (:instance lw-complex-zeta-euler-series-agreement (euler-error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-sub-disk (left (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error)) (lw-complex-zeta-pole-removed-derivative-series-value rate height series-error))) (right (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error)) (lw-complex-zeta-series-value nil rate height series-error)))
         (radius (+ (lw-zeta-derivative-request rate height error) (* 3/8 (lw-euler-native-derivative-gain rate height) series-error))) (other-radius (+ (* 1/4 (lw-zeta-derivative-request rate height error)) (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) series-error))))
        (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-sub (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error)) (lw-complex-zeta-pole-removed-derivative-series-value rate height series-error)) (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error)) (lw-complex-zeta-series-value nil rate height series-error)))) (radius (lw-zeta-euler-inverse-cap rate height)) (other-radius (+ (+ (lw-zeta-derivative-request rate height error) (* 3/8 (lw-euler-native-derivative-gain rate height) series-error)) (+ (* 1/4 (lw-zeta-derivative-request rate height error)) (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) series-error)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius error) (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height series-error))))
         (radius (* (lw-zeta-euler-inverse-cap rate height) (+ (+ (lw-zeta-derivative-request rate height error) (* 3/8 (lw-euler-native-derivative-gain rate height) series-error)) (+ (* 1/4 (lw-zeta-derivative-request rate height error)) (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) series-error))))) (cap (+ error (* 3/8 (lw-zeta-native-derivative-gain rate height) series-error)))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-derivative-value lw-zeta-native-derivative-gain lw-znd-derivative-residual lw-complex-scale-rational lw-complex-ring-rational lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-zeta-native-derivative-request (rate height error)
 (min (/ error 2) (lw-euler-rounding-precision (lw-zeta-native-derivative-gain rate height) error)))

(local (in-theory (disable lw-zeta-native-derivative-request)))

(defthm lw-zeta-native-derivative-request-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-native-derivative-request rate height error)) (< 0 (lw-zeta-native-derivative-request rate height error)) (<= (lw-zeta-native-derivative-request rate height error) (/ error 2))
       (<= (* (lw-zeta-native-derivative-gain rate height) (lw-zeta-native-derivative-request rate height error)) (/ error 2))))
 :hints (("Goal"
  :use (lw-zeta-native-derivative-gain-valid
        (:instance lw-euler-rounding-precision-valid (cost (lw-zeta-native-derivative-gain rate height)))
        (:instance lw-znd-multiply-order (a (lw-zeta-native-derivative-request rate height error)) (b (lw-euler-rounding-precision (lw-zeta-native-derivative-gain rate height) error)) (factor (lw-zeta-native-derivative-gain rate height))))
  :in-theory (union-theories
 '(lw-zeta-native-derivative-request min lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-zeta-native-derivative-computed-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-native-derivative-request rate height error)) (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height (lw-zeta-native-derivative-request rate height error)))) error))
 :hints (("Goal"
  :use (lw-zeta-native-derivative-request-data
        (:instance lw-complex-zeta-native-derivative-agreement (error (lw-zeta-native-derivative-request rate height error)) (series-error (lw-zeta-native-derivative-request rate height error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-native-derivative-request rate height error)) (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height (lw-zeta-native-derivative-request rate height error)))))
         (radius (+ (lw-zeta-native-derivative-request rate height error) (* 3/8 (lw-zeta-native-derivative-gain rate height) (lw-zeta-native-derivative-request rate height error)))) (cap error)))
  :in-theory (union-theories
 '( lw-znd-left-commutes lw-znd-left-distributes lw-znd-fold-constants lw-znd-times-negative lw-znd-negative-times lw-znd-zero-times lw-znd-minus-one lw-znd-double-negative lw-znd-add-cancel lw-znd-double lw-znd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


