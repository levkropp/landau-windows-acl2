(in-package "ACL2")

(include-book "zeta-native-derivative")
(include-book "zeta-series-clearance")

; Transfer the native ordinary-series cap to the actual normalized
; evaluator, then obtain a checked denominator clearance.

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

(local (defthm lw-zecl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zecl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zecl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zecl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zecl-times-negative (a b) (b a)))
                 :in-theory (disable lw-zecl-times-negative)))))

(local (defthm lw-zecl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zecl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zecl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zecl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zecl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zecl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zecl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zecl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zecl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zecl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zecl-left-commutes)))))

(local (defthm lw-zecl-square-nonnegative
 (implies (rationalp value) (<= 0 (* value value)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-zeta-euler-clearance-cost (rate height)
 (+ 1 (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1))))

(local (in-theory (disable lw-zeta-euler-clearance-cost)))

(defthm lw-zeta-euler-clearance-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (rationalp (lw-zeta-euler-clearance-cost rate height)) (< 0 (lw-zeta-euler-clearance-cost rate height))))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-euler-disk-envelope-data (radius 0))
        (:instance lw-zecl-positive-product (a (lw-zeta-euler-inverse-cap rate height)) (b (+ rate (abs height) 1))))
  :in-theory (union-theories
 '(lw-zeta-euler-clearance-cost lw-zecl-left-commutes lw-zecl-left-distributes lw-zecl-fold-constants lw-zecl-times-negative lw-zecl-negative-times lw-zecl-zero-times lw-zecl-minus-one lw-zecl-double-negative lw-zecl-add-cancel lw-zecl-double lw-zecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-zecl-cap-with-native-error
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error) (rationalp series-error) (< 0 series-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-value rate height error) (cons 1 0)) (+ (+ 1/2 (* 1/4 error)) (* (lw-zeta-euler-clearance-cost rate height) series-error))))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-euler-disk-envelope-data (radius 0))
        (:instance lw-complex-zeta-euler-value-rational)
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error series-error))
        (:instance lw-complex-zeta-series-ordinary-cap (error series-error))
        (:instance lw-complex-zeta-euler-series-agreement (euler-error error))
        (:instance lw-complex-difference-triangle (left (lw-complex-zeta-euler-value rate height error)) (middle (lw-complex-zeta-series-value nil rate height series-error)) (right (cons 1 0))
         (radius (+ (* 1/4 error) (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) series-error)))
         (other-radius (+ 1/2 series-error))))
  :in-theory (union-theories
 '(lw-zeta-euler-clearance-cost (:executable-counterpart lw-complexp) lw-zecl-left-commutes lw-zecl-left-distributes lw-zecl-fold-constants lw-zecl-times-negative lw-zecl-negative-times lw-zecl-zero-times lw-zecl-minus-one lw-zecl-double-negative lw-zecl-add-cancel lw-zecl-double lw-zecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-euler-ordinary-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-value rate height error) (cons 1 0)) (+ 1/2 (* 1/4 error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-value rate height error) (cons 1 0)) (+ 1/2 (* 1/4 error))))
  :use (lw-zeta-euler-clearance-cost-valid lw-complex-zeta-euler-value-rational
        (:instance lw-complex-operations-rational (left (lw-complex-zeta-euler-value rate height error)) (right (cons 1 0)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-zeta-euler-value rate height error) (cons 1 0))) (radius (+ 1/2 (* 1/4 error))) (cost (lw-zeta-euler-clearance-cost rate height)))
        (:instance lw-zecl-cap-with-native-error (series-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-zeta-euler-value rate height error) (cons 1 0)) (+ 1/2 (* 1/4 error)) (lw-zeta-euler-clearance-cost rate height)))))
  :in-theory (union-theories
 '((:executable-counterpart lw-complexp) lw-zecl-left-commutes lw-zecl-left-distributes lw-zecl-fold-constants lw-zecl-times-negative lw-zecl-negative-times lw-zecl-zero-times lw-zecl-minus-one lw-zecl-double-negative lw-zecl-add-cancel lw-zecl-double lw-zecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-zeta-euler-clearance
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error) (<= error 1))
  (and (<= 1/16 (lw-complex-norm-square (lw-complex-zeta-euler-value rate height error))) (not (equal (lw-complex-zeta-euler-value rate height error) (cons 0 0)))))
 :hints (("Goal"
  :use (lw-complex-zeta-euler-ordinary-cap lw-complex-zeta-euler-value-rational
        (:instance lw-zecl-square-nonnegative (value (cdr (lw-complex-zeta-euler-value rate height error))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-value rate height error) (cons 1 0))) (radius (+ 1/2 (* 1/4 error))) (cap 3/4))
        (:instance lw-complex-disk-coordinates (point (lw-complex-sub (lw-complex-zeta-euler-value rate height error) (cons 1 0))) (radius 3/4)))
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-norm-square abs lw-zecl-left-commutes lw-zecl-left-distributes lw-zecl-fold-constants lw-zecl-times-negative lw-zecl-negative-times lw-zecl-zero-times lw-zecl-minus-one lw-zecl-double-negative lw-zecl-add-cancel lw-zecl-double lw-zecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-complex-zeta-euler-reciprocal-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-reciprocal (lw-complex-zeta-euler-value rate height error)) 4))
 :hints (("Goal"
  :use (lw-complex-zeta-euler-clearance lw-complex-zeta-euler-value-rational
        (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-zeta-euler-value rate height error)) (lower 1/4)))
  :in-theory (union-theories
 '( lw-zecl-left-commutes lw-zecl-left-distributes lw-zecl-fold-constants lw-zecl-times-negative lw-zecl-negative-times lw-zecl-zero-times lw-zecl-minus-one lw-zecl-double-negative lw-zecl-add-cancel lw-zecl-double lw-zecl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

