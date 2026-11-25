(in-package "ACL2")

(include-book "zeta-euler-log-derivative")
(include-book "dirichlet-series-ratio")

; Identify the evaluated negative logarithmic derivative with
; the already-constructed native zeta series ratio.

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

(local (in-theory (disable lw-zeta-euler-log-derivative-cap)))

(local (in-theory (disable lw-zeta-euler-log-derivative-cost)))

(local (in-theory (disable lw-zeta-euler-log-derivative-request)))

(local (in-theory (disable lw-complex-zeta-euler-log-derivative-value)))
(local (in-theory (disable lw-complex-zeta-log-quotient-value lw-zeta-log-quotient-precision)))

(local (defthm lw-znld-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-znld-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-znld-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-znld-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-znld-times-negative (a b) (b a)))
                 :in-theory (disable lw-znld-times-negative)))))

(local (defthm lw-znld-zero-times (equal (* 0 a) 0)))

(local (defthm lw-znld-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-znld-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-znld-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-znld-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-znld-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-znld-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-znld-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-znld-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-znld-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-znld-left-commutes)))))

(defun lw-zeta-native-log-derivative-cost (rate height)
 (+ (* 3/2 (lw-zeta-native-derivative-gain rate height)) (* 18 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1))))

(local (in-theory (disable lw-zeta-native-log-derivative-cost)))

(defthm lw-zeta-native-log-derivative-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (rationalp (lw-zeta-native-log-derivative-cost rate height)) (< 0 (lw-zeta-native-log-derivative-cost rate height))))
 :hints (("Goal"
  :use (lw-zeta-native-derivative-gain-valid lw-zeta-euler-inverse-cap-data
        (:instance lw-euler-disk-envelope-data (radius 0))
        (:instance lw-znld-positive-product (a (lw-zeta-euler-inverse-cap rate height)) (b (+ rate (abs height) 1))))
  :in-theory (union-theories
 '(lw-zeta-native-log-derivative-cost lw-znld-left-commutes lw-znld-left-distributes lw-znld-fold-constants lw-znld-times-negative lw-znld-negative-times lw-znld-zero-times lw-znld-minus-one lw-znld-double-negative lw-znld-add-cancel lw-znld-double lw-znld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-znld-minus-residual
 (implies (and (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-scale -1 (lw-complex-sub left (lw-complex-scale -1 right)))
         (lw-complex-sub (lw-complex-scale -1 left) right)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-znld-left-commutes lw-znld-left-distributes lw-znld-fold-constants lw-znld-times-negative lw-znld-negative-times lw-znld-zero-times lw-znld-minus-one lw-znld-double-negative lw-znld-add-cancel lw-znld-double lw-znld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-zeta-log-derivative-native-precision-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error) (rationalp ratio-error) (< 0 ratio-error)) (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error)) (+ (* 16 (lw-zeta-euler-log-derivative-request rate height radius error)) (* (lw-zeta-native-log-derivative-cost rate height) (lw-zeta-log-quotient-precision ratio-error)))))
 :hints (("Goal"
  :use (lw-zeta-euler-log-derivative-request-data lw-zeta-native-log-derivative-cost-valid
        lw-zeta-native-derivative-gain-valid lw-zeta-euler-inverse-cap-data
        lw-euler-disk-envelope-data
        (:instance lw-zeta-log-quotient-precision-valid (error ratio-error))
        (:instance lw-complex-zeta-euler-derivative-rational (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error (lw-zeta-log-quotient-precision ratio-error)))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error (lw-zeta-log-quotient-precision ratio-error)))
        (:instance lw-complex-zeta-euler-clearance (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-series-clearance (error (lw-zeta-log-quotient-precision ratio-error)))
        (:instance lw-complex-zeta-series-log-cap (error (lw-zeta-log-quotient-precision ratio-error)))
        (:instance lw-complex-zeta-native-derivative-agreement (error (lw-zeta-euler-log-derivative-request rate height radius error)) (series-error (lw-zeta-log-quotient-precision ratio-error)))
        (:instance lw-complex-zeta-euler-series-agreement (euler-error (lw-zeta-euler-log-derivative-request rate height radius error)) (series-error (lw-zeta-log-quotient-precision ratio-error)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision ratio-error))))) (factor -1) (radius (+ (lw-zeta-euler-log-derivative-request rate height radius error) (* 3/8 (lw-zeta-native-derivative-gain rate height) (lw-zeta-log-quotient-precision ratio-error)))))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-scale -1 (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius error)))) (denominator (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error)))
         (approximate-numerator (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision ratio-error))) (approximate-denominator (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision ratio-error)))
         (left-clearance 1/4) (right-clearance 1/4) (numerator-cap 3)
         (numerator-error (+ (lw-zeta-euler-log-derivative-request rate height radius error) (* 3/8 (lw-zeta-native-derivative-gain rate height) (lw-zeta-log-quotient-precision ratio-error)))) (denominator-error (+ (* 1/4 (lw-zeta-euler-log-derivative-request rate height radius error)) (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) (lw-zeta-log-quotient-precision ratio-error)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error))) (radius (+ (* 4 (+ (lw-zeta-euler-log-derivative-request rate height radius error) (* 3/8 (lw-zeta-native-derivative-gain rate height) (lw-zeta-log-quotient-precision ratio-error)))) (* 48 (+ (* 1/4 (lw-zeta-euler-log-derivative-request rate height radius error)) (* 3/8 (lw-zeta-euler-inverse-cap rate height) (+ rate (abs height) 1) (lw-zeta-log-quotient-precision ratio-error)))))) (cap (+ (* 16 (lw-zeta-euler-log-derivative-request rate height radius error)) (* (lw-zeta-native-log-derivative-cost rate height) (lw-zeta-log-quotient-precision ratio-error))))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-log-derivative-value lw-complex-zeta-log-quotient-value lw-zeta-native-log-derivative-cost lw-znld-minus-residual lw-complex-scale-rational abs lw-znld-left-commutes lw-znld-left-distributes lw-znld-fold-constants lw-znld-times-negative lw-znld-negative-times lw-znld-zero-times lw-znld-minus-one lw-znld-double-negative lw-znld-add-cancel lw-znld-double lw-znld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-znld-with-auxiliary-error
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error) (rationalp ratio-error) (< 0 ratio-error)) (rationalp aux-error) (< 0 aux-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error)) (+ error ratio-error (* (+ 1 (lw-zeta-native-log-derivative-cost rate height)) aux-error))))
 :hints (("Goal"
  :use (lw-zeta-native-log-derivative-cost-valid lw-zeta-euler-log-derivative-request-data
        lw-complex-zeta-euler-log-derivative-rational
        (:instance lw-complex-zeta-log-quotient-value-rational (error ratio-error))
        (:instance lw-complex-zeta-log-quotient-value-rational (error aux-error))
        (:instance lw-complex-zeta-log-quotient-value-cauchy (left-error aux-error) (right-error ratio-error))
        (:instance lw-zeta-log-quotient-precision-small (error aux-error))
        (:instance lw-zeta-log-quotient-precision-valid (error aux-error))
        (:instance lw-complex-zeta-log-derivative-native-precision-agreement (ratio-error aux-error))
        (:instance lw-znld-multiply-order (a (lw-zeta-log-quotient-precision aux-error)) (b aux-error) (factor (lw-zeta-native-log-derivative-cost rate height)))
        (:instance lw-complex-difference-triangle (left (lw-complex-zeta-euler-log-derivative-value rate height radius error)) (middle (lw-complex-zeta-log-quotient-value rate height aux-error)) (right (lw-complex-zeta-log-quotient-value rate height ratio-error))
         (radius (+ (* 16 (lw-zeta-euler-log-derivative-request rate height radius error)) (* (lw-zeta-native-log-derivative-cost rate height) (lw-zeta-log-quotient-precision aux-error)))) (other-radius (+ aux-error ratio-error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error)))
         (radius (+ (* 16 (lw-zeta-euler-log-derivative-request rate height radius error)) (* (lw-zeta-native-log-derivative-cost rate height) (lw-zeta-log-quotient-precision aux-error)) aux-error ratio-error))
         (cap (+ error ratio-error (* (+ 1 (lw-zeta-native-log-derivative-cost rate height)) aux-error)))))
  :in-theory (union-theories
 '( lw-znld-left-commutes lw-znld-left-distributes lw-znld-fold-constants lw-znld-times-negative lw-znld-negative-times lw-znld-zero-times lw-znld-minus-one lw-znld-double-negative lw-znld-add-cancel lw-znld-double lw-znld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-log-derivative-native-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error) (rationalp ratio-error) (< 0 ratio-error)) (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error)) (+ error ratio-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error)) (+ error ratio-error)))
  :use (lw-zeta-native-log-derivative-cost-valid lw-complex-zeta-euler-log-derivative-rational
        (:instance lw-complex-zeta-log-quotient-value-rational (error ratio-error))
        (:instance lw-complex-operations-rational (left (lw-complex-zeta-euler-log-derivative-value rate height radius error)) (right (lw-complex-zeta-log-quotient-value rate height ratio-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error))) (radius (+ error ratio-error)) (cost (+ 1 (lw-zeta-native-log-derivative-cost rate height))))
        (:instance lw-znld-with-auxiliary-error (aux-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-log-quotient-value rate height ratio-error)) (+ error ratio-error) (+ 1 (lw-zeta-native-log-derivative-cost rate height))))))
  :in-theory (union-theories
 '( lw-znld-left-commutes lw-znld-left-distributes lw-znld-fold-constants lw-znld-times-negative lw-znld-negative-times lw-znld-zero-times lw-znld-minus-one lw-znld-double-negative lw-znld-add-cancel lw-znld-double lw-znld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-zeta-log-derivative-native-computed-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius (/ error 2))
                   (lw-complex-zeta-log-quotient-value rate height (/ error 2))) error))
 :hints (("Goal"
  :use ((:instance lw-complex-zeta-log-derivative-native-agreement (error (/ error 2)) (ratio-error (/ error 2))))
  :in-theory (union-theories
 '( lw-znld-left-commutes lw-znld-left-distributes lw-znld-fold-constants lw-znld-times-negative lw-znld-negative-times lw-znld-zero-times lw-znld-minus-one lw-znld-double-negative lw-znld-add-cancel lw-znld-double lw-znld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


