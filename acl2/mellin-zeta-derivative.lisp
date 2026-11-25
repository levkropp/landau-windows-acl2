(in-package "ACL2")

(include-book "zeta-native-log-derivative")
(include-book "mellin-zeta-series")

; Normalize the actual evaluated negative logarithmic derivative and
; identify it with the existing computed improper Mellin value.

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

(local (in-theory (disable lw-zeta-native-log-derivative-cost)))
(local (in-theory
 (disable lw-dirichlet-transform lw-mellin-zeta-ratio-value lw-mellin-zeta-ratio-request lw-mellin-integral)))

(local (defthm lw-mzd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mzd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mzd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mzd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mzd-times-negative (a b) (b a)))
                 :in-theory (disable lw-mzd-times-negative)))))

(local (defthm lw-mzd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mzd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mzd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mzd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mzd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mzd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mzd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mzd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mzd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mzd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mzd-left-commutes)))))

(local (defthm lw-mzd-euler-rational
 (implies (and (rationalp error) (< 0 error)) (rationalp (car (lw-euler-bounds error))))
 :hints (("Goal" :use ((:instance lw-euler-bounds-interval (epsilon error)))
                 :in-theory (union-theories
 '(lw-intervalp lw-mzd-left-commutes lw-mzd-left-distributes lw-mzd-fold-constants lw-mzd-times-negative lw-mzd-negative-times lw-mzd-zero-times lw-mzd-minus-one lw-mzd-double-negative lw-mzd-add-cancel lw-mzd-double lw-mzd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-mellin-zeta-derivative-value (rate height radius error)
 (lw-dirichlet-transform rate height (lw-complex-zeta-euler-log-derivative-value rate height radius (* 1/4 error)) (car (lw-euler-bounds (* 1/4 error)))))

(local (in-theory (disable lw-mellin-zeta-derivative-value)))

(defthm lw-mellin-zeta-derivative-value-rational
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-zeta-derivative-value rate height radius error)))
 :hints (("Goal"
  :use ((:instance lw-mzd-euler-rational (error (* 1/4 error)))
        (:instance lw-complex-zeta-euler-log-derivative-rational (error (* 1/4 error)))
        (:instance lw-dirichlet-transform-rational
         (prime-value (lw-complex-zeta-euler-log-derivative-value rate height radius (* 1/4 error))) (gamma-value (car (lw-euler-bounds (* 1/4 error))))))
  :in-theory (union-theories
 '(lw-mellin-zeta-derivative-value lw-mzd-left-commutes lw-mzd-left-distributes lw-mzd-fold-constants lw-mzd-times-negative lw-mzd-negative-times lw-mzd-zero-times lw-mzd-minus-one lw-mzd-double-negative lw-mzd-add-cancel lw-mzd-double lw-mzd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-mellin-zeta-derivative-value-cauchy
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-zeta-derivative-value rate height radius left-error) (lw-mellin-zeta-derivative-value rate height radius right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-mzd-euler-rational (error (* 1/4 left-error)))
        (:instance lw-mzd-euler-rational (error (* 1/4 right-error)))
        (:instance lw-complex-zeta-euler-log-derivative-rational (error (* 1/4 left-error)))
        (:instance lw-complex-zeta-euler-log-derivative-rational (error (* 1/4 right-error)))
        (:instance lw-complex-zeta-euler-log-derivative-cauchy (left-error (* 1/4 left-error)) (right-error (* 1/4 right-error)))
        (:instance lw-euler-lower-cauchy (left-error (* 1/4 left-error)) (right-error (* 1/4 right-error)))
        (:instance lw-dirichlet-transform-transport
         (left (lw-complex-zeta-euler-log-derivative-value rate height radius (* 1/4 left-error))) (right (lw-complex-zeta-euler-log-derivative-value rate height radius (* 1/4 right-error)))
         (left-gamma (car (lw-euler-bounds (* 1/4 left-error)))) (right-gamma (car (lw-euler-bounds (* 1/4 right-error))))
         (prime-error (+ (* 1/4 left-error) (* 1/4 right-error))) (gamma-error (+ (* 1/4 left-error) (* 1/4 right-error)))))
  :in-theory (union-theories
 '(lw-mellin-zeta-derivative-value lw-mzd-left-commutes lw-mzd-left-distributes lw-mzd-fold-constants lw-mzd-times-negative lw-mzd-negative-times lw-mzd-zero-times lw-mzd-minus-one lw-mzd-double-negative lw-mzd-add-cancel lw-mzd-double lw-mzd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-mellin-zeta-derivative-native-comparison
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-zeta-derivative-value rate height radius left-error) (lw-mellin-zeta-ratio-value rate height right-error))
                    (+ (* 1/2 left-error) (* 1/4 right-error))))
 :hints (("Goal"
  :use ((:instance lw-mellin-zeta-ratio-request-valid (error right-error))
        (:instance lw-mzd-euler-rational (error (* 1/4 left-error)))
        (:instance lw-mzd-euler-rational (error (lw-mellin-zeta-ratio-request rate height right-error)))
        (:instance lw-complex-zeta-euler-log-derivative-rational (error (* 1/4 left-error)))
        (:instance lw-complex-zeta-log-quotient-value-rational (error (lw-mellin-zeta-ratio-request rate height right-error)))
        (:instance lw-complex-zeta-log-derivative-native-agreement (error (* 1/4 left-error)) (ratio-error (lw-mellin-zeta-ratio-request rate height right-error)))
        (:instance lw-euler-lower-cauchy (left-error (* 1/4 left-error)) (right-error (lw-mellin-zeta-ratio-request rate height right-error)))
        (:instance lw-dirichlet-transform-transport
         (left (lw-complex-zeta-euler-log-derivative-value rate height radius (* 1/4 left-error))) (right (lw-complex-zeta-log-quotient-value rate height (lw-mellin-zeta-ratio-request rate height right-error)))
         (left-gamma (car (lw-euler-bounds (* 1/4 left-error)))) (right-gamma (car (lw-euler-bounds (lw-mellin-zeta-ratio-request rate height right-error))))
         (prime-error (+ (* 1/4 left-error) (lw-mellin-zeta-ratio-request rate height right-error))) (gamma-error (+ (* 1/4 left-error) (lw-mellin-zeta-ratio-request rate height right-error))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-zeta-derivative-value rate height radius left-error) (lw-mellin-zeta-ratio-value rate height right-error)))
         (radius (+ (* 1/2 left-error) (* 2 (lw-mellin-zeta-ratio-request rate height right-error)))) (cap (+ (* 1/2 left-error) (* 1/4 right-error)))))
  :in-theory (union-theories
 '(lw-mellin-zeta-derivative-value lw-mellin-zeta-ratio-value lw-mzd-left-commutes lw-mzd-left-distributes lw-mzd-fold-constants lw-mzd-times-negative lw-mzd-negative-times lw-mzd-zero-times lw-mzd-minus-one lw-mzd-double-negative lw-mzd-add-cancel lw-mzd-double lw-mzd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-mzd-with-auxiliary-error
 (implies (and (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)) (rationalp aux-error) (< 0 aux-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-derivative-value rate height radius right-error)) (+ (+ (* 5 left-error) (* 1/2 right-error)) (* 5/4 aux-error))))
 :hints (("Goal"
  :use ((:instance lw-mellin-integral-rational (sigma rate) (index 0) (error left-error))
        (:instance lw-mellin-zeta-derivative-value-rational (error right-error))
        (:instance lw-mellin-zeta-ratio-value-rational (error aux-error))
        (:instance lw-mellin-zeta-series-ratio-comparison (right-error aux-error))
        (:instance lw-mellin-zeta-derivative-native-comparison (left-error right-error) (right-error aux-error))
        (:instance lw-complex-difference-symmetric (left (lw-mellin-zeta-derivative-value rate height radius right-error)) (right (lw-mellin-zeta-ratio-value rate height aux-error))
         (radius (+ (* 1/2 right-error) (* 1/4 aux-error))))
        (:instance lw-complex-difference-triangle (left (lw-mellin-integral rate height 0 left-error)) (middle (lw-mellin-zeta-ratio-value rate height aux-error)) (right (lw-mellin-zeta-derivative-value rate height radius right-error))
         (radius (+ (* 5 left-error) aux-error)) (other-radius (+ (* 1/2 right-error) (* 1/4 aux-error))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-derivative-value rate height radius right-error)))
         (radius (+ (* 5 left-error) aux-error (* 1/2 right-error) (* 1/4 aux-error)))
         (cap (+ (+ (* 5 left-error) (* 1/2 right-error)) (* 5/4 aux-error)))))
  :in-theory (union-theories
 '( lw-mzd-left-commutes lw-mzd-left-distributes lw-mzd-fold-constants lw-mzd-times-negative lw-mzd-negative-times lw-mzd-zero-times lw-mzd-minus-one lw-mzd-double-negative lw-mzd-add-cancel lw-mzd-double lw-mzd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-zeta-derivative-comparison
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)) (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-derivative-value rate height radius right-error)) (+ (* 5 left-error) (* 1/2 right-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-derivative-value rate height radius right-error)) (+ (* 5 left-error) (* 1/2 right-error))))
  :use ((:instance lw-mellin-integral-rational (sigma rate) (index 0) (error left-error))
        (:instance lw-mellin-zeta-derivative-value-rational (error right-error))
        (:instance lw-complex-operations-rational (left (lw-mellin-integral rate height 0 left-error)) (right (lw-mellin-zeta-derivative-value rate height radius right-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-derivative-value rate height radius right-error))) (radius (+ (* 5 left-error) (* 1/2 right-error))) (cost 5/4))
        (:instance lw-mzd-with-auxiliary-error (aux-error (lw-disk-gap-refinement (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-derivative-value rate height radius right-error)) (+ (* 5 left-error) (* 1/2 right-error)) 5/4))))
  :in-theory (union-theories
 '( lw-mzd-left-commutes lw-mzd-left-distributes lw-mzd-fold-constants lw-mzd-times-negative lw-mzd-negative-times lw-mzd-zero-times lw-mzd-minus-one lw-mzd-double-negative lw-mzd-add-cancel lw-mzd-double lw-mzd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-mellin-zeta-derivative-computed-comparison
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-mellin-integral rate height 0 (/ error 10))
                   (lw-mellin-zeta-derivative-value rate height radius error)) error))
 :hints (("Goal"
  :use ((:instance lw-mellin-zeta-derivative-comparison (left-error (/ error 10)) (right-error error)))
  :in-theory (union-theories
 '( lw-mzd-left-commutes lw-mzd-left-distributes lw-mzd-fold-constants lw-mzd-times-negative lw-mzd-negative-times lw-mzd-zero-times lw-mzd-minus-one lw-mzd-double-negative lw-mzd-add-cancel lw-mzd-double lw-mzd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


