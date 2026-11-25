; Uniform quotient polynomials are coherent across target and accuracy choices.
(in-package "ACL2")
(include-book "euler-uniform-log-derivative")
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

(local (in-theory (disable lw-euler-uniform-polynomial
 lw-complex-euler-continuation-value lw-polynomial-affine
 lw-polynomial-multiply-linear lw-polynomial-add-constant)))
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-neighborhood-radius
 lw-euler-uniform-log-polynomial lw-complex-polynomial lw-complex-euler-log-derivative-value)))
(local (defthm lw-elpc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-elpc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-elpc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-elpc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-elpc-times-negative (a b) (b a)))
                 :in-theory (disable lw-elpc-times-negative)))))

(local (defthm lw-elpc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-elpc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-elpc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-elpc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-elpc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-elpc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-elpc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-elpc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-elpc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-elpc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-elpc-left-commutes)))))

(local (defthm lw-elpc-point-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
 (and (lw-complexp point) (rationalp (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (< 0 (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
      (rationalp (+ rate (car point))) (< (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (+ rate (car point))) (rationalp (+ height (cdr point)))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-shifted-center-data (center point) (radius (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))))
 :in-theory (union-theories
 '( lw-elpc-left-commutes lw-elpc-left-distributes lw-elpc-fold-constants lw-elpc-times-negative lw-elpc-negative-times lw-elpc-zero-times lw-elpc-minus-one lw-elpc-double-negative lw-elpc-add-cancel lw-elpc-double lw-elpc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-elpc-polynomial-with-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (+ left-error right-error (* 2 value-error))))
 :hints (("Goal"
 :use (lw-elpc-point-data lw-euler-neighborhood-shifted-check
       (:instance lw-euler-uniform-log-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-uniform-log-polynomial-valid (target right-target) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error)) (offset 0))
       (:instance lw-complex-euler-log-derivative-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (anchor-error (* 1/2 anchor-error)) (error value-error))
       (:instance lw-complex-euler-uniform-log-comparison (target left-target) (error left-error) (coefficient-radius (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
       (:instance lw-complex-euler-uniform-log-comparison (target right-target) (error right-error) (coefficient-radius (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
       (:instance lw-complex-difference-symmetric (left (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (* 1/2 anchor-error) value-error)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0)) (radius (+ left-error value-error)))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0)) (middle (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) (- outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (* 1/2 anchor-error) value-error)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0))
        (radius (+ left-error value-error)) (other-radius (+ right-error value-error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0)))
        (radius (+ left-error value-error right-error value-error)) (cap (+ left-error right-error (* 2 value-error)))))
 :in-theory (union-theories
 '( lw-elpc-left-commutes lw-elpc-left-distributes lw-elpc-fold-constants lw-elpc-times-negative lw-elpc-negative-times lw-elpc-zero-times lw-elpc-minus-one lw-elpc-double-negative lw-elpc-add-cancel lw-elpc-double lw-elpc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-log-polynomial-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (+ left-error right-error)))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (+ left-error right-error)))
 :use (lw-elpc-point-data
       (:instance lw-euler-uniform-log-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-uniform-log-polynomial-valid (target right-target) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error)) (offset 0))
       (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes
        (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0))) (radius (+ left-error right-error)) (cost 2))
       (:instance lw-elpc-polynomial-with-margin
        (value-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error right-target right-error) point 0)) (+ left-error right-error) 2))))
 :in-theory (union-theories
 '( lw-elpc-left-commutes lw-elpc-left-distributes lw-elpc-fold-constants lw-elpc-times-negative lw-elpc-negative-times lw-elpc-zero-times lw-elpc-minus-one lw-elpc-double-negative lw-elpc-add-cancel lw-elpc-double lw-elpc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

