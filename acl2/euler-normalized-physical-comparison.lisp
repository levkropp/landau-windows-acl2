; Compare physical normalized coefficients with independently requested models.
(in-package "ACL2")
(include-book "euler-normalized-physical-coefficients")
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
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-local-normalized-radius
 lw-euler-local-normalized-polynomial lw-euler-local-coefficient-request
 lw-complex-euler-normalized-physical-coefficient-value
 lw-complex-euler-local-normalized-coefficient-value
 lw-complex-euler-local-normalized-polynomial-coefficient lw-complex-coefficient-at)))
(local (defthm lw-npcp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-npcp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-npcp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-npcp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-npcp-times-negative (a b) (b a)))
                 :in-theory (disable lw-npcp-times-negative)))))

(local (defthm lw-npcp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-npcp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-npcp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-npcp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-npcp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-npcp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-npcp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-npcp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-npcp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-npcp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-npcp-left-commutes)))))
(local (defthm lw-npcp-divide-difference
 (implies (and (rationalp factor) (not (equal factor 0)) (lw-complexp left) (lw-complexp right))
 (equal (lw-complex-scale (/ factor) (lw-complex-sub left (lw-complex-scale factor right)))
        (lw-complex-sub (lw-complex-scale (/ factor) left) right)))
 :hints (("Goal"
 :use ((:instance lw-npcp-inverse-factor (divisor factor) (coefficient (car right)))
       (:instance lw-npcp-inverse-factor (divisor factor) (coefficient (cdr right))))
 :in-theory (union-theories
 '(lw-complexp lw-complex-scale lw-complex-sub lw-npcp-left-commutes lw-npcp-left-distributes lw-npcp-fold-constants lw-npcp-times-negative lw-npcp-negative-times lw-npcp-zero-times lw-npcp-minus-one lw-npcp-double-negative lw-npcp-add-cancel lw-npcp-double lw-npcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-complex-euler-normalized-physical-polynomial-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (natp target)
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp polynomial-error) (< 0 polynomial-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target polynomial-error) index 0))
  (+ (* 1/2 coefficient-error) (* 1/2 polynomial-error (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data
       (:instance lw-euler-local-coefficient-request-valid (radius (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (error coefficient-error))
       (:instance lw-euler-local-normalized-polynomial-valid (error polynomial-error))
       (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target polynomial-error)) (target index) (offset 0))
       (:instance lw-complex-euler-local-normalized-coefficient-value-rational (error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index coefficient-error)))
       (:instance lw-complex-euler-local-normalized-polynomial-coefficient-scaling (error polynomial-error))
       (:instance lw-complex-euler-local-normalized-coefficient-polynomial-comparison (coefficient-error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index coefficient-error)))
       (:instance lw-npcp-inverse-factor (divisor (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (coefficient 1))
       (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index coefficient-error)) (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error target index polynomial-error)))
        (factor (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))) (radius (* 1/2 (+ (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index coefficient-error) polynomial-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index coefficient-error) (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target polynomial-error) index 0)))
        (radius (* 1/2 (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (+ (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index coefficient-error) polynomial-error)))
        (cap (+ (* 1/2 coefficient-error) (* 1/2 polynomial-error (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))))))
 :in-theory (union-theories
 '(lw-npcp-divide-difference lw-complex-scale-rational lw-complex-euler-local-normalized-polynomial-coefficient-scaling lw-complex-euler-normalized-physical-coefficient-value lw-complex-sub-scales lw-complex-scale-compose lw-complex-scale-one abs lw-npcp-left-commutes lw-npcp-left-distributes lw-npcp-fold-constants lw-npcp-times-negative lw-npcp-negative-times lw-npcp-zero-times lw-npcp-minus-one lw-npcp-double-negative lw-npcp-add-cancel lw-npcp-double lw-npcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
