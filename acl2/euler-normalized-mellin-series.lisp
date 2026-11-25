; Identify the normalized coefficient series with the actual Mellin evaluator.
(in-package "ACL2")
(include-book "euler-normalized-inner-series")
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
 lw-euler-local-normalized-anchor lw-euler-zeta-clearance-request lw-mellin-euler-log-extended-value
 lw-complex-euler-normalized-inner-series-value lw-mellin-integral)))
(local (defthm lw-nms-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nms-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nms-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nms-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nms-times-negative (a b) (b a)))
                 :in-theory (disable lw-nms-times-negative)))))

(local (defthm lw-nms-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nms-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nms-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nms-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nms-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nms-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nms-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nms-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nms-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nms-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nms-left-commutes)))))
(local (defthm lw-nms-comparison-with-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner) (< 3 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))
 (rationalp error) (< 0 error) (rationalp integral-error) (< 0 integral-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error)) (+ (+ (* 1/2 error) (* 5 integral-error)) margin)))
 :hints (("Goal"
 :use (lw-euler-normalized-inner-point-data lw-euler-local-normalized-data
       lw-complex-euler-normalized-inner-series-value-rational
       (:instance lw-mellin-integral-rational (sigma (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (index 0) (error integral-error))
       (:instance lw-euler-zeta-clearance-check (rate (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (radius (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (anchor-error (lw-euler-zeta-clearance-request (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (error margin))
       (:instance lw-complex-euler-normalized-inner-series-value-agreement (local-anchor (lw-euler-zeta-clearance-request (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (coefficient-radius (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (value-error margin))
       (:instance lw-mellin-euler-log-extended-right-comparison (rate (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (radius (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (euler-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error)) (right (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (lw-euler-zeta-clearance-request (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) margin)) (radius (+ (* 5 integral-error) (* 1/2 margin))))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error)) (middle (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (lw-euler-zeta-clearance-request (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) margin)) (right (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error))
        (radius (* 1/2 (+ error margin))) (other-radius (+ (* 5 integral-error) (* 1/2 margin)))))
 :in-theory (union-theories
 '(lw-complexp lw-nms-left-commutes lw-nms-left-distributes lw-nms-fold-constants lw-nms-times-negative lw-nms-negative-times lw-nms-zero-times lw-nms-minus-one lw-nms-double-negative lw-nms-add-cancel lw-nms-double lw-nms-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-normalized-inner-series-mellin-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner) (< 3 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))
 (rationalp error) (< 0 error) (rationalp integral-error) (< 0 integral-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error)) (+ (* 1/2 error) (* 5 integral-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error)) (+ (* 1/2 error) (* 5 integral-error))))
 :use (lw-euler-normalized-inner-point-data lw-euler-local-normalized-data
       lw-complex-euler-normalized-inner-series-value-rational
       (:instance lw-mellin-integral-rational (sigma (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (index 0) (error integral-error))
       (:instance lw-complex-operations-rational (left (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error)) (right (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error))) (radius (+ (* 1/2 error) (* 5 integral-error))) (cost 1))
       (:instance lw-nms-comparison-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 integral-error)) (+ (* 1/2 error) (* 5 integral-error)) 1))))
 :in-theory (union-theories
 '( lw-nms-left-commutes lw-nms-left-distributes lw-nms-fold-constants lw-nms-times-negative lw-nms-negative-times lw-nms-zero-times lw-nms-minus-one lw-nms-double-negative lw-nms-add-cancel lw-nms-double lw-nms-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-normalized-inner-series-computed-mellin-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner) (< 3 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (rationalp error) (< 0 error))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-integral (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) 0 (* 1/10 error))) error))
 :hints (("Goal"
 :use ((:instance lw-complex-euler-normalized-inner-series-mellin-comparison (integral-error (* 1/10 error))))
 :in-theory (union-theories
 '( lw-nms-left-commutes lw-nms-left-distributes lw-nms-fold-constants lw-nms-times-negative lw-nms-negative-times lw-nms-zero-times lw-nms-minus-one lw-nms-double-negative lw-nms-add-cancel lw-nms-double lw-nms-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
