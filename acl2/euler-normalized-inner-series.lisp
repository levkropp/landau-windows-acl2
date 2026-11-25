; Reconstruct normalized Euler values from canonical coefficients on inner disks.
(in-package "ACL2")
(include-book "euler-normalized-series-coefficients")
(include-book "polynomial-geometric-bounds")
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
(local (in-theory (disable lw-euler-value-clearance-check
 lw-euler-local-normalized-radius lw-euler-local-normalized-cap lw-euler-local-normalized-polynomial
 lw-euler-local-normalized-coefficient-polynomial lw-euler-local-normalized-anchor
 lw-complex-euler-normalized-series-prefix lw-euler-normalized-series-coefficients
 lw-euler-normalized-series-prefix-difference lw-mellin-euler-log-extended-value
 lw-polynomial-pad lw-polynomial-difference lw-polynomial-rescale
 lw-complex-polynomial lw-complex-coefficient-at lw-rational-power lw-geometric-disk-gain
 lw-resolvent-truncation-count)))
(local (defthm lw-nis-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nis-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nis-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nis-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nis-times-negative (a b) (b a)))
                 :in-theory (disable lw-nis-times-negative)))))

(local (defthm lw-nis-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nis-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nis-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nis-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nis-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nis-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nis-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nis-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nis-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nis-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nis-left-commutes)))))
(local (defthm lw-nis-zero-power
 (equal (lw-rational-power base 0) 1)
 :hints (("Goal" :expand ((lw-rational-power base 0)) :in-theory (union-theories
 '( lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(defthm lw-euler-normalized-inner-point-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner))
 (and (lw-complexp point) (lw-complex-diskp point 1) (lw-complex-diskp (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point) (lw-euler-local-normalized-radius rate height outer-radius anchor-error))
      (lw-complexp (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)) (rationalp (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (< 0 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (rationalp (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))
      (lw-euler-value-clearance-check (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (lw-euler-local-normalized-anchor rate height anchor-error))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data
       (:instance lw-complex-disk-data (radius inner))
       (:instance lw-complex-disk-enlarge (radius inner) (cap 1))
       (:instance lw-complex-scale-disk (factor (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (radius 1))
       (:instance lw-complex-operations-rational (left point) (right point) (factor (lw-euler-local-normalized-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-local-normalized-point-data (point (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))
 :in-theory (union-theories
 '(abs lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)
(defthm lw-complex-euler-normalized-inner-prefix-polynomial-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (natp count) (natp target) (lw-complex-diskp point inner)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error) (lw-complex-polynomial (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) point 0))
   (+ (* (* 1/2 (+ coefficient-error polynomial-error)) (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)))))
 :hints (("Goal"
  :use (lw-euler-normalized-series-prefix-difference-valid lw-euler-normalized-series-prefix-difference-caps
        lw-euler-local-normalized-data
        (:instance lw-geometric-disk-gain-data (radius inner))
        (:instance lw-complex-disk-data (radius inner))
        (:instance lw-euler-normalized-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-euler-local-normalized-coefficient-polynomial-valid (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count)) (offset 0))
        (:instance lw-polynomial-difference-evaluation (left (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count)) (offset 0))
        (:instance lw-complex-polynomial-geometric-tail-bound
         (coefficients (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error)) (cap (* 1/2 (+ coefficient-error polynomial-error))) (radius inner) (offset 0))
        (:instance lw-euler-local-normalized-polynomial-coefficient-caps (error polynomial-error))
        (:instance lw-complex-polynomial-geometric-prefix-bound
         (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)) (cap (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (radius inner))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-polynomial (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) point 0)) (right (lw-complex-polynomial (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count) point 0)) (radius (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error) point 0))
         (middle (lw-complex-polynomial (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count) point 0)) (right (lw-complex-polynomial (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) point 0))
         (radius (* (* 1/2 (+ coefficient-error polynomial-error)) (lw-geometric-disk-gain inner))) (other-radius (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)))))
  :in-theory (union-theories
   '(lw-euler-normalized-series-prefix-difference lw-complex-euler-normalized-series-prefix lw-nis-zero-power lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


(local (defthm lw-nis-prefix-with-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp inner) (<= 0 inner) (< inner 1) (natp count) (lw-complex-diskp point inner)
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp value-error) (< 0 value-error)
 (lw-euler-value-clearance-check (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (rationalp polynomial-error) (< 0 polynomial-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error) (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error)) (+ (+ (* 1/2 coefficient-error (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/2 value-error)) (* (+ 1/2 (* 1/2 (lw-geometric-disk-gain inner))) polynomial-error))))
 :hints (("Goal"
 :use (lw-euler-normalized-inner-point-data lw-euler-local-normalized-data
       (:instance lw-geometric-disk-gain-data (radius inner))
       (:instance lw-rational-power-rational (base inner) (exponent count))
       (:instance lw-rational-power-nonnegative (base inner) (exponent count))
       (:instance lw-complex-euler-normalized-series-prefix-rational (error coefficient-error))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-euler-local-normalized-polynomial-valid (target 0) (error polynomial-error))
       (:instance lw-euler-local-normalized-coefficient-polynomial-valid (target 0) (error polynomial-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error 0 polynomial-error)) (offset 0))
       (:instance lw-complex-euler-normalized-inner-prefix-polynomial-comparison (target 0))
       (:instance lw-complex-euler-local-normalized-comparison (target 0) (point (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)) (error polynomial-error))
       (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error 0 polynomial-error)) (factor (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (offset 0))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error)) (middle (lw-complex-polynomial (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error 0 polynomial-error) point 0)) (right (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error))
        (radius (+ (* 1/2 (+ coefficient-error polynomial-error) (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count))))
        (other-radius (* 1/2 (+ polynomial-error value-error)))))
 :in-theory (union-theories
 '(lw-euler-local-normalized-coefficient-polynomial lw-nis-zero-power lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-normalized-inner-prefix-agreement
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp inner) (<= 0 inner) (< inner 1) (natp count) (lw-complex-diskp point inner)
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp value-error) (< 0 value-error)
 (lw-euler-value-clearance-check (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error) (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error)) (+ (* 1/2 coefficient-error (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/2 value-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error) (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error)) (+ (* 1/2 coefficient-error (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/2 value-error))))
 :use (lw-euler-normalized-inner-point-data lw-euler-local-normalized-data
       (:instance lw-geometric-disk-gain-data (radius inner))
       (:instance lw-rational-power-rational (base inner) (exponent count))
       (:instance lw-rational-power-nonnegative (base inner) (exponent count))
       (:instance lw-complex-euler-normalized-series-prefix-rational (error coefficient-error))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-operations-rational (left (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error)) (right (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error) (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error))) (radius (+ (* 1/2 coefficient-error (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/2 value-error))) (cost (+ 1/2 (* 1/2 (lw-geometric-disk-gain inner)))))
       (:instance lw-nis-prefix-with-margin (polynomial-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error) (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error)) (+ (* 1/2 coefficient-error (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/2 value-error)) (+ 1/2 (* 1/2 (lw-geometric-disk-gain inner)))))))
 :in-theory (union-theories
 '( lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t)))

(defun lw-euler-normalized-inner-series-count (rate height outer-radius anchor-error inner error)
 (lw-resolvent-truncation-count inner (* 1/4 error (/ (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))))

(defun lw-euler-normalized-inner-series-coefficient-error (inner error)
 (min 1 (* 1/4 error (- 1 inner))))

(defun lw-complex-euler-normalized-inner-series-value (rate height outer-radius anchor-error inner point error)
 (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error) point (lw-euler-normalized-inner-series-coefficient-error inner error)))

(local (in-theory (disable lw-euler-normalized-inner-series-count lw-euler-normalized-inner-series-coefficient-error lw-complex-euler-normalized-inner-series-value)))

(local (defthm lw-nis-reciprocal-positive
 (implies (and (rationalp x) (< 0 x)) (and (rationalp (/ x)) (< 0 (/ x))))
 :hints (("Goal" :use ((:instance inverse-of-* (x x))) :nonlinearp t))
 :rule-classes nil))

(defthm lw-euler-normalized-inner-series-constructor-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (rationalp error) (< 0 error))
  (and (natp (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)) (< 0 (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error))
       (rationalp (lw-euler-normalized-inner-series-coefficient-error inner error)) (< 0 (lw-euler-normalized-inner-series-coefficient-error inner error)) (<= (lw-euler-normalized-inner-series-coefficient-error inner error) 1)
       (<= (* (lw-euler-normalized-inner-series-coefficient-error inner error) (lw-geometric-disk-gain inner)) (/ error 4))
       (<= (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error))) (/ error 4))))
 :hints (("Goal"
  :use (lw-euler-local-normalized-data
        (:instance lw-geometric-disk-gain-data (radius inner))
        (:instance lw-nis-reciprocal-positive (x (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
        (:instance lw-nis-positive-product (a (* 1/4 error)) (b (- 1 inner)))
        (:instance lw-nis-positive-product (a (* 1/4 error)) (b (/ (lw-euler-local-normalized-cap rate height outer-radius anchor-error))))
        (:instance lw-resolvent-truncation-count-natural (radius inner) (error (* 1/4 error (/ (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))))
        (:instance lw-rational-power-rational (base inner) (exponent (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)))
        (:instance lw-resolvent-truncation-count-adequate (radius inner) (error (* 1/4 error (/ (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))) (count (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)))
        (:instance lw-nis-multiply-order (a (lw-euler-normalized-inner-series-coefficient-error inner error)) (b (* 1/4 error (- 1 inner))) (factor (lw-geometric-disk-gain inner)))
        (:instance lw-nis-multiply-order (a (* (lw-geometric-disk-gain inner) (lw-rational-power inner (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)))) (b (* 1/4 error (/ (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))) (factor (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
        (:instance lw-nis-inverse-factor (divisor (- 1 inner)) (coefficient error))
        (:instance lw-nis-inverse-factor (divisor (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (coefficient error)))
  :in-theory (union-theories
   '(lw-euler-normalized-inner-series-count lw-euler-normalized-inner-series-coefficient-error lw-geometric-disk-gain min lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-normalized-inner-series-value-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (lw-complexp point) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error)))
 :hints (("Goal"
  :use (lw-euler-normalized-inner-series-constructor-data
        (:instance lw-complex-euler-normalized-series-prefix-rational (count (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)) (error (lw-euler-normalized-inner-series-coefficient-error inner error))))
  :in-theory (union-theories
   '(lw-complex-euler-normalized-inner-series-value lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-normalized-inner-series-value-bound
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner))))
 :hints (("Goal"
  :use (lw-euler-normalized-inner-series-constructor-data lw-euler-local-normalized-data
        (:instance lw-geometric-disk-gain-data (radius inner))
        (:instance lw-euler-normalized-series-coefficients-valid (start 0) (count (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)) (error (lw-euler-normalized-inner-series-coefficient-error inner error)))
        (:instance lw-euler-normalized-series-coefficients-caps (start 0) (count (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)) (error (lw-euler-normalized-inner-series-coefficient-error inner error)))
        (:instance lw-complex-polynomial-geometric-tail-bound
         (coefficients (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error) (lw-euler-normalized-inner-series-coefficient-error inner error))) (cap (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (radius inner) (offset 0)))
  :in-theory (union-theories
   '(lw-complex-euler-normalized-inner-series-value lw-complex-euler-normalized-series-prefix lw-nis-zero-power lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


(defthm lw-complex-euler-normalized-inner-series-value-agreement
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner)
 (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error)
 (lw-euler-value-clearance-check (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use (lw-euler-normalized-inner-series-constructor-data
       (:instance lw-complex-euler-normalized-inner-prefix-agreement (count (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error)) (coefficient-error (lw-euler-normalized-inner-series-coefficient-error inner error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error inner point error) (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) coefficient-radius local-anchor value-error)))
        (radius (+ (* 1/2 (lw-euler-normalized-inner-series-coefficient-error inner error) (lw-geometric-disk-gain inner)) (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-geometric-disk-gain inner) (lw-rational-power inner (lw-euler-normalized-inner-series-count rate height outer-radius anchor-error inner error))) (* 1/2 value-error)))
        (cap (* 1/2 (+ error value-error)))))
 :in-theory (union-theories
 '(lw-complex-euler-normalized-inner-series-value lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(local (defthm lw-nis-series-cauchy-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp left-inner) (<= 0 left-inner) (< left-inner 1) (rationalp right-inner) (<= 0 right-inner) (< right-inner 1)
 (lw-complex-diskp point left-inner) (lw-complex-diskp point right-inner)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error left-inner point left-error) (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error)) (+ (* 1/2 (+ left-error right-error)) margin)))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data
       (:instance lw-euler-normalized-inner-point-data (inner left-inner))
       (:instance lw-euler-normalized-inner-point-data (inner right-inner))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (inner left-inner) (error left-error))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (inner right-inner) (error right-error))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (height (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))
        (radius (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (anchor-error (lw-euler-local-normalized-anchor rate height anchor-error)) (error margin))
       (:instance lw-complex-euler-normalized-inner-series-value-agreement (inner left-inner) (error left-error)
        (local-anchor (lw-euler-local-normalized-anchor rate height anchor-error)) (coefficient-radius (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (value-error margin))
       (:instance lw-complex-euler-normalized-inner-series-value-agreement (inner right-inner) (error right-error)
        (local-anchor (lw-euler-local-normalized-anchor rate height anchor-error)) (coefficient-radius (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))))) (value-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error)) (right (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (lw-euler-local-normalized-anchor rate height anchor-error) margin)) (radius (* 1/2 (+ right-error margin))))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error left-inner point left-error)) (middle (lw-mellin-euler-log-extended-value (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (+ height (cdr (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point))) (* 1/2 (+ rate (car (lw-complex-scale (lw-euler-local-normalized-radius rate height outer-radius anchor-error) point)))) (lw-euler-local-normalized-anchor rate height anchor-error) margin)) (right (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error))
        (radius (* 1/2 (+ left-error margin))) (other-radius (* 1/2 (+ right-error margin)))))
 :in-theory (union-theories
 '(lw-complexp lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-normalized-inner-series-value-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp left-inner) (<= 0 left-inner) (< left-inner 1) (rationalp right-inner) (<= 0 right-inner) (< right-inner 1)
 (lw-complex-diskp point left-inner) (lw-complex-diskp point right-inner)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error left-inner point left-error) (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error left-inner point left-error) (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error)) (* 1/2 (+ left-error right-error))))
 :use ((:instance lw-euler-normalized-inner-point-data (inner left-inner))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (inner left-inner) (error left-error))
       (:instance lw-complex-euler-normalized-inner-series-value-rational (inner right-inner) (error right-error))
       (:instance lw-complex-operations-rational (left (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error left-inner point left-error)) (right (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error left-inner point left-error) (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error))) (radius (* 1/2 (+ left-error right-error))) (cost 1))
       (:instance lw-nis-series-cauchy-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error left-inner point left-error) (lw-complex-euler-normalized-inner-series-value rate height outer-radius anchor-error right-inner point right-error)) (* 1/2 (+ left-error right-error)) 1))))
 :in-theory (union-theories
 '( lw-nis-left-commutes lw-nis-left-distributes lw-nis-fold-constants lw-nis-times-negative lw-nis-negative-times lw-nis-zero-times lw-nis-minus-one lw-nis-double-negative lw-nis-add-cancel lw-nis-double lw-nis-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


