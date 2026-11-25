(in-package "ACL2")

(include-book "euler-local-series")
(include-book "polynomial-geometric-bounds")

; Canonical Euler series on arbitrary strict inner disks.
; Cutoffs and coefficient requests are uniform over the chosen disk.

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

(local (in-theory (disable lw-euler-coefficient-polynomial lw-euler-uniform-coefficient-cap
 lw-complex-euler-continuation-value lw-complex-euler-series-prefix lw-euler-series-coefficients
 lw-euler-series-prefix-difference lw-polynomial-pad lw-polynomial-difference
 lw-complex-polynomial lw-complex-coefficient-at lw-rational-power lw-geometric-disk-gain
 lw-resolvent-truncation-count)))

(local (defthm lw-eis-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eis-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eis-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eis-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eis-times-negative (a b) (b a)))
                 :in-theory (disable lw-eis-times-negative)))))

(local (defthm lw-eis-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eis-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eis-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eis-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eis-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eis-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eis-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eis-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eis-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eis-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eis-left-commutes)))))

(local (defthm lw-eis-zero-power
 (equal (lw-rational-power base 0) 1)
 :hints (("Goal" :expand ((lw-rational-power base 0)) :in-theory (union-theories
   '( lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-eis-point-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner))
  (and (lw-complexp point) (lw-complex-diskp point 1) (lw-complex-diskp (lw-complex-scale radius point) radius)
       (rationalp (+ rate (car (lw-complex-scale radius point)))) (< 0 (+ rate (car (lw-complex-scale radius point))))
       (rationalp (+ height (cdr (lw-complex-scale radius point))))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (radius inner))
        (:instance lw-complex-disk-enlarge (radius inner) (cap 1))
        (:instance lw-complex-scale-disk (factor radius) (radius 1))
        (:instance lw-euler-disk-point-data (offset (lw-complex-scale radius point))))
  :in-theory (union-theories
   '(abs lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-inner-prefix-polynomial-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (natp count) (natp target) (lw-complex-diskp point inner)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target polynomial-error) point 0))
   (+ (* (+ coefficient-error polynomial-error) (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)))))
 :hints (("Goal"
  :use (lw-euler-series-prefix-difference-valid lw-euler-series-prefix-difference-caps
        lw-euler-uniform-coefficient-cap-valid
        (:instance lw-geometric-disk-gain-data (radius inner))
        (:instance lw-complex-disk-data (radius inner))
        (:instance lw-euler-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-euler-polynomial-coefficient-rational (index 0) (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-series-coefficients rate height radius 0 count coefficient-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count)) (offset 0))
        (:instance lw-polynomial-difference-evaluation (left (lw-euler-series-coefficients rate height radius 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count)) (offset 0))
        (:instance lw-complex-polynomial-geometric-tail-bound
         (coefficients (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error)) (cap (+ coefficient-error polynomial-error)) (radius inner) (offset 0))
        (:instance lw-euler-polynomial-coefficient-caps (error polynomial-error))
        (:instance lw-complex-polynomial-geometric-prefix-bound
         (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)) (cap (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error)) (radius inner))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target polynomial-error) point 0)) (right (lw-complex-polynomial (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count) point 0)) (radius (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-series-coefficients rate height radius 0 count coefficient-error) point 0))
         (middle (lw-complex-polynomial (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count) point 0)) (right (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target polynomial-error) point 0))
         (radius (* (+ coefficient-error polynomial-error) (lw-geometric-disk-gain inner))) (other-radius (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)))))
  :in-theory (union-theories
   '(lw-euler-series-prefix-difference lw-complex-euler-series-prefix lw-eis-zero-power lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-inner-prefix-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (natp count) (lw-complex-diskp point inner)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp value-error) (< 0 value-error)
               (rationalp polynomial-error) (< 0 polynomial-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (+ (* coefficient-error (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/4 value-error)) (* (+ 1 (lw-geometric-disk-gain inner) (* (lw-geometric-disk-gain inner) (lw-rational-power inner count))) polynomial-error))))
 :hints (("Goal"
  :use (lw-eis-point-data
        (:instance lw-complex-euler-series-prefix-rational (error coefficient-error))
        (:instance lw-euler-polynomial-coefficient-rational (target 0) (index 0) (error polynomial-error))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius 0 polynomial-error)) (offset 0))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error value-error))
        (:instance lw-complex-euler-inner-prefix-polynomial-comparison (target 0))
        (:instance lw-complex-euler-normalized-polynomial-comparison (target 0) (error polynomial-error))
        (:instance lw-complex-difference-triangle (left (lw-complex-euler-series-prefix rate height radius count point coefficient-error))
         (middle (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 polynomial-error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error))
         (radius (+ (* (+ coefficient-error polynomial-error) (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-geometric-disk-gain inner) (lw-rational-power inner count)))) (other-radius (+ polynomial-error (* 1/4 value-error)))))
  :in-theory (union-theories
   '( lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-inner-prefix-agreement
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (natp count) (lw-complex-diskp point inner)
               (rationalp coefficient-error) (< 0 coefficient-error) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (* coefficient-error (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/4 value-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (* coefficient-error (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/4 value-error))))
  :use (lw-eis-point-data lw-euler-uniform-coefficient-cap-valid
        (:instance lw-geometric-disk-gain-data (radius inner))
        (:instance lw-rational-power-rational (base inner) (exponent count))
        (:instance lw-rational-power-nonnegative (base inner) (exponent count))
        (:instance lw-complex-euler-series-prefix-rational (error coefficient-error))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error value-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-series-prefix rate height radius count point coefficient-error)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error))) (radius (+ (* coefficient-error (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/4 value-error))) (cost (+ 1 (lw-geometric-disk-gain inner) (* (lw-geometric-disk-gain inner) (lw-rational-power inner count)))))
        (:instance lw-complex-euler-inner-prefix-with-margin
         (polynomial-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (* coefficient-error (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-geometric-disk-gain inner) (lw-rational-power inner count)) (* 1/4 value-error)) (+ 1 (lw-geometric-disk-gain inner) (* (lw-geometric-disk-gain inner) (lw-rational-power inner count)))))))
  :in-theory (union-theories
   '( lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defun lw-euler-inner-series-count (rate height radius inner error)
 (lw-resolvent-truncation-count inner (* 1/4 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))))

(defun lw-euler-inner-series-coefficient-error (inner error)
 (min 1 (* 1/4 error (- 1 inner))))

(defun lw-complex-euler-inner-series-value (rate height radius inner point error)
 (lw-complex-euler-series-prefix rate height radius (lw-euler-inner-series-count rate height radius inner error) point (lw-euler-inner-series-coefficient-error inner error)))

(local (in-theory (disable lw-euler-inner-series-count lw-euler-inner-series-coefficient-error
 lw-complex-euler-inner-series-value)))

(local (defthm lw-eis-reciprocal-positive
 (implies (and (rationalp x) (< 0 x)) (and (rationalp (/ x)) (< 0 (/ x))))
 :hints (("Goal" :use ((:instance inverse-of-* (x x))) :nonlinearp t))
 :rule-classes nil))

(defthm lw-euler-inner-series-constructor-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (rationalp error) (< 0 error))
  (and (natp (lw-euler-inner-series-count rate height radius inner error)) (< 0 (lw-euler-inner-series-count rate height radius inner error))
       (rationalp (lw-euler-inner-series-coefficient-error inner error)) (< 0 (lw-euler-inner-series-coefficient-error inner error)) (<= (lw-euler-inner-series-coefficient-error inner error) 1)
       (<= (* (lw-euler-inner-series-coefficient-error inner error) (lw-geometric-disk-gain inner)) (/ error 4))
       (<= (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-geometric-disk-gain inner) (lw-rational-power inner (lw-euler-inner-series-count rate height radius inner error))) (/ error 4))))
 :hints (("Goal"
  :use (lw-euler-uniform-coefficient-cap-valid
        (:instance lw-geometric-disk-gain-data (radius inner))
        (:instance lw-eis-reciprocal-positive (x (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))
        (:instance lw-eis-positive-product (a (* 1/4 error)) (b (- 1 inner)))
        (:instance lw-eis-positive-product (a (* 1/4 error)) (b (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)))))
        (:instance lw-resolvent-truncation-count-natural (radius inner) (error (* 1/4 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))))
        (:instance lw-rational-power-rational (base inner) (exponent (lw-euler-inner-series-count rate height radius inner error)))
        (:instance lw-resolvent-truncation-count-adequate (radius inner) (error (* 1/4 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))) (count (lw-euler-inner-series-count rate height radius inner error)))
        (:instance lw-eis-multiply-order (a (lw-euler-inner-series-coefficient-error inner error)) (b (* 1/4 error (- 1 inner))) (factor (lw-geometric-disk-gain inner)))
        (:instance lw-eis-multiply-order (a (* (lw-geometric-disk-gain inner) (lw-rational-power inner (lw-euler-inner-series-count rate height radius inner error)))) (b (* 1/4 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))) (factor (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))
        (:instance lw-eis-inverse-factor (divisor (- 1 inner)) (coefficient error))
        (:instance lw-eis-inverse-factor (divisor (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))) (coefficient error)))
  :in-theory (union-theories
   '(lw-euler-inner-series-count lw-euler-inner-series-coefficient-error lw-geometric-disk-gain min lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-inner-series-value-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (lw-complexp point) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-inner-series-value rate height radius inner point error)))
 :hints (("Goal"
  :use (lw-euler-inner-series-constructor-data
        (:instance lw-complex-euler-series-prefix-rational (count (lw-euler-inner-series-count rate height radius inner error)) (error (lw-euler-inner-series-coefficient-error inner error))))
  :in-theory (union-theories
   '(lw-complex-euler-inner-series-value lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-inner-series-value-agreement
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner)
               (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (/ error 2) (* 1/4 value-error))))
 :hints (("Goal"
  :use (lw-euler-inner-series-constructor-data
        (:instance lw-complex-euler-inner-prefix-agreement (count (lw-euler-inner-series-count rate height radius inner error)) (coefficient-error (lw-euler-inner-series-coefficient-error inner error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)))
         (radius (+ (* (lw-euler-inner-series-coefficient-error inner error) (lw-geometric-disk-gain inner)) (* (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-geometric-disk-gain inner) (lw-rational-power inner (lw-euler-inner-series-count rate height radius inner error))) (* 1/4 value-error)))
         (cap (+ (/ error 2) (* 1/4 value-error)))))
  :in-theory (union-theories
   '(lw-complex-euler-inner-series-value lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-inner-series-value-cauchy
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error))))
  :use (lw-eis-point-data
        (:instance lw-complex-euler-inner-series-value-rational (error left-error))
        (:instance lw-complex-euler-inner-series-value-rational (error right-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-inner-series-value rate height radius inner point left-error)) (right (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error))) (radius (* 1/2 (+ left-error right-error))) (cost 1))
        (:instance lw-complex-euler-inner-series-value-agreement (error left-error) (value-error (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1))))
        (:instance lw-complex-euler-inner-series-value-agreement (error right-error) (value-error (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1))))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1))))
        (:instance lw-complex-difference-symmetric (left (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1))))
         (radius (+ (* 1/2 right-error) (* 1/2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1)))))
        (:instance lw-complex-difference-triangle (left (lw-complex-euler-inner-series-value rate height radius inner point left-error)) (middle (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1)))) (right (lw-complex-euler-inner-series-value rate height radius inner point right-error))
         (radius (+ (* 1/2 left-error) (* 1/2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1)))) (other-radius (+ (* 1/2 right-error) (* 1/2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-inner-series-value rate height radius inner point left-error) (lw-complex-euler-inner-series-value rate height radius inner point right-error)) (* 1/2 (+ left-error right-error)) 1))))))
  :in-theory (union-theories
   '( lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-inner-series-value-bound
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp inner) (<= 0 inner) (< inner 1) (lw-complex-diskp point inner) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-euler-inner-series-value rate height radius inner point error) (* (lw-euler-uniform-coefficient-cap rate height radius) (lw-geometric-disk-gain inner))))
 :hints (("Goal"
  :use (lw-euler-inner-series-constructor-data lw-euler-uniform-coefficient-cap-valid
        (:instance lw-geometric-disk-gain-data (radius inner))
        (:instance lw-euler-series-coefficients-valid (start 0) (count (lw-euler-inner-series-count rate height radius inner error)) (error (lw-euler-inner-series-coefficient-error inner error)))
        (:instance lw-euler-series-coefficients-caps (start 0) (count (lw-euler-inner-series-count rate height radius inner error)) (error (lw-euler-inner-series-coefficient-error inner error)))
        (:instance lw-complex-polynomial-geometric-tail-bound
         (coefficients (lw-euler-series-coefficients rate height radius 0 (lw-euler-inner-series-count rate height radius inner error) (lw-euler-inner-series-coefficient-error inner error))) (cap (lw-euler-uniform-coefficient-cap rate height radius)) (radius inner) (offset 0)))
  :in-theory (union-theories
   '(lw-complex-euler-inner-series-value lw-complex-euler-series-prefix lw-eis-zero-power lw-eis-left-commutes lw-eis-left-distributes lw-eis-fold-constants lw-eis-times-negative lw-eis-negative-times lw-eis-zero-times lw-eis-minus-one lw-eis-double-negative lw-eis-add-cancel lw-eis-double lw-eis-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


