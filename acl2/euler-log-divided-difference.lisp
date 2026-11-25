; Stable physical divided differences for the actual uniform quotient models.
; Polynomial construction includes the center, where division by the point is absent.
(in-package "ACL2")
(include-book "euler-log-coefficient-caps")
(include-book "polynomial-tail-stability")
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
 lw-euler-uniform-log-polynomial lw-euler-uniform-log-cap lw-euler-log-coefficient-polynomial
 lw-euler-log-difference-count lw-euler-log-difference-polynomial lw-polynomial-disk-difference
 lw-polynomial-pad lw-polynomial-rescale lw-polynomial-multiply-coefficients lw-complex-polynomial)))
(local (defthm lw-ldd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ldd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ldd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ldd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ldd-times-negative (a b) (b a)))
                 :in-theory (disable lw-ldd-times-negative)))))

(local (defthm lw-ldd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ldd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ldd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ldd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ldd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ldd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ldd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ldd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ldd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ldd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ldd-left-commutes)))))

(local (defthm lw-ldd-real-multiple
 (implies (and (rationalp factor) (lw-complexp value))
 (equal (lw-complex-mul (cons factor 0) value) (lw-complex-scale factor value)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-mul lw-complex-scale lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ldd-move-scale
 (implies (and (rationalp factor) (lw-complexp left) (lw-complexp right))
 (equal (lw-complex-mul left (lw-complex-scale factor right))
        (lw-complex-mul (lw-complex-scale factor left) right)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-mul lw-complex-scale lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ldd-rescale-point
 (implies (and (rationalp radius) (< 0 radius) (lw-complexp point))
 (equal (lw-complex-scale radius (lw-complex-scale (/ radius) point)) point))
 :hints (("Goal" :use ((:instance lw-ldd-inverse-factor (divisor radius) (coefficient 1)))
 :in-theory (union-theories
 '(lw-complex-scale-compose lw-complex-scale-one lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(local (defthm lw-ldd-half-point
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (* 1/2 (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
 (and (lw-complexp point) (lw-complexp (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (lw-complex-diskp (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point) 1/2)))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data
       (:instance lw-complex-disk-data (radius (* 1/2 (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
       (:instance lw-reciprocal-positive (value (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-ldd-inverse-factor (divisor (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (coefficient 1/2))
       (:instance lw-complex-scale-disk (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (radius (* 1/2 (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (radius (* (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (* 1/2 (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))) (cap 1/2))
       (:instance lw-complex-disk-data (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (radius 1/2)))
 :in-theory (union-theories
 '(abs lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-log-divided-polynomial (rate height outer-radius anchor-error target error)
 (lw-polynomial-multiply-coefficients (cons (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) 0)
  (lw-polynomial-rescale (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) 0)))

(local (in-theory (disable lw-euler-log-divided-polynomial)))

(defthm lw-euler-log-divided-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-log-divided-polynomial rate height outer-radius anchor-error target error)))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-log-coefficient-polynomial-valid lw-euler-log-polynomial-coefficient-caps
       (:instance lw-polynomial-tail-data (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-polynomial-rescale-valid (coefficients (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error))) (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (offset 0))
       (:instance lw-polynomial-multiply-coefficients-valid
        (coefficients (lw-polynomial-rescale (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) 0)) (factor (cons (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) 0))))
 :in-theory (union-theories
 '(lw-euler-log-divided-polynomial lw-complexp lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-log-divided-polynomial-evaluation
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complexp point))
 (equal (lw-complex-polynomial (lw-euler-log-divided-polynomial rate height outer-radius anchor-error target error) point 0) (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (lw-complex-polynomial (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point) 0))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-log-coefficient-polynomial-valid lw-euler-log-polynomial-coefficient-caps
       (:instance lw-polynomial-tail-data (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-complex-scale-rational (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
       (:instance lw-polynomial-rescale-valid (coefficients (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error))) (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (offset 0))
       (:instance lw-polynomial-rescale-evaluation (coefficients (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error))) (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error))) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (offset 0))
       (:instance lw-polynomial-multiply-coefficients-evaluation
        (coefficients (lw-polynomial-rescale (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) 0)) (factor (cons (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) 0)) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-log-divided-polynomial lw-ldd-real-multiple lw-complexp lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-log-divided-polynomial-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (* 1/2 (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-log-divided-polynomial rate height outer-radius anchor-error target error) point 0) (* 2 (lw-euler-uniform-log-cap rate height outer-radius anchor-error) (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-ldd-half-point lw-euler-uniform-log-model-data
       lw-euler-log-coefficient-polynomial-valid lw-euler-log-polynomial-coefficient-caps
       lw-euler-log-divided-polynomial-evaluation
       (:instance lw-reciprocal-positive (value (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-polynomial-tail-half-bound (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-complex-scale-disk (point (lw-complex-polynomial (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point) 0)) (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (radius (* 2 (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))))
 :in-theory (union-theories
 '(abs lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-log-divided-polynomial-identity
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complexp point))
 (equal (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) (cons 0 0) 0))
        (lw-complex-mul point (lw-complex-polynomial (lw-euler-log-divided-polynomial rate height outer-radius anchor-error target error) point 0))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-uniform-log-polynomial-valid
       lw-euler-log-coefficient-polynomial-valid lw-euler-log-polynomial-coefficient-caps
       lw-euler-log-divided-polynomial-evaluation
       (:instance lw-polynomial-tail-data (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-complex-scale-rational (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
       (:instance lw-complex-polynomial-rational (coefficients (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error))) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (offset 0))
       (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)) (factor (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (offset 0) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)))
       (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)) (factor (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (offset 0) (point (cons 0 0)))
       (:instance lw-complex-polynomial-first-tail-identity (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error target error)) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)))
       (:instance lw-ldd-rescale-point (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-euler-log-coefficient-polynomial lw-ldd-move-scale lw-complex-scale-zero (:executable-counterpart lw-complexp) lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-log-divided-polynomial-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (lw-complex-diskp point (* 1/2 (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-polynomial (lw-euler-log-divided-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-euler-log-divided-polynomial rate height outer-radius anchor-error right-target right-error) point 0))
  (* 2 (+ left-error right-error) (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-ldd-half-point
       lw-euler-log-difference-polynomial-data lw-euler-log-polynomial-difference-coefficient-caps
       (:instance lw-euler-log-coefficient-polynomial-valid (target left-target) (error left-error))
       (:instance lw-euler-log-coefficient-polynomial-valid (target right-target) (error right-error))
       (:instance lw-euler-log-polynomial-coefficient-caps (target left-target) (error left-error))
       (:instance lw-euler-log-polynomial-coefficient-caps (target right-target) (error right-error))
       (:instance lw-polynomial-tail-data (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error left-target left-error)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-polynomial-tail-data (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error right-target right-error)) (cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-complex-polynomial-rational (coefficients (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error left-target left-error))) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error right-target right-error))) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)) (offset 0))
       (:instance lw-euler-log-divided-polynomial-evaluation (target left-target) (error left-error))
       (:instance lw-euler-log-divided-polynomial-evaluation (target right-target) (error right-error))
       (:instance lw-polynomial-pad-valid (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error left-target left-error)) (count (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)))
       (:instance lw-polynomial-pad-valid (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error right-target right-error)) (count (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)))
       (:instance lw-polynomial-pad-tail-evaluation (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error left-target left-error)) (count (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)))
       (:instance lw-polynomial-pad-tail-evaluation (coefficients (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error right-target right-error)) (count (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)))
       (:instance lw-complex-polynomial-tail-difference-half-bound
        (left (lw-polynomial-pad (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error left-target left-error) (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error))) (right (lw-polynomial-pad (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error right-target right-error) (lw-euler-log-difference-count rate height outer-radius anchor-error left-target right-target left-error right-error)))
        (cap (+ left-error right-error)) (point (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point)))
       (:instance lw-reciprocal-positive (value (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-scale-disk (point (lw-complex-sub (lw-complex-polynomial (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error left-target left-error)) (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point) 0) (lw-complex-polynomial (cdr (lw-euler-log-coefficient-polynomial rate height outer-radius anchor-error right-target right-error)) (lw-complex-scale (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) point) 0)))
        (factor (/ (lw-euler-neighborhood-radius rate height outer-radius anchor-error))) (radius (* 2 (+ left-error right-error)))))
 :in-theory (union-theories
 '(lw-euler-log-divided-polynomial-evaluation lw-euler-log-coefficient-polynomial lw-euler-log-difference-polynomial lw-polynomial-disk-difference lw-complex-sub-scales abs lw-ldd-left-commutes lw-ldd-left-distributes lw-ldd-fold-constants lw-ldd-times-negative lw-ldd-negative-times lw-ldd-zero-times lw-ldd-minus-one lw-ldd-double-negative lw-ldd-add-cancel lw-ldd-double lw-ldd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

