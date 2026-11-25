; Uniform inverse polynomials for the actual Euler family on computed disks.
(in-package "ACL2")
(include-book "euler-nonzero-neighborhood")
(include-book "polynomial-inverse")
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
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-value-clearance-size
 lw-euler-value-clearance-lower lw-euler-neighborhood-radius lw-euler-rounding-precision
 lw-polynomial-inverse-residual lw-polynomial-inverse lw-polynomial-inverse-count
 lw-complex-polynomial)))
(local (defthm lw-eui-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eui-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eui-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eui-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eui-times-negative (a b) (b a)))
                 :in-theory (disable lw-eui-times-negative)))))

(local (defthm lw-eui-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eui-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eui-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eui-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eui-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eui-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eui-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eui-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eui-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eui-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eui-left-commutes)))))

(defun lw-euler-neighborhood-anchor-inverse-cap (rate height anchor-error)
 (/ (* 1/2 (lw-euler-value-clearance-size rate height anchor-error))))

(defun lw-euler-neighborhood-inverse-gain (rate height anchor-error)
 (* (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))
    (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))))

(local (in-theory (disable lw-euler-neighborhood-anchor-inverse-cap lw-euler-neighborhood-inverse-gain)))

(defthm lw-euler-neighborhood-inverse-data
 (implies (lw-euler-value-clearance-check rate height anchor-error)
 (and (rationalp (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)) (< 0 (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-euler-continuation-value rate height anchor-error)) (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error))
      (equal (* (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error) (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))) 1/2)
      (rationalp (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))) (< 0 (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))
      (rationalp (lw-euler-neighborhood-inverse-gain rate height anchor-error)) (< 0 (lw-euler-neighborhood-inverse-gain rate height anchor-error))))
 :hints (("Goal"
 :use (lw-euler-value-clearance-data
       (:instance lw-complex-l1-clearance (point (lw-complex-euler-continuation-value rate height anchor-error)))
       (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-euler-continuation-value rate height anchor-error)) (lower (* 1/2 (lw-euler-value-clearance-size rate height anchor-error))))
       (:instance lw-reciprocal-positive (value (* 1/2 (lw-euler-value-clearance-size rate height anchor-error))))
       (:instance lw-reciprocal-positive (value (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))))
       (:instance lw-eui-positive-product (a (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))) (b (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))))
       (:instance lw-eui-inverse-factor (divisor (* 1/2 (lw-euler-value-clearance-size rate height anchor-error))) (coefficient 1/2)))
 :in-theory (union-theories
 '(lw-euler-neighborhood-anchor-inverse-cap lw-euler-neighborhood-inverse-gain lw-euler-value-clearance-size lw-eui-left-commutes lw-eui-left-distributes lw-eui-fold-constants lw-eui-times-negative lw-eui-negative-times lw-eui-zero-times lw-eui-minus-one lw-eui-double-negative lw-eui-add-cancel lw-eui-double lw-eui-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(local (defthm lw-eui-residual-factor
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))) (lw-complexp value))
 (equal (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value))
        (lw-complex-mul (lw-complex-reciprocal anchor) (lw-complex-sub anchor value))))
 :hints (("Goal"
 :use ((:instance lw-complex-reciprocal-inverse (point anchor)))
 :in-theory (union-theories
 '(lw-complex-mul-subtract lw-complex-reciprocal-rational (:executable-counterpart lw-complexp) lw-eui-left-commutes lw-eui-left-distributes lw-eui-fold-constants lw-eui-times-negative lw-eui-negative-times lw-eui-zero-times lw-eui-minus-one lw-eui-double-negative lw-eui-add-cancel lw-eui-double lw-eui-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(defthm lw-complex-euler-neighborhood-inverse-residual
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (natp target) (rationalp error) (< 0 error) (<= error anchor-error))
 (lw-complex-diskp
  (lw-complex-polynomial (lw-polynomial-inverse-residual (lw-euler-uniform-polynomial rate height outer-radius target error) (lw-complex-euler-continuation-value rate height anchor-error)) point 0) 1/2))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-neighborhood-inverse-data
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       lw-complex-euler-neighborhood-polynomial-anchor
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error)) (offset 0))
       (:instance lw-polynomial-inverse-residual-evaluation (coefficients (lw-euler-uniform-polynomial rate height outer-radius target error)) (anchor (lw-complex-euler-continuation-value rate height anchor-error)))
       (:instance lw-eui-residual-factor (anchor (lw-complex-euler-continuation-value rate height anchor-error)) (value (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0)))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0)) (right (lw-complex-euler-continuation-value rate height anchor-error)) (radius (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))))
       (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (lw-complex-euler-continuation-value rate height anchor-error))) (right (lw-complex-sub (lw-complex-euler-continuation-value rate height anchor-error) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target error) point 0)))
        (radius (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)) (other-radius (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))))
 :in-theory (union-theories
 '( lw-eui-left-commutes lw-eui-left-distributes lw-eui-fold-constants lw-eui-times-negative lw-eui-negative-times lw-eui-zero-times lw-eui-minus-one lw-eui-double-negative lw-eui-add-cancel lw-eui-double lw-eui-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-euler-uniform-inverse-request (rate height anchor-error error)
 (min anchor-error (lw-euler-rounding-precision (lw-euler-neighborhood-inverse-gain rate height anchor-error) error)))

(local (in-theory (disable lw-euler-uniform-inverse-request)))

(defthm lw-euler-uniform-inverse-request-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error) (rationalp error) (< 0 error))
 (and (rationalp (lw-euler-uniform-inverse-request rate height anchor-error error)) (< 0 (lw-euler-uniform-inverse-request rate height anchor-error error)) (<= (lw-euler-uniform-inverse-request rate height anchor-error error) anchor-error) (<= (lw-euler-uniform-inverse-request rate height anchor-error error) 1)
      (<= (* (lw-euler-neighborhood-inverse-gain rate height anchor-error) (lw-euler-uniform-inverse-request rate height anchor-error error)) (* 1/2 error))))
 :hints (("Goal"
 :use (lw-euler-value-clearance-data lw-euler-neighborhood-inverse-data
       (:instance lw-euler-rounding-precision-valid (cost (lw-euler-neighborhood-inverse-gain rate height anchor-error)))
       (:instance lw-eui-multiply-order (a (lw-euler-uniform-inverse-request rate height anchor-error error)) (b (lw-euler-rounding-precision (lw-euler-neighborhood-inverse-gain rate height anchor-error) error)) (factor (lw-euler-neighborhood-inverse-gain rate height anchor-error))))
 :in-theory (union-theories
 '(lw-euler-uniform-inverse-request min lw-eui-left-commutes lw-eui-left-distributes lw-eui-fold-constants lw-eui-times-negative lw-eui-negative-times lw-eui-zero-times lw-eui-minus-one lw-eui-double-negative lw-eui-add-cancel lw-eui-double lw-eui-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-euler-uniform-inverse-polynomial
 (rate height outer-radius anchor-error target error)
 (lw-polynomial-inverse (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error)) (lw-complex-euler-continuation-value rate height anchor-error) (lw-polynomial-inverse-count (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error) (* 1/2 error))))

(local (in-theory (disable lw-euler-uniform-inverse-polynomial lw-euler-uniform-inverse-request)))

(defthm lw-euler-uniform-inverse-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target error)))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-uniform-inverse-request-data
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (error (lw-euler-uniform-inverse-request rate height anchor-error error)))
       (:instance lw-polynomial-inverse-valid (coefficients (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error))) (anchor (lw-complex-euler-continuation-value rate height anchor-error)) (count (lw-polynomial-inverse-count (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error) (* 1/2 error)))))
 :in-theory (union-theories
 '(lw-euler-uniform-inverse-polynomial lw-eui-left-commutes lw-eui-left-distributes lw-eui-fold-constants lw-eui-times-negative lw-eui-negative-times lw-eui-zero-times lw-eui-minus-one lw-eui-double-negative lw-eui-add-cancel lw-eui-double lw-eui-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-uniform-inverse-polynomial-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (natp target) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target error) point 0) (* 4 (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-neighborhood-inverse-data lw-euler-uniform-inverse-request-data
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (error (lw-euler-uniform-inverse-request rate height anchor-error error)))
       (:instance lw-complex-euler-neighborhood-inverse-residual (error (lw-euler-uniform-inverse-request rate height anchor-error error)))
       (:instance lw-polynomial-inverse-count-natural (anchor-cap (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)) (error (* 1/2 error)))
       (:instance lw-polynomial-inverse-half-cap (coefficients (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error))) (anchor (lw-complex-euler-continuation-value rate height anchor-error)) (count (lw-polynomial-inverse-count (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error) (* 1/2 error))) (anchor-cap (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error))))
 :in-theory (union-theories
 '(lw-euler-uniform-inverse-polynomial lw-eui-left-commutes lw-eui-left-distributes lw-eui-fold-constants lw-eui-times-negative lw-eui-negative-times lw-eui-zero-times lw-eui-minus-one lw-eui-double-negative lw-eui-add-cancel lw-eui-double lw-eui-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-uniform-inverse-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (natp target) (rationalp error) (< 0 error)
  (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-reciprocal (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error)) (lw-complex-polynomial (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target error) point 0))
  (+ error (* 1/4 (lw-euler-neighborhood-inverse-gain rate height anchor-error) value-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-neighborhood-inverse-data lw-euler-uniform-inverse-request-data
       lw-euler-uniform-inverse-polynomial-valid
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-disk-enlarge (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (cap outer-radius))
       (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (error (lw-euler-uniform-inverse-request rate height anchor-error error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error))) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-complex-euler-neighborhood-value-clearance (error value-error))
       (:instance lw-complex-euler-neighborhood-polynomial-clearance (error (lw-euler-uniform-inverse-request rate height anchor-error error)))
       (:instance lw-complex-reciprocal-rational (point (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error)))
       (:instance lw-complex-reciprocal-rational (point (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error)) point 0)))
       (:instance lw-complex-euler-uniform-polynomial-comparison (radius outer-radius) (error (lw-euler-uniform-inverse-request rate height anchor-error error)))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error)) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error)) (radius (+ (lw-euler-uniform-inverse-request rate height anchor-error error) (* 1/4 value-error))))
       (:instance lw-complex-reciprocal-difference-bound
        (a (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error)) (b (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error)) point 0)) (left-clearance (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))) (right-clearance (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))
        (error (+ (lw-euler-uniform-inverse-request rate height anchor-error error) (* 1/4 value-error))))
       (:instance lw-complex-euler-neighborhood-inverse-residual (error (lw-euler-uniform-inverse-request rate height anchor-error error)))
       (:instance lw-polynomial-inverse-count-natural (anchor-cap (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)) (error (* 1/2 error)))
       (:instance lw-polynomial-inverse-computed-error (coefficients (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error))) (anchor (lw-complex-euler-continuation-value rate height anchor-error)) (count (lw-polynomial-inverse-count (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error) (* 1/2 error))) (anchor-cap (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)) (error (* 1/2 error)))
       (:instance lw-complex-difference-triangle (left (lw-complex-reciprocal (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))) (middle (lw-complex-reciprocal (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target (lw-euler-uniform-inverse-request rate height anchor-error error)) point 0))) (right (lw-complex-polynomial (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target error) point 0))
        (radius (* (lw-euler-neighborhood-inverse-gain rate height anchor-error) (+ (lw-euler-uniform-inverse-request rate height anchor-error error) (* 1/4 value-error)))) (other-radius (* 1/2 error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-reciprocal (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error)) (lw-complex-polynomial (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target error) point 0)))
        (radius (+ (* (lw-euler-neighborhood-inverse-gain rate height anchor-error) (+ (lw-euler-uniform-inverse-request rate height anchor-error error) (* 1/4 value-error))) (* 1/2 error)))
        (cap (+ error (* 1/4 (lw-euler-neighborhood-inverse-gain rate height anchor-error) value-error)))))
 :in-theory (union-theories
 '(lw-euler-uniform-inverse-polynomial lw-euler-neighborhood-inverse-gain lw-eui-left-commutes lw-eui-left-distributes lw-eui-fold-constants lw-eui-times-negative lw-eui-negative-times lw-eui-zero-times lw-eui-minus-one lw-eui-double-negative lw-eui-add-cancel lw-eui-double lw-eui-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))


