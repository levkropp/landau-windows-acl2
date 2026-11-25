; Actual uniform polynomial models for V'/V on generated nonzero disks.
; Model coefficients and boundary caps are independent of the evaluation point.
(in-package "ACL2")
(include-book "euler-uniform-inverse")
(include-book "euler-log-derivative")
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
(local (in-theory (disable lw-euler-neighborhood-radius lw-euler-value-clearance-check
 lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-euler-neighborhood-inverse-gain
 lw-euler-neighborhood-anchor-inverse-cap lw-euler-uniform-derivative-cap
 lw-euler-uniform-derivative-polynomial lw-euler-uniform-inverse-polynomial
 lw-euler-rounding-precision lw-polynomial-product lw-complex-polynomial
 lw-complex-euler-local-coefficient-value lw-complex-quotient
 lw-euler-log-derivative-cost lw-euler-log-derivative-request lw-complex-euler-log-derivative-value)))
(local (defthm lw-eul-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eul-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eul-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eul-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eul-times-negative (a b) (b a)))
                 :in-theory (disable lw-eul-times-negative)))))

(local (defthm lw-eul-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eul-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eul-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eul-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eul-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eul-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eul-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eul-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eul-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eul-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eul-left-commutes)))))

(defun lw-euler-uniform-log-slope-cap (rate height outer-radius anchor-error)
 (+ 2 (lw-euler-uniform-derivative-cap rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error))))

(defun lw-euler-uniform-log-model-cost (rate height outer-radius anchor-error)
 (+ (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))) (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error)))

(defun lw-euler-uniform-log-node-cost (rate height outer-radius anchor-error)
 (+ (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))) (* 1/4 (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error) (lw-euler-neighborhood-inverse-gain rate height anchor-error))))

(defun lw-euler-uniform-log-request (rate height outer-radius anchor-error error)
 (lw-euler-rounding-precision (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error) error))

(defun lw-euler-uniform-log-cap (rate height outer-radius anchor-error)
 (* (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error) 4 (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)))

(local (in-theory (disable lw-euler-uniform-log-slope-cap lw-euler-uniform-log-model-cost
 lw-euler-uniform-log-node-cost lw-euler-uniform-log-request lw-euler-uniform-log-cap)))

(defthm lw-euler-uniform-log-model-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (rationalp error) (< 0 error))
 (and (rationalp (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error)) (< 0 (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error)) (rationalp (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error)) (< 0 (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error))
      (rationalp (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error)) (< 0 (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error)) (rationalp (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (< 0 (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (<= (lw-euler-uniform-log-request rate height outer-radius anchor-error error) 1)
      (<= (* (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error) (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (* 1/2 error))
      (rationalp (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (< 0 (lw-euler-uniform-log-cap rate height outer-radius anchor-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-neighborhood-inverse-data
       (:instance lw-euler-uniform-derivative-cap-valid (inner-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-reciprocal-positive (value (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))))
       (:instance lw-eul-positive-product (a (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error)) (b (lw-euler-neighborhood-inverse-gain rate height anchor-error)))
       (:instance lw-eul-positive-product (a (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error)) (b (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)))
       (:instance lw-euler-rounding-precision-valid (cost (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-euler-uniform-log-slope-cap lw-euler-uniform-log-model-cost lw-euler-uniform-log-node-cost lw-euler-uniform-log-request lw-euler-uniform-log-cap lw-eul-left-commutes lw-eul-left-distributes lw-eul-fold-constants lw-eul-times-negative lw-eul-negative-times lw-eul-zero-times lw-eul-minus-one lw-eul-double-negative lw-eul-add-cancel lw-eul-double lw-eul-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-euler-uniform-log-polynomial (rate height outer-radius anchor-error target error)
 (lw-polynomial-product (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))))

(local (in-theory (disable lw-euler-uniform-log-polynomial)))

(defthm lw-euler-uniform-log-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-uniform-log-model-data
       (:instance lw-euler-uniform-derivative-polynomial-valid (inner-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-euler-uniform-inverse-polynomial-valid (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-polynomial-product-valid (left (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))) (right (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))))
 :in-theory (union-theories
 '(lw-euler-uniform-log-polynomial lw-eul-left-commutes lw-eul-left-distributes lw-eul-fold-constants lw-eul-times-negative lw-eul-negative-times lw-eul-zero-times lw-eul-minus-one lw-eul-double-negative lw-eul-add-cancel lw-eul-double lw-eul-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-uniform-log-polynomial-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (natp target) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-uniform-log-model-data
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-uniform-derivative-polynomial-valid (inner-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-euler-uniform-inverse-polynomial-valid (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-euler-uniform-derivative-polynomial-cap
        (inner-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (center point) (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-euler-uniform-inverse-polynomial-cap (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-polynomial-product-evaluation (left (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))) (right (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))))
       (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) point 0)) (right (lw-complex-polynomial (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) point 0)) (radius (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error)) (other-radius (* 4 (lw-euler-neighborhood-anchor-inverse-cap rate height anchor-error)))))
 :in-theory (union-theories
 '(lw-euler-uniform-log-polynomial lw-euler-uniform-log-cap lw-euler-uniform-log-slope-cap lw-eul-left-commutes lw-eul-left-distributes lw-eul-fold-constants lw-eul-times-negative lw-eul-negative-times lw-eul-zero-times lw-eul-minus-one lw-eul-double-negative lw-eul-add-cancel lw-eul-double lw-eul-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-uniform-log-node-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
  (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point)))
  (natp target) (rationalp error) (< 0 error)
  (rationalp request) (< 0 request) (<= request anchor-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-quotient (lw-complex-euler-local-coefficient-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius 1 request) (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) request)) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)) (+ (* (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error) (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (* (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error) request))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-neighborhood-inverse-data lw-euler-uniform-log-model-data
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-disk-point-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (offset point))
       (:instance lw-euler-uniform-derivative-polynomial-valid (inner-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-euler-uniform-inverse-polynomial-valid (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))) (offset 0))
       (:instance lw-polynomial-product-evaluation (left (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))) (right (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target (lw-euler-uniform-log-request rate height outer-radius anchor-error error))))
       (:instance lw-complex-euler-local-coefficient-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (index 1) (error request))
       (:instance lw-complex-euler-neighborhood-value-clearance (error request))
       (:instance lw-complex-reciprocal-rational (point (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) request)))
       (:instance lw-complex-euler-uniform-derivative-comparison
        (inner-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (center point) (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (coefficient-error request))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) point 0)) (right (lw-complex-euler-local-coefficient-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius 1 request)) (radius (+ (lw-euler-uniform-log-request rate height outer-radius anchor-error error) request)))
       (:instance lw-complex-euler-uniform-derivative-polynomial-cap
        (inner-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (center point) (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)))
       (:instance lw-complex-euler-uniform-inverse-comparison (error (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (value-error request))
       (:instance lw-complex-mul-difference-bound (a (lw-complex-euler-local-coefficient-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius 1 request)) (b (lw-complex-reciprocal (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) request))) (c (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial rate height outer-radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error) target (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) point 0)) (d (lw-complex-polynomial (lw-euler-uniform-inverse-polynomial rate height outer-radius anchor-error target (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) point 0))
        (right-cap (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))) (left-cap (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error)) (left-error (+ (lw-euler-uniform-log-request rate height outer-radius anchor-error error) request)) (right-error (+ (lw-euler-uniform-log-request rate height outer-radius anchor-error error) (* 1/4 (lw-euler-neighborhood-inverse-gain rate height anchor-error) request))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-quotient (lw-complex-euler-local-coefficient-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius 1 request) (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) request)) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)))
        (radius (+ (* (/ (* 1/4 (lw-euler-value-clearance-size rate height anchor-error))) (+ (lw-euler-uniform-log-request rate height outer-radius anchor-error error) request)) (* (lw-euler-uniform-log-slope-cap rate height outer-radius anchor-error) (+ (lw-euler-uniform-log-request rate height outer-radius anchor-error error) (* 1/4 (lw-euler-neighborhood-inverse-gain rate height anchor-error) request)))))
        (cap (+ (* (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error) (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (* (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error) request)))))
 :in-theory (union-theories
 '(lw-euler-uniform-log-polynomial lw-euler-uniform-log-model-cost lw-euler-uniform-log-node-cost lw-euler-uniform-log-slope-cap lw-complex-quotient lw-eul-left-commutes lw-eul-left-distributes lw-eul-fold-constants lw-eul-times-negative lw-eul-negative-times lw-eul-zero-times lw-eul-minus-one lw-eul-double-negative lw-eul-add-cancel lw-eul-double lw-eul-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-euler-uniform-log-comparison-request
 (rate height outer-radius anchor-error point coefficient-radius error)
 (min anchor-error
  (min (* 1/4 (lw-euler-value-clearance-lower (+ rate (car point)) (+ height (cdr point)) (* 1/2 anchor-error)))
   (lw-euler-rounding-precision (+ (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)) (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error)) error))))

(local (in-theory (disable lw-euler-uniform-log-comparison-request)))

(defthm lw-euler-uniform-log-comparison-request-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (rationalp error) (< 0 error))
 (and (rationalp (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)) (< 0 (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)) (<= (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error) anchor-error) (<= (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error) 1)
      (<= (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error) (* 1/4 (lw-euler-value-clearance-lower (+ rate (car point)) (+ height (cdr point)) (* 1/2 anchor-error))))
      (rationalp (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error))) (< 0 (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)))
      (<= (* (+ (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)) (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error)) (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)) (* 1/2 error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-uniform-log-model-data lw-euler-neighborhood-shifted-check
       (:instance lw-euler-value-clearance-data (rate (+ rate (car point))) (height (+ height (cdr point))) (anchor-error (* 1/2 anchor-error)))
       (:instance lw-euler-log-derivative-cost-valid (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error (* 1/2 anchor-error)))
       (:instance lw-euler-rounding-precision-valid (cost (+ (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)) (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error))))
       (:instance lw-eul-multiply-order (a (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error))
        (b (lw-euler-rounding-precision (+ (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)) (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error)) error)) (factor (+ (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)) (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error)))))
 :in-theory (union-theories
 '(lw-euler-uniform-log-comparison-request min lw-eul-left-commutes lw-eul-left-distributes lw-eul-fold-constants lw-eul-times-negative lw-eul-negative-times lw-eul-zero-times lw-eul-minus-one lw-eul-double-negative lw-eul-add-cancel lw-eul-double lw-eul-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-uniform-log-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (natp target) (rationalp error) (< 0 error)
  (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error) value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)) (+ error value-error)))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-uniform-log-model-data lw-euler-neighborhood-shifted-check
       lw-euler-uniform-log-comparison-request-data lw-euler-uniform-log-polynomial-valid
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-value-clearance-data (rate (+ rate (car point))) (height (+ height (cdr point))) (anchor-error (* 1/2 anchor-error)))
       (:instance lw-complex-euler-log-derivative-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error (* 1/2 anchor-error)) (error value-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-complex-euler-local-coefficient-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (index 1) (error (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)))
       (:instance lw-complex-euler-continuation-value-rational (rate (+ rate (car point))) (height (+ height (cdr point))) (error (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)))
       (:instance lw-complex-quotient-rational (numerator (lw-complex-euler-local-coefficient-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius 1 (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error))) (denominator (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error))))
       (:instance lw-complex-euler-uniform-log-node-comparison (request (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)))
       (:instance lw-complex-euler-log-derivative-common-comparison
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error (* 1/2 anchor-error))
        (error value-error) (request (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error) value-error)) (middle (lw-complex-quotient (lw-complex-euler-local-coefficient-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius 1 (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)) (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)))) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0))
        (radius (+ value-error (* (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)) (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)))) (other-radius (+ (* (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error) (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (* (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error) (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error) value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)))
        (radius (+ value-error (* (lw-euler-log-derivative-cost (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error)) (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error)) (* (lw-euler-uniform-log-model-cost rate height outer-radius anchor-error) (lw-euler-uniform-log-request rate height outer-radius anchor-error error)) (* (lw-euler-uniform-log-node-cost rate height outer-radius anchor-error) (lw-euler-uniform-log-comparison-request rate height outer-radius anchor-error point coefficient-radius error))))
        (cap (+ error value-error))))
 :in-theory (union-theories
 '( lw-eul-left-commutes lw-eul-left-distributes lw-eul-fold-constants lw-eul-times-negative lw-eul-negative-times lw-eul-zero-times lw-eul-minus-one lw-eul-double-negative lw-eul-add-cancel lw-eul-double lw-eul-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-neighborhood-log-uniform-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point))) (rationalp value-error) (< 0 value-error) (<= value-error 1))
 (lw-complex-diskp (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error) value-error) (+ 2 (lw-euler-uniform-log-cap rate height outer-radius anchor-error))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-data lw-euler-neighborhood-shifted-check
       (:instance lw-euler-uniform-log-model-data (error 1))
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-uniform-log-polynomial-valid (target 0) (error 1))
       (:instance lw-complex-euler-uniform-log-polynomial-cap (target 0) (error 1))
       (:instance lw-complex-polynomial-rational
        (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error 0 1)) (offset 0))
       (:instance lw-complex-euler-log-derivative-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error (* 1/2 anchor-error)) (error value-error))
       (:instance lw-complex-euler-uniform-log-comparison (target 0) (error 1))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error) value-error))
        (middle (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error 0 1) point 0))
        (right (cons 0 0)) (radius (+ 1 value-error)) (other-radius (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error) value-error)) (radius (+ 1 value-error (lw-euler-uniform-log-cap rate height outer-radius anchor-error))) (cap (+ 2 (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))))
 :in-theory (union-theories
 '(lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-eul-left-commutes lw-eul-left-distributes lw-eul-fold-constants lw-eul-times-negative lw-eul-negative-times lw-eul-zero-times lw-eul-minus-one lw-eul-double-negative lw-eul-add-cancel lw-eul-double lw-eul-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))


