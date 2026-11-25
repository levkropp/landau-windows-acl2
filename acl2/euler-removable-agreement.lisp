; Identification of the local normalized family away from the center.
(in-package "ACL2")
(include-book "euler-removable-value")
(include-book "euler-log-polynomial-anchor")
(include-book "complex-normalized-extension")
(include-book "mellin-euler-log-derivative")
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
(local (in-theory (disable lw-euler-removable-radius lw-euler-removable-cost
 lw-euler-removable-request lw-euler-removable-model-value lw-euler-removable-value
 lw-euler-removable-numerator lw-euler-uniform-log-polynomial lw-euler-log-divided-polynomial
 lw-complex-polynomial lw-complex-normalized-euler lw-complex-euler-log-derivative-value
 lw-euler-log-transform lw-mellin-euler-log-value lw-mellin-euler-log-request
 lw-euler-value-clearance-check lw-euler-bounds)))
(local (defthm lw-era-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-era-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-era-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-era-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-era-times-negative (a b) (b a)))
                 :in-theory (disable lw-era-times-negative)))))

(local (defthm lw-era-zero-times (equal (* 0 a) 0)))

(local (defthm lw-era-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-era-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-era-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-era-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-era-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-era-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-era-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-era-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-era-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-era-left-commutes)))))

(local (defthm lw-era-pair-reconstruction
 (implies (lw-complexp point) (equal (cons (car point) (cdr point)) point))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp cons-car-cdr lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-era-not-one
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
 (not (and (equal (+ 1 (car point)) 1) (equal (cdr point) 0))))
 :hints (("Goal" :use (lw-era-pair-reconstruction) :cases ((equal (car point) 0))
 :in-theory (union-theories
 '(lw-complexp lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defun lw-euler-removable-step-cap (point)
 (/ (* 1/2 (lw-complex-l1 point))))

(local (in-theory (disable lw-euler-removable-step-cap)))

(defthm lw-euler-removable-point-data
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))))
 (and (lw-complexp point) (lw-complexp (lw-complex-add (cons 1 0) point))
      (rationalp (+ 1 (car point))) (< 0 (+ 1 (car point))) (rationalp (cdr point))
      (not (and (equal (+ 1 (car point)) 1) (equal (cdr point) 0)))
      (rationalp (lw-euler-removable-step-cap point)) (< 0 (lw-euler-removable-step-cap point))
      (lw-complex-diskp (lw-complex-add (cons 1 0) point) 2)
      (lw-complex-diskp (lw-complex-reciprocal point) (lw-euler-removable-step-cap point))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-mul (lw-complex-add (cons 1 0) point) point)) (* 4 (lw-euler-removable-step-cap point)))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-denominator-clearance lw-era-not-one
       (:instance lw-euler-disk-point-data (rate 1) (height 0) (radius (* 1/2 (lw-euler-removable-radius))) (offset point))
       (:instance lw-complex-l1-clearance)
       (:instance lw-reciprocal-positive (value (* 1/2 (lw-complex-l1 point))))
       (:instance lw-complex-reciprocal-disk-bound (lower (* 1/2 (lw-complex-l1 point))))
       (:instance lw-complex-add-disk (left (cons 1 0)) (right point) (radius 1) (other-radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-add (cons 1 0) point)) (radius (+ 1 (* 1/2 (lw-euler-removable-radius)))) (cap 2))
       (:instance lw-complex-reciprocal-product (a (lw-complex-add (cons 1 0) point)) (b point))
       (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (lw-complex-add (cons 1 0) point))) (right (lw-complex-reciprocal point))
        (radius 4) (other-radius (lw-euler-removable-step-cap point))))
 :in-theory (union-theories
 '(lw-euler-removable-step-cap lw-complex-reciprocal-product (:executable-counterpart lw-complex-diskp) lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-removable-model-normalized
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))) (natp target) (rationalp error) (< 0 error))
 (equal (lw-euler-removable-model-value point target error) (lw-complex-normalized-euler point (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-point-data
       lw-euler-removable-denominator-clearance lw-euler-removable-request-data
       lw-euler-removable-numerator-evaluation
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-euler-log-divided-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (offset 0))
       (:instance lw-complex-euler-log-divided-polynomial-identity (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-complex-normalized-euler-divided-identity (value (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) point 0)) (anchor (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0)) (slope (lw-complex-polynomial (lw-euler-log-divided-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) point 0))))
 :in-theory (union-theories
 '(lw-euler-removable-model-value lw-euler-removable-numerator-evaluation (:executable-counterpart lw-complexp) lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-era-gamma-rational
 (implies (and (rationalp gamma-error) (< 0 gamma-error))
 (and (rationalp (car (lw-euler-bounds gamma-error))) (lw-complexp (cons (car (lw-euler-bounds gamma-error)) 0))))
 :hints (("Goal" :use ((:instance lw-euler-bounds-interval (epsilon gamma-error)))
 :in-theory (union-theories
 '(lw-intervalp lw-complexp lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(defthm lw-complex-euler-removable-model-transform-comparison
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))) (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point))) (natp target) (rationalp error) (< 0 error)
  (rationalp value-error) (< 0 value-error) (rationalp gamma-error) (< 0 gamma-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-model-value point target error) (lw-euler-log-transform (+ 1 (car point)) (cdr point) (lw-complex-euler-log-derivative-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error) (car (lw-euler-bounds gamma-error))))
  (* 4 (lw-euler-removable-step-cap point) (+ (lw-euler-removable-request error) value-error (* 2 (+ (lw-euler-removable-request error) gamma-error))))))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-point-data
       lw-euler-removable-request-data lw-euler-removable-model-normalized lw-era-gamma-rational
       (:instance lw-complex-disk-enlarge (radius (* 1/2 (lw-euler-removable-radius))) (cap (lw-euler-removable-radius)))
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error))) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-euler-log-derivative-rational
        (rate (+ 1 (car point))) (height (cdr point)) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-euler-log-polynomial-checked-comparison (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64) (error (lw-euler-removable-request error)))
       (:instance lw-complex-difference-symmetric (left (lw-complex-euler-log-derivative-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) point 0)) (radius (+ (lw-euler-removable-request error) value-error)))
       (:instance lw-complex-euler-log-polynomial-anchor (error (lw-euler-removable-request error)))
       (:instance lw-complex-normalized-euler-real-anchor (value (lw-complex-euler-log-derivative-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (gamma (car (lw-euler-bounds gamma-error))))
       (:instance lw-complex-normalized-euler-transport
        (value (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) point 0)) (other-value (lw-complex-euler-log-derivative-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (anchor (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target (lw-euler-removable-request error)) (cons 0 0) 0)) (other-anchor (cons (car (lw-euler-bounds gamma-error)) 0))
        (point-cap 2) (inverse-cap (* 4 (lw-euler-removable-step-cap point))) (value-error (+ (lw-euler-removable-request error) value-error)) (anchor-error (+ (lw-euler-removable-request error) gamma-error))))
 :in-theory (union-theories
 '(lw-euler-removable-radius lw-euler-removable-model-normalized lw-complex-normalized-euler-real-anchor (:executable-counterpart lw-complexp) lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-era-small-requests
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))) (rationalp margin) (< 0 margin))
 (and (rationalp (lw-euler-removable-request margin)) (< 0 (lw-euler-removable-request margin)) (<= (lw-euler-removable-request margin) margin)
      (rationalp (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin)) (< 0 (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin)) (<= (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin) margin)))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data lw-euler-removable-point-data
       (:instance lw-euler-removable-request-data (error margin))
       (:instance lw-reciprocal-positive (value (lw-euler-removable-radius)))
       (:instance lw-era-multiply-order (a 1) (b (lw-euler-removable-cost)) (factor (lw-euler-removable-request margin)))
       (:instance lw-mellin-euler-log-request-data (rate (+ 1 (car point))) (height (cdr point)) (error margin)))
 :in-theory (union-theories
 '(lw-euler-removable-cost lw-euler-removable-divided-gain lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-era-small-comparison
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))) (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point))) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-value point margin) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor margin)) (* 24 (lw-euler-removable-step-cap point) margin)))
 :hints (("Goal"
 :use (lw-euler-removable-point-data lw-era-small-requests
       (:instance lw-complex-euler-removable-model-transform-comparison
        (target 0) (error margin) (value-error (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin)) (gamma-error (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin)))
       (:instance lw-era-multiply-order (a (lw-euler-removable-request margin)) (b margin) (factor (* 12 (lw-euler-removable-step-cap point))))
       (:instance lw-era-multiply-order (a (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin)) (b margin) (factor (* 12 (lw-euler-removable-step-cap point))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-removable-value point margin) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor margin)))
        (radius (* 4 (lw-euler-removable-step-cap point) (+ (lw-euler-removable-request margin) (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin) (* 2 (+ (lw-euler-removable-request margin) (lw-mellin-euler-log-request (+ 1 (car point)) (cdr point) margin))))))
        (cap (* 24 (lw-euler-removable-step-cap point) margin))))
 :in-theory (union-theories
 '(lw-euler-removable-value lw-mellin-euler-log-value lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-era-agreement-with-margin
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))) (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point))) (natp target) (rationalp error) (< 0 error)
  (rationalp value-error) (< 0 value-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-model-value point target error) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (+ (* 1/2 (+ error value-error)) (* (+ 1 (* 24 (lw-euler-removable-step-cap point))) margin))))
 :hints (("Goal"
 :use (lw-euler-removable-point-data lw-era-small-comparison
       lw-euler-removable-model-value-rational
       (:instance lw-euler-removable-value-rational (error margin))
       (:instance lw-mellin-euler-log-value-rational (rate (+ 1 (car point))) (height (cdr point)) (radius coefficient-radius) (anchor-error local-anchor) (error margin))
       (:instance lw-mellin-euler-log-value-rational (rate (+ 1 (car point))) (height (cdr point)) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-euler-removable-model-value-cauchy (left-target target) (right-target 0) (left-error error) (right-error margin))
       (:instance lw-mellin-euler-log-value-cauchy (rate (+ 1 (car point))) (height (cdr point)) (radius coefficient-radius) (anchor-error local-anchor) (left-error margin) (right-error value-error))
       (:instance lw-complex-difference-triangle (left (lw-euler-removable-model-value point target error)) (middle (lw-euler-removable-value point margin)) (right (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor margin))
        (radius (* 1/2 (+ error margin))) (other-radius (* 24 (lw-euler-removable-step-cap point) margin)))
       (:instance lw-complex-difference-triangle (left (lw-euler-removable-model-value point target error)) (middle (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor margin)) (right (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error))
        (radius (+ (* 1/2 (+ error margin)) (* 24 (lw-euler-removable-step-cap point) margin))) (other-radius (* 1/2 (+ margin value-error))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-euler-removable-model-value point target error) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)))
        (radius (+ (* 1/2 (+ error margin)) (* 24 (lw-euler-removable-step-cap point) margin) (* 1/2 (+ margin value-error))))
        (cap (+ (* 1/2 (+ error value-error)) (* (+ 1 (* 24 (lw-euler-removable-step-cap point))) margin)))))
 :in-theory (union-theories
 '(lw-euler-removable-value lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-removable-model-agreement
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))) (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point))) (natp target) (rationalp error) (< 0 error)
  (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-model-value point target error) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-euler-removable-model-value point target error) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :use (lw-euler-removable-point-data lw-euler-removable-model-value-rational
       (:instance lw-mellin-euler-log-value-rational (rate (+ 1 (car point))) (height (cdr point)) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-operations-rational (left (lw-euler-removable-model-value point target error)) (right (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-euler-removable-model-value point target error) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error))) (radius (* 1/2 (+ error value-error))) (cost (+ 1 (* 24 (lw-euler-removable-step-cap point)))))
       (:instance lw-era-agreement-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-euler-removable-model-value point target error) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error)) (+ 1 (* 24 (lw-euler-removable-step-cap point)))))))
 :in-theory (union-theories
 '( lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-removable-agreement
 (implies (and (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))) (not (equal point (cons 0 0))) (lw-euler-value-clearance-check (+ 1 (car point)) (cdr point) local-anchor)
 (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ 1 (car point))) (rationalp error) (< 0 error)
  (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-value point error) (lw-mellin-euler-log-value (+ 1 (car point)) (cdr point) coefficient-radius local-anchor value-error)) (* 1/2 (+ error value-error))))
 :hints (("Goal"
 :use ((:instance lw-complex-euler-removable-model-agreement (target 0)))
 :in-theory (union-theories
 '(lw-euler-removable-value lw-era-left-commutes lw-era-left-distributes lw-era-fold-constants lw-era-times-negative lw-era-negative-times lw-era-zero-times lw-era-minus-one lw-era-double-negative lw-era-add-cancel lw-era-double lw-era-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))


