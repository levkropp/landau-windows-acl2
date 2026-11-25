; Compute normalization disks and common precision away from one.
(in-package "ACL2")
(include-book "normalized-local-polynomial")
(include-book "euler-log-polynomial-anchor")
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
 lw-euler-uniform-log-cap lw-normalized-local-point-cap lw-normalized-local-numerator-cap
 lw-normalized-local-inverse-cost lw-normalized-local-transport-cost lw-normalized-local-cap
 lw-euler-rounding-precision lw-euler-bounds)))
(local (defthm lw-end-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-end-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-end-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-end-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-end-times-negative (a b) (b a)))
                 :in-theory (disable lw-end-times-negative)))))

(local (defthm lw-end-zero-times (equal (* 0 a) 0)))

(local (defthm lw-end-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-end-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-end-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-end-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-end-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-end-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-end-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-end-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-end-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-end-left-commutes)))))

(local (defthm lw-end-pair-equality
 (implies (equal left right)
  (and (equal (car left) (car right)) (equal (cdr left) (cdr right))))
 :rule-classes nil))

(local (defthm lw-end-cons-equality
 (equal (equal (cons a b) (cons c d)) (and (equal a c) (equal b d)))
 :hints (("Goal" :use ((:instance lw-end-pair-equality (left (cons a b)) (right (cons c d))))
                 :in-theory (union-theories
 '( lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))))

(local (defthm lw-end-base-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))))
 (and (lw-complexp (cons rate height)) (not (equal (cons rate height) (cons 0 0)))
      (lw-complexp (lw-complex-sub (cons rate height) (cons 1 0))) (not (equal (lw-complex-sub (cons rate height) (cons 1 0)) (cons 0 0)))
      (rationalp (lw-complex-l1 (cons rate height))) (< 0 (lw-complex-l1 (cons rate height)))
      (rationalp (lw-complex-l1 (lw-complex-sub (cons rate height) (cons 1 0)))) (< 0 (lw-complex-l1 (lw-complex-sub (cons rate height) (cons 1 0))))))
 :hints (("Goal"
 :cases ((equal rate 1) (equal height 0))
 :use (lw-euler-value-clearance-data
       (:instance lw-complex-l1-clearance (point (cons rate height)))
       (:instance lw-complex-l1-clearance (point (lw-complex-sub (cons rate height) (cons 1 0)))))
 :in-theory (union-theories
 '(lw-end-cons-equality lw-complexp lw-complex-sub lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-normalized-disk-radius (rate height outer-radius anchor-error)
 (min (lw-euler-neighborhood-radius rate height outer-radius anchor-error)
  (min (* 1/4 (lw-complex-l1 (cons rate height)))
       (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate height) (cons 1 0)))))))

(defun lw-euler-normalized-total-cost (rate height outer-radius anchor-error)
 (+ (lw-normalized-local-inverse-cost (cons rate height)
     (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)
     (lw-euler-uniform-log-cap rate height outer-radius anchor-error))
    (lw-normalized-local-transport-cost (cons rate height)
     (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))))

(local (in-theory (disable lw-euler-normalized-disk-radius lw-euler-normalized-total-cost)))

(defthm lw-euler-normalized-disk-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))))
 (and (lw-complexp (cons rate height)) (not (equal (cons rate height) (cons 0 0)))
      (lw-complexp (lw-complex-sub (cons rate height) (cons 1 0))) (not (equal (lw-complex-sub (cons rate height) (cons 1 0)) (cons 0 0)))
      (rationalp (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (< 0 (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (<= (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (< (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) outer-radius) (< (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) rate) (<= (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) 1)
      (<= (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (* 1/4 (lw-complex-l1 (cons rate height)))) (<= (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate height) (cons 1 0)))))
      (rationalp (lw-euler-uniform-log-cap rate height outer-radius anchor-error)) (< 0 (lw-euler-uniform-log-cap rate height outer-radius anchor-error))
      (rationalp (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error))) (< 0 (lw-normalized-local-inverse-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error))) (rationalp (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))) (< 0 (lw-normalized-local-transport-cost (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
      (rationalp (lw-euler-normalized-total-cost rate height outer-radius anchor-error)) (< 0 (lw-euler-normalized-total-cost rate height outer-radius anchor-error)) (rationalp (lw-normalized-local-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error))) (< 0 (lw-normalized-local-cap (cons rate height) (lw-euler-normalized-disk-radius rate height outer-radius anchor-error) (lw-euler-uniform-log-cap rate height outer-radius anchor-error)))))
 :hints (("Goal"
 :use (lw-end-base-data lw-euler-neighborhood-data
       (:instance lw-euler-uniform-log-model-data (error 1))
       (:instance lw-normalized-local-cap-data (anchor (cons rate height)) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (log-cap (lw-euler-uniform-log-cap rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-euler-normalized-disk-radius lw-euler-normalized-total-cost min lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-euler-normalized-request (rate height outer-radius anchor-error error)
 (lw-euler-rounding-precision (lw-euler-normalized-total-cost rate height outer-radius anchor-error) error))
(defun lw-euler-normalized-gamma (rate height outer-radius anchor-error error)
 (car (lw-euler-bounds (lw-euler-normalized-request rate height outer-radius anchor-error error))))

(local (in-theory (disable lw-euler-normalized-request lw-euler-normalized-gamma)))

(defthm lw-euler-normalized-request-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (rationalp error) (< 0 error))
 (and (rationalp (lw-euler-normalized-request rate height outer-radius anchor-error error)) (< 0 (lw-euler-normalized-request rate height outer-radius anchor-error error)) (<= (lw-euler-normalized-request rate height outer-radius anchor-error error) 1)
      (<= (* (lw-euler-normalized-total-cost rate height outer-radius anchor-error) (lw-euler-normalized-request rate height outer-radius anchor-error error)) (* 1/2 error))
      (rationalp (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) (<= (abs (lw-euler-normalized-gamma rate height outer-radius anchor-error error)) 2)))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data
       (:instance lw-euler-rounding-precision-valid (cost (lw-euler-normalized-total-cost rate height outer-radius anchor-error)))
       (:instance lw-euler-bounds-interval (epsilon (lw-euler-normalized-request rate height outer-radius anchor-error error)))
       (:instance lw-euler-bounds-coarse (epsilon (lw-euler-normalized-request rate height outer-radius anchor-error error))))
 :in-theory (union-theories
 '(lw-euler-normalized-request lw-euler-normalized-gamma lw-intervalp abs lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-normalized-point-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (not (and (equal rate 1) (equal height 0))) (lw-complex-diskp point (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
 (and (lw-complexp point) (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error))
      (rationalp (+ rate (car point))) (< 0 (+ rate (car point))) (rationalp (+ height (cdr point)))
      (not (and (equal (+ rate (car point)) 1) (equal (+ height (cdr point)) 0)))))
 :hints (("Goal"
 :use (lw-euler-normalized-disk-data lw-euler-value-clearance-data lw-euler-neighborhood-data
       (:instance lw-complex-disk-data (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-disk-enlarge (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (cap (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-disk-point-data (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error)) (offset point))
       (:instance lw-normalized-local-point-data (anchor (cons rate height)) (radius (lw-euler-normalized-disk-radius rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '(lw-end-cons-equality lw-complex-add lw-complex-sub lw-end-left-commutes lw-end-left-distributes lw-end-fold-constants lw-end-times-negative lw-end-negative-times lw-end-zero-times lw-end-minus-one lw-end-double-negative lw-end-add-cancel lw-end-double lw-end-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

