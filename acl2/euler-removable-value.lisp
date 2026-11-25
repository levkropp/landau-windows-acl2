; A uniform rational Cauchy family on a disk containing the point s=1.
; Its identification with the existing normalized Euler family is proved separately.
(in-package "ACL2")
(include-book "euler-removable-numerator")
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
(local (in-theory (disable lw-euler-removable-radius lw-euler-removable-divided-gain
 lw-euler-removable-cost lw-euler-removable-numerator-cap lw-euler-removable-request
 lw-euler-removable-numerator lw-complex-polynomial lw-complex-quotient)))
(local (defthm lw-erv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erv-times-negative (a b) (b a)))
                 :in-theory (disable lw-erv-times-negative)))))

(local (defthm lw-erv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erv-left-commutes)))))

(local (defthm lw-erv-disk-l1
 (implies (lw-complex-diskp point radius)
  (<= (lw-complex-l1 point) (* 2 radius)))
 :hints (("Goal" :use (lw-complex-disk-coordinates)
  :in-theory (union-theories
 '(lw-complex-l1 lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-euler-removable-denominator-clearance
 (implies (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius)))
 (and (lw-complexp point) (lw-complexp (lw-complex-add (cons 1 0) point)) (not (equal (lw-complex-add (cons 1 0) point) (cons 0 0)))
      (<= 1/16 (lw-complex-norm-square (lw-complex-add (cons 1 0) point)))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-add (cons 1 0) point)) 4)))
 :hints (("Goal"
 :use (lw-euler-removable-neighborhood-data
       (:instance lw-complex-disk-data (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-erv-disk-l1 (radius (* 1/2 (lw-euler-removable-radius))))
       (:instance lw-complex-small-shift-clearance (anchor (cons 1 0)) (offset point)))
 :in-theory (union-theories
 '(lw-complex-l1 abs (:executable-counterpart lw-complexp) lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(local (defthm lw-erv-right-product-difference
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp factor))
 (equal (lw-complex-sub (lw-complex-mul a factor) (lw-complex-mul b factor))
        (lw-complex-mul factor (lw-complex-sub a b))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-mul lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-erv-quotient-difference
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp denominator))
 (equal (lw-complex-sub (lw-complex-quotient a denominator) (lw-complex-quotient b denominator))
        (lw-complex-mul (lw-complex-reciprocal denominator) (lw-complex-sub a b))))
 :hints (("Goal"
 :use ((:instance lw-complex-reciprocal-rational (point denominator)))
 :in-theory (union-theories
 '(lw-complex-quotient lw-erv-right-product-difference lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(defun lw-euler-removable-model-value (point target error)
 (lw-complex-quotient (lw-complex-polynomial (lw-euler-removable-numerator target error) point 0)
  (lw-complex-add (cons 1 0) point)))

(local (in-theory (disable lw-euler-removable-model-value)))

(defthm lw-euler-removable-model-value-rational
 (implies (and (lw-complexp point) (natp target) (rationalp error) (< 0 error))
 (lw-complexp (lw-euler-removable-model-value point target error)))
 :hints (("Goal"
 :use (lw-euler-removable-numerator-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-removable-numerator target error)) (offset 0))
       (:instance lw-complex-ring-rational (left (cons 1 0)) (right point))
       (:instance lw-complex-quotient-rational
        (numerator (lw-complex-polynomial (lw-euler-removable-numerator target error) point 0)) (denominator (lw-complex-add (cons 1 0) point))))
 :in-theory (union-theories
 '(lw-euler-removable-model-value (:executable-counterpart lw-complexp) lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-model-value-cap
 (implies (and (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-euler-removable-model-value point target error) (* 4 (lw-euler-removable-numerator-cap))))
 :hints (("Goal"
 :use (lw-euler-removable-denominator-clearance lw-complex-euler-removable-numerator-cap
       (:instance lw-complex-mul-disk (left (lw-complex-polynomial (lw-euler-removable-numerator target error) point 0))
        (right (lw-complex-reciprocal (lw-complex-add (cons 1 0) point))) (radius (lw-euler-removable-numerator-cap)) (other-radius 4)))
 :in-theory (union-theories
 '(lw-euler-removable-model-value lw-complex-quotient lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-model-value-cauchy
 (implies (and (natp left-target) (natp right-target)
  (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
  (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-model-value point left-target left-error) (lw-euler-removable-model-value point right-target right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-euler-removable-denominator-clearance lw-complex-euler-removable-numerator-cauchy
       (:instance lw-euler-removable-request-data (error left-error))
       (:instance lw-euler-removable-request-data (error right-error))
       (:instance lw-euler-removable-numerator-valid (target left-target) (error left-error))
       (:instance lw-euler-removable-numerator-valid (target right-target) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-removable-numerator left-target left-error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-removable-numerator right-target right-error)) (offset 0))
       (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (lw-complex-add (cons 1 0) point))) (right (lw-complex-sub (lw-complex-polynomial (lw-euler-removable-numerator left-target left-error) point 0) (lw-complex-polynomial (lw-euler-removable-numerator right-target right-error) point 0)))
        (radius 4) (other-radius (* (lw-euler-removable-divided-gain) (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error)))))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-mul (lw-complex-reciprocal (lw-complex-add (cons 1 0) point)) (lw-complex-sub (lw-complex-polynomial (lw-euler-removable-numerator left-target left-error) point 0) (lw-complex-polynomial (lw-euler-removable-numerator right-target right-error) point 0))))
        (radius (* 4 (lw-euler-removable-divided-gain) (+ (lw-euler-removable-request left-error) (lw-euler-removable-request right-error)))) (cap (* 1/2 (+ left-error right-error)))))
 :in-theory (union-theories
 '(lw-euler-removable-model-value lw-euler-removable-cost lw-erv-quotient-difference lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-euler-removable-value (point error)
 (lw-euler-removable-model-value point 0 error))

(local (in-theory (disable lw-euler-removable-value)))

(defthm lw-euler-removable-value-rational
 (implies (and (lw-complexp point) (rationalp error) (< 0 error))
 (lw-complexp (lw-euler-removable-value point error)))
 :hints (("Goal" :use ((:instance lw-euler-removable-model-value-rational (target 0)))
 :in-theory (union-theories
 '(lw-euler-removable-value lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-value-cap
 (implies (and (rationalp error) (< 0 error) (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-euler-removable-value point error) (* 4 (lw-euler-removable-numerator-cap))))
 :hints (("Goal" :use ((:instance lw-complex-euler-removable-model-value-cap (target 0)))
 :in-theory (union-theories
 '(lw-euler-removable-value lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-euler-removable-value-cauchy
 (implies (and (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
  (lw-complex-diskp point (* 1/2 (lw-euler-removable-radius))))
 (lw-complex-diskp (lw-complex-sub (lw-euler-removable-value point left-error)
                                 (lw-euler-removable-value point right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :use ((:instance lw-complex-euler-removable-model-value-cauchy (left-target 0) (right-target 0)))
 :in-theory (union-theories
 '(lw-euler-removable-value lw-erv-left-commutes lw-erv-left-distributes lw-erv-fold-constants lw-erv-times-negative lw-erv-negative-times lw-erv-zero-times lw-erv-minus-one lw-erv-double-negative lw-erv-add-cancel lw-erv-double lw-erv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

