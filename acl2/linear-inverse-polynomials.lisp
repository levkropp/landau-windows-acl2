; Uniform polynomial inverses of an affine denominator.
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
(local (in-theory (disable lw-complex-polynomial lw-polynomial-inverse
 lw-polynomial-inverse-count lw-polynomial-inverse-residual)))
(local (defthm lw-lip-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lip-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-lip-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-lip-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-lip-times-negative (a b) (b a)))
                 :in-theory (disable lw-lip-times-negative)))))

(local (defthm lw-lip-zero-times (equal (* 0 a) 0)))

(local (defthm lw-lip-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-lip-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-lip-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-lip-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-lip-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-lip-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-lip-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lip-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lip-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-lip-left-commutes)))))

(defun lw-linear-polynomial (anchor) (list anchor (cons 1 0)))
(defun lw-linear-inverse-cap (anchor) (/ (* 1/2 (lw-complex-l1 anchor))))
(local (in-theory (disable lw-linear-polynomial lw-linear-inverse-cap)))

(defthm lw-linear-polynomial-valid
 (implies (lw-complexp anchor) (lw-complex-coefficientsp (lw-linear-polynomial anchor)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-linear-polynomial lw-complex-coefficientsp endp (:executable-counterpart lw-complexp) lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-linear-polynomial-evaluation
 (implies (and (lw-complexp anchor) (lw-complexp point))
 (equal (lw-complex-polynomial (lw-linear-polynomial anchor) point 0) (lw-complex-add anchor point)))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-linear-polynomial lw-complex-polynomial lw-complex-power endp lw-complex-mul-one lw-complex-mul-zero lw-complex-add-zero (:executable-counterpart lw-complexp) lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-linear-inverse-cap-data
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))))
 (and (rationalp (lw-complex-l1 anchor)) (< 0 (lw-complex-l1 anchor)) (rationalp (lw-linear-inverse-cap anchor)) (< 0 (lw-linear-inverse-cap anchor))
      (lw-complex-diskp (lw-complex-reciprocal anchor) (lw-linear-inverse-cap anchor))
      (equal (* (lw-linear-inverse-cap anchor) (* 1/4 (lw-complex-l1 anchor))) 1/2)))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-clearance (point anchor))
       (:instance lw-reciprocal-positive (value (* 1/2 (lw-complex-l1 anchor))))
       (:instance lw-complex-reciprocal-disk-bound (point anchor) (lower (* 1/2 (lw-complex-l1 anchor))))
       (:instance lw-lip-inverse-factor (divisor (* 1/2 (lw-complex-l1 anchor))) (coefficient 1/2)))
 :in-theory (union-theories
 '(lw-linear-inverse-cap lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(local (defthm lw-lip-residual-factor
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0))) (lw-complexp value))
 (equal (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value))
        (lw-complex-mul (lw-complex-reciprocal anchor) (lw-complex-sub anchor value))))
 :hints (("Goal"
 :use ((:instance lw-complex-reciprocal-inverse (point anchor)))
 :in-theory (union-theories
 '(lw-complex-mul-subtract lw-complex-reciprocal-rational (:executable-counterpart lw-complexp) lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(local (defthm lw-lip-negative-offset
 (implies (and (lw-complexp anchor) (lw-complexp point))
 (equal (lw-complex-sub anchor (lw-complex-add anchor point)) (lw-complex-scale -1 point)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-linear-inverse-residual-bound
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
  (lw-complex-diskp point radius) (<= radius (* 1/4 (lw-complex-l1 anchor))))
 (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-inverse-residual (lw-linear-polynomial anchor) anchor) point 0) 1/2))
 :hints (("Goal"
 :use (lw-linear-polynomial-valid lw-linear-inverse-cap-data
       (:instance lw-complex-disk-data)
       lw-linear-polynomial-evaluation
       (:instance lw-polynomial-inverse-residual-evaluation (coefficients (lw-linear-polynomial anchor)))
       (:instance lw-lip-residual-factor (value (lw-complex-add anchor point)))
       (:instance lw-complex-ring-rational (left anchor) (right point))
       (:instance lw-complex-scale-disk (factor -1))
       (:instance lw-lip-multiply-order (a radius) (b (* 1/4 (lw-complex-l1 anchor))) (factor (lw-linear-inverse-cap anchor)))
       (:instance lw-complex-mul-disk (left (lw-complex-reciprocal anchor)) (right (lw-complex-scale -1 point))
        (radius (lw-linear-inverse-cap anchor)) (other-radius radius))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-mul (lw-complex-reciprocal anchor) (lw-complex-scale -1 point)))
        (radius (* (lw-linear-inverse-cap anchor) radius)) (cap 1/2)))
 :in-theory (union-theories
 '(lw-lip-negative-offset abs lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-linear-denominator-clearance
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
  (lw-complex-diskp point radius) (<= radius (* 1/4 (lw-complex-l1 anchor))))
 (and (lw-complexp (lw-complex-add anchor point)) (not (equal (lw-complex-add anchor point) (cons 0 0)))
      (<= (* 1/16 (lw-complex-l1 anchor) (lw-complex-l1 anchor)) (lw-complex-norm-square (lw-complex-add anchor point)))
      (lw-complex-diskp (lw-complex-reciprocal (lw-complex-add anchor point)) (/ (* 1/4 (lw-complex-l1 anchor))))))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-data)
       lw-linear-inverse-cap-data
       (:instance lw-complex-disk-enlarge (cap (* 1/4 (lw-complex-l1 anchor))))
       (:instance lw-complex-ring-rational (left anchor) (right point))
       (:instance lw-complex-disk-anchor-clearance (point (lw-complex-add anchor point))))
 :in-theory (union-theories
 '(lw-complex-sub-add-cancel lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-linear-inverse-polynomial (anchor error)
 (lw-polynomial-inverse (lw-linear-polynomial anchor) anchor
  (lw-polynomial-inverse-count (lw-linear-inverse-cap anchor) error)))

(local (in-theory (disable lw-linear-inverse-polynomial)))

(defthm lw-linear-inverse-polynomial-valid
 (implies (lw-complexp anchor) (lw-complex-coefficientsp (lw-linear-inverse-polynomial anchor error)))
 :hints (("Goal"
 :use (lw-linear-polynomial-valid (:instance lw-polynomial-inverse-valid (coefficients (lw-linear-polynomial anchor)) (count (lw-polynomial-inverse-count (lw-linear-inverse-cap anchor) error))))
 :in-theory (union-theories
 '(lw-linear-inverse-polynomial lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-linear-inverse-polynomial-cap
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
  (lw-complex-diskp point radius) (<= radius (* 1/4 (lw-complex-l1 anchor))))
 (lw-complex-diskp (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0) (* 4 (lw-linear-inverse-cap anchor))))
 :hints (("Goal"
 :use (lw-linear-polynomial-valid lw-linear-inverse-cap-data lw-linear-inverse-residual-bound
       (:instance lw-complex-disk-data)
       (:instance lw-polynomial-inverse-count-natural (anchor-cap (lw-linear-inverse-cap anchor)))
       (:instance lw-polynomial-inverse-half-cap (coefficients (lw-linear-polynomial anchor)) (count (lw-polynomial-inverse-count (lw-linear-inverse-cap anchor) error)) (anchor-cap (lw-linear-inverse-cap anchor))))
 :in-theory (union-theories
 '(lw-linear-inverse-polynomial lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-linear-inverse-polynomial-error
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
  (lw-complex-diskp point radius) (<= radius (* 1/4 (lw-complex-l1 anchor)))
  (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-reciprocal (lw-complex-add anchor point)) (lw-complex-polynomial (lw-linear-inverse-polynomial anchor error) point 0)) error))
 :hints (("Goal"
 :use (lw-linear-polynomial-valid lw-linear-inverse-cap-data lw-linear-inverse-residual-bound
       (:instance lw-complex-disk-data)
       lw-linear-polynomial-evaluation
       (:instance lw-polynomial-inverse-count-natural (anchor-cap (lw-linear-inverse-cap anchor)))
       (:instance lw-polynomial-inverse-computed-error (coefficients (lw-linear-polynomial anchor)) (count (lw-polynomial-inverse-count (lw-linear-inverse-cap anchor) error)) (anchor-cap (lw-linear-inverse-cap anchor))))
 :in-theory (union-theories
 '(lw-linear-inverse-polynomial lw-lip-left-commutes lw-lip-left-distributes lw-lip-fold-constants lw-lip-times-negative lw-lip-negative-times lw-lip-zero-times lw-lip-minus-one lw-lip-double-negative lw-lip-add-cancel lw-lip-double lw-lip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

