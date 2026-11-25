; Explicit polynomial inversion around a rational nonzero anchor.
(in-package "ACL2")
(include-book "polynomial-geometric-sum")
(include-book "cauchy-resolvents")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner
                 lw-polynomial-add-constant lw-polynomial-multiply-coefficients)))
(local (in-theory (disable lw-polynomial-geometric-sum lw-polynomial-product
 lw-complex-geometric-sum lw-complex-reciprocal lw-complex-norm-square
 lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes)))
(local (defthm lw-piv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-piv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-piv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-piv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-piv-times-negative (a b) (b a)))
                 :in-theory (disable lw-piv-times-negative)))))

(local (defthm lw-piv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-piv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-piv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-piv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-piv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-piv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-piv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-piv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-piv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-piv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-piv-left-commutes)))))

(local (defthm lw-piv-negative-multiple
 (implies (and (lw-complexp factor) (lw-complexp value))
 (equal (lw-complex-add (cons 1 0) (lw-complex-mul (lw-complex-scale -1 factor) value))
        (lw-complex-sub (cons 1 0) (lw-complex-mul factor value))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-mul lw-complex-scale lw-complex-sub lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-polynomial-inverse-residual (coefficients anchor)
 (lw-polynomial-add-constant (cons 1 0)
  (lw-polynomial-multiply-coefficients
   (lw-complex-scale -1 (lw-complex-reciprocal anchor)) coefficients)))

(local (in-theory (disable lw-polynomial-inverse-residual)))

(defthm lw-polynomial-inverse-residual-valid
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor))
 (lw-complex-coefficientsp (lw-polynomial-inverse-residual coefficients anchor)))
 :hints (("Goal"
 :use ((:instance lw-complex-reciprocal-rational (point anchor))
       (:instance lw-complex-scale-rational (factor -1) (point (lw-complex-reciprocal anchor)))
       (:instance lw-polynomial-multiply-coefficients-valid (factor (lw-complex-scale -1 (lw-complex-reciprocal anchor))))
       (:instance lw-polynomial-add-constant-valid
        (constant (cons 1 0)) (coefficients (lw-polynomial-multiply-coefficients (lw-complex-scale -1 (lw-complex-reciprocal anchor)) coefficients))))
 :in-theory (union-theories
 '(lw-polynomial-inverse-residual (:executable-counterpart lw-complexp) lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-inverse-residual-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (lw-complexp point))
 (equal (lw-complex-polynomial (lw-polynomial-inverse-residual coefficients anchor) point 0) (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) (lw-complex-polynomial coefficients point 0)))))
 :hints (("Goal"
 :use ((:instance lw-complex-reciprocal-rational (point anchor))
       (:instance lw-complex-scale-rational (factor -1) (point (lw-complex-reciprocal anchor)))
       (:instance lw-complex-polynomial-rational (offset 0))
       (:instance lw-polynomial-multiply-coefficients-valid (factor (lw-complex-scale -1 (lw-complex-reciprocal anchor))))
       (:instance lw-polynomial-multiply-coefficients-evaluation (factor (lw-complex-scale -1 (lw-complex-reciprocal anchor))) (offset 0))
       (:instance lw-polynomial-add-constant-evaluation
        (constant (cons 1 0)) (coefficients (lw-polynomial-multiply-coefficients (lw-complex-scale -1 (lw-complex-reciprocal anchor)) coefficients))))
 :in-theory (union-theories
 '(lw-polynomial-inverse-residual lw-piv-negative-multiple (:executable-counterpart lw-complexp) lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-polynomial-inverse (coefficients anchor count)
 (lw-polynomial-multiply-coefficients (lw-complex-reciprocal anchor)
  (lw-polynomial-geometric-sum (lw-polynomial-inverse-residual coefficients anchor) count)))

(local (in-theory (disable lw-polynomial-inverse)))

(defthm lw-polynomial-inverse-valid
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor))
 (lw-complex-coefficientsp (lw-polynomial-inverse coefficients anchor count)))
 :hints (("Goal"
 :use (lw-polynomial-inverse-residual-valid
       (:instance lw-complex-reciprocal-rational (point anchor))
       (:instance lw-polynomial-geometric-sum-valid (coefficients (lw-polynomial-inverse-residual coefficients anchor)))
       (:instance lw-polynomial-multiply-coefficients-valid (coefficients (lw-polynomial-geometric-sum (lw-polynomial-inverse-residual coefficients anchor) count)) (factor (lw-complex-reciprocal anchor))))
 :in-theory (union-theories
 '(lw-polynomial-inverse lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-inverse-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (lw-complexp point) (natp count))
 (equal (lw-complex-polynomial (lw-polynomial-inverse coefficients anchor count) point 0) (lw-complex-mul (lw-complex-reciprocal anchor) (lw-complex-geometric-sum (lw-complex-polynomial (lw-polynomial-inverse-residual coefficients anchor) point 0) count))))
 :hints (("Goal"
 :use (lw-polynomial-inverse-residual-valid
       (:instance lw-complex-reciprocal-rational (point anchor))
       (:instance lw-polynomial-geometric-sum-valid (coefficients (lw-polynomial-inverse-residual coefficients anchor)))
       (:instance lw-polynomial-geometric-sum-evaluation (coefficients (lw-polynomial-inverse-residual coefficients anchor)))
       (:instance lw-polynomial-multiply-coefficients-evaluation (coefficients (lw-polynomial-geometric-sum (lw-polynomial-inverse-residual coefficients anchor) count)) (factor (lw-complex-reciprocal anchor)) (offset 0)))
 :in-theory (union-theories
 '(lw-polynomial-inverse lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-piv-normalized-inverse
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
  (lw-complexp value) (lw-complex-diskp (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value)) 1/2))
 (and (not (equal value (cons 0 0)))
      (equal (lw-complex-reciprocal value) (lw-complex-mul (lw-complex-reciprocal anchor) (lw-complex-reciprocal (lw-complex-sub (cons 1 0) (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value))))))))
 :hints (("Goal"
 :use ((:instance lw-complex-one-minus-norm-lower (point (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value))) (radius 1/2))
       (:instance lw-complex-norm-lower-nonzero (point (lw-complex-sub (cons 1 0) (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value)))) (lower 1/2))
       (:instance lw-complex-reciprocal-inverse (point (lw-complex-sub (cons 1 0) (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value)))))
       (:instance lw-complex-mul-associative
        (left value) (middle (lw-complex-reciprocal anchor)) (right (lw-complex-reciprocal (lw-complex-sub (cons 1 0) (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value))))))
       (:instance lw-complex-mul-commutative (left value) (right (lw-complex-reciprocal anchor)))
       (:instance lw-complex-linear-solve
        (a value) (b (lw-complex-mul (lw-complex-reciprocal anchor) (lw-complex-reciprocal (lw-complex-sub (cons 1 0) (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-complex-reciprocal anchor) value)))))) (c (cons 1 0))))
 :in-theory (union-theories
 '(lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-subtract-cancel lw-complex-mul-zero lw-complex-mul-one (:executable-counterpart lw-complexp) lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-polynomial-inverse-error-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
  (not (equal anchor (cons 0 0))) (lw-complexp point) (natp count)
  (lw-complex-diskp (lw-complex-reciprocal anchor) anchor-cap) (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-inverse-residual coefficients anchor) point 0) 1/2))
 (lw-complex-diskp (lw-complex-sub (lw-complex-reciprocal (lw-complex-polynomial coefficients point 0)) (lw-complex-polynomial (lw-polynomial-inverse coefficients anchor count) point 0))
  (* anchor-cap 2 (lw-rational-power 1/2 count))))
 :hints (("Goal"
 :use (lw-polynomial-inverse-residual-valid lw-polynomial-inverse-residual-evaluation
       lw-polynomial-inverse-evaluation
       (:instance lw-complex-polynomial-rational (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-inverse-residual coefficients anchor)) (offset 0))
       (:instance lw-piv-normalized-inverse (value (lw-complex-polynomial coefficients point 0)))
       (:instance lw-polynomial-geometric-sum-remainder-bound (coefficients (lw-polynomial-inverse-residual coefficients anchor)) (radius 1/2))
       (:instance lw-polynomial-geometric-sum-evaluation (coefficients (lw-polynomial-inverse-residual coefficients anchor)))
       (:instance lw-complex-mul-disk
        (left (lw-complex-reciprocal anchor)) (right (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (cons 1 0) (lw-complex-polynomial (lw-polynomial-inverse-residual coefficients anchor) point 0)))
                            (lw-complex-polynomial (lw-polynomial-geometric-sum (lw-polynomial-inverse-residual coefficients anchor) count) point 0)))
        (radius anchor-cap) (other-radius (* 2 (lw-rational-power 1/2 count)))))
 :in-theory (union-theories
 '((:executable-counterpart lw-complexp) lw-complex-mul-subtract lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-geometric-sum-rational lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(local (defthm lw-piv-precision-budget
 (implies (and (rationalp anchor-cap) (<= 0 anchor-cap) (rationalp error) (< 0 error))
 (and (rationalp (/ error (+ 1 anchor-cap))) (< 0 (/ error (+ 1 anchor-cap))) (<= (* anchor-cap (/ error (+ 1 anchor-cap))) error)))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-positive (value (+ 1 anchor-cap)))
       (:instance lw-piv-positive-product (a error) (b (/ (+ 1 anchor-cap))))
       (:instance lw-positive-division-bound (numerator (* anchor-cap error)) (divisor (+ 1 anchor-cap)) (bound error)))
 :in-theory (union-theories
 '( lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defun lw-polynomial-inverse-count (anchor-cap error)
 (lw-resolvent-truncation-count 1/2 (/ error (+ 1 anchor-cap))))

(local (in-theory (disable lw-polynomial-inverse-count)))

(defthm lw-polynomial-inverse-count-natural
 (and (natp (lw-polynomial-inverse-count anchor-cap error)) (posp (lw-polynomial-inverse-count anchor-cap error)))
 :hints (("Goal"
 :use ((:instance lw-resolvent-truncation-count-natural (radius 1/2) (error (/ error (+ 1 anchor-cap)))))
 :in-theory (union-theories
 '(lw-polynomial-inverse-count lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-polynomial-inverse-computed-error
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
  (not (equal anchor (cons 0 0))) (lw-complexp point)
  (rationalp anchor-cap) (<= 0 anchor-cap) (rationalp error) (< 0 error)
  (natp count) (<= (lw-polynomial-inverse-count anchor-cap error) count)
  (lw-complex-diskp (lw-complex-reciprocal anchor) anchor-cap) (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-inverse-residual coefficients anchor) point 0) 1/2))
 (lw-complex-diskp (lw-complex-sub (lw-complex-reciprocal (lw-complex-polynomial coefficients point 0)) (lw-complex-polynomial (lw-polynomial-inverse coefficients anchor count) point 0)) error))
 :hints (("Goal"
 :use (lw-polynomial-inverse-error-bound lw-piv-precision-budget
       (:instance lw-resolvent-truncation-count-adequate (radius 1/2) (error (/ error (+ 1 anchor-cap))))
       (:instance lw-rational-power-rational (base 1/2) (exponent count))
       (:instance lw-piv-multiply-order (a (* 2 (lw-rational-power 1/2 count))) (b (/ error (+ 1 anchor-cap))) (factor anchor-cap))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-reciprocal (lw-complex-polynomial coefficients point 0)) (lw-complex-polynomial (lw-polynomial-inverse coefficients anchor count) point 0)))
        (radius (* anchor-cap 2 (lw-rational-power 1/2 count))) (cap error)))
 :in-theory (union-theories
 '(lw-polynomial-inverse-count lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defthm lw-polynomial-inverse-half-cap
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
  (lw-complexp point) (natp count)
  (lw-complex-diskp (lw-complex-reciprocal anchor) anchor-cap) (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-inverse-residual coefficients anchor) point 0) 1/2))
 (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-inverse coefficients anchor count) point 0) (* 4 anchor-cap)))
 :hints (("Goal"
 :use (lw-polynomial-inverse-residual-valid lw-polynomial-inverse-evaluation
       (:instance lw-polynomial-geometric-sum-half-cap (coefficients (lw-polynomial-inverse-residual coefficients anchor)))
       (:instance lw-polynomial-geometric-sum-evaluation (coefficients (lw-polynomial-inverse-residual coefficients anchor)))
       (:instance lw-complex-mul-disk (left (lw-complex-reciprocal anchor))
        (right (lw-complex-polynomial (lw-polynomial-geometric-sum (lw-polynomial-inverse-residual coefficients anchor) count) point 0)) (radius anchor-cap) (other-radius 4)))
 :in-theory (union-theories
 '( lw-piv-left-commutes lw-piv-left-distributes lw-piv-fold-constants lw-piv-times-negative lw-piv-negative-times lw-piv-zero-times lw-piv-minus-one lw-piv-double-negative lw-piv-add-cancel lw-piv-double lw-piv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))


