; Finite geometric inversion uses generated polynomials, not abstract models.
(in-package "ACL2")
(include-book "polynomial-product")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner
                 lw-polynomial-add-constant lw-polynomial-multiply-coefficients)))
(local (in-theory (disable lw-polynomial-product lw-complex-geometric-sum
 lw-complex-reciprocal lw-complex-norm-square)))
(local (defthm lw-pgs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pgs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pgs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pgs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pgs-times-negative (a b) (b a)))
                 :in-theory (disable lw-pgs-times-negative)))))

(local (defthm lw-pgs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pgs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pgs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pgs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pgs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pgs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pgs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pgs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pgs-left-commutes)))))

(local (defthm lw-pgs-polynomial-nil
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial endp lw-pgs-left-commutes lw-pgs-left-distributes lw-pgs-fold-constants lw-pgs-times-negative lw-pgs-negative-times lw-pgs-zero-times lw-pgs-minus-one lw-pgs-double-negative lw-pgs-add-cancel lw-pgs-double lw-pgs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-polynomial-geometric-sum (coefficients count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil
  (lw-polynomial-add-constant (cons 1 0)
   (lw-polynomial-product coefficients (lw-polynomial-geometric-sum coefficients (- count 1))))))

(local (in-theory (disable lw-polynomial-geometric-sum)))

(defthm lw-polynomial-geometric-sum-valid
 (implies (lw-complex-coefficientsp coefficients)
 (lw-complex-coefficientsp (lw-polynomial-geometric-sum coefficients count)))
 :hints (("Goal" :induct (lw-polynomial-geometric-sum coefficients count)
 :in-theory (union-theories
 '(lw-polynomial-geometric-sum lw-polynomial-add-constant-valid lw-polynomial-product-valid lw-complex-coefficientsp (:executable-counterpart lw-complexp) lw-pgs-left-commutes lw-pgs-left-distributes lw-pgs-fold-constants lw-pgs-times-negative lw-pgs-negative-times lw-pgs-zero-times lw-pgs-minus-one lw-pgs-double-negative lw-pgs-add-cancel lw-pgs-double lw-pgs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))))

(defthm lw-polynomial-geometric-sum-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp count))
 (equal (lw-complex-polynomial (lw-polynomial-geometric-sum coefficients count) point 0) (lw-complex-geometric-sum (lw-complex-polynomial coefficients point 0) count)))
 :hints (("Goal" :induct (lw-polynomial-geometric-sum coefficients count)
 :in-theory (union-theories
 '(lw-polynomial-geometric-sum lw-complex-geometric-sum lw-polynomial-geometric-sum-valid lw-polynomial-add-constant-valid lw-polynomial-product-valid lw-polynomial-add-constant-evaluation lw-polynomial-product-evaluation lw-complex-polynomial-rational lw-complex-geometric-sum-rational (:executable-counterpart lw-complexp) lw-pgs-polynomial-nil lw-pgs-left-commutes lw-pgs-left-distributes lw-pgs-fold-constants lw-pgs-times-negative lw-pgs-negative-times lw-pgs-zero-times lw-pgs-minus-one lw-pgs-double-negative lw-pgs-add-cancel lw-pgs-double lw-pgs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))))

(defthm lw-polynomial-geometric-sum-remainder-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp count)
  (lw-complex-diskp (lw-complex-polynomial coefficients point 0) radius) (< radius 1))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (cons 1 0) (lw-complex-polynomial coefficients point 0)))
                 (lw-complex-polynomial (lw-polynomial-geometric-sum coefficients count) point 0))
  (* (/ (- 1 radius)) (lw-rational-power radius count))))
 :hints (("Goal"
 :use (lw-polynomial-geometric-sum-evaluation
       (:instance lw-complex-geometric-remainder-bound (point (lw-complex-polynomial coefficients point 0))))
 :in-theory (union-theories
 '( lw-pgs-left-commutes lw-pgs-left-distributes lw-pgs-fold-constants lw-pgs-times-negative lw-pgs-negative-times lw-pgs-zero-times lw-pgs-minus-one lw-pgs-double-negative lw-pgs-add-cancel lw-pgs-double lw-pgs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-geometric-sum-half-cap
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp count)
  (lw-complex-diskp (lw-complex-polynomial coefficients point 0) 1/2))
 (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-geometric-sum coefficients count) point 0) 4))
 :hints (("Goal"
 :use (lw-polynomial-geometric-sum-evaluation
       (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial coefficients point 0)) (radius 1/2) (cap 1))
       (:instance lw-complex-one-minus-norm-lower (point (lw-complex-polynomial coefficients point 0)) (radius 1/2))
       (:instance lw-complex-geometric-unit-sum-bound (point (lw-complex-polynomial coefficients point 0)) (lower 1/2)))
 :in-theory (union-theories
 '( lw-pgs-left-commutes lw-pgs-left-distributes lw-pgs-fold-constants lw-pgs-times-negative lw-pgs-negative-times lw-pgs-zero-times lw-pgs-minus-one lw-pgs-double-negative lw-pgs-add-cancel lw-pgs-double lw-pgs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

