(in-package "ACL2")

(include-book "polynomial-divided-difference")
(include-book "polynomial-leading")

; Synthetic division reduces degree while preserving the final coefficient.

(local (defthm lw-pdl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pdl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pdl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pdl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pdl-times-negative (a b) (b a)))
                 :in-theory (disable lw-pdl-times-negative)))))

(local (defthm lw-pdl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pdl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pdl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pdl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pdl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pdl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pdl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pdl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pdl-left-commutes)))))
(local (defthm lw-pdl-constant-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
               (not (consp (cdr coefficients))) (lw-complexp point))
  (equal (lw-complex-polynomial coefficients point 0) (car coefficients)))
 :hints (("Goal"
  :expand ((lw-complex-polynomial coefficients point 0) (lw-complex-power point 0))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficientsp lw-complex-polynomial lw-complexp lw-complex-mul lw-complex-add endp lw-pdl-left-commutes lw-pdl-left-distributes lw-pdl-fold-constants lw-pdl-times-negative lw-pdl-negative-times lw-pdl-zero-times lw-pdl-minus-one lw-pdl-double-negative lw-pdl-add-cancel lw-pdl-double lw-pdl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-pdl-consp-quotient
 (equal (consp (lw-polynomial-divided-difference coefficients anchor))
        (and (consp coefficients) (consp (cdr coefficients))))
 :hints (("Goal" :expand ((lw-polynomial-divided-difference coefficients anchor))
          :in-theory (union-theories
 '(fold-consts-in-+ endp lw-pdl-left-commutes lw-pdl-left-distributes lw-pdl-fold-constants lw-pdl-times-negative lw-pdl-negative-times lw-pdl-zero-times lw-pdl-minus-one lw-pdl-double-negative lw-pdl-add-cancel lw-pdl-double lw-pdl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-divided-difference-leading
 (implies (and (lw-complex-coefficientsp coefficients)
               (consp coefficients) (consp (cdr coefficients)) (lw-complexp anchor))
  (equal (lw-polynomial-leading (lw-polynomial-divided-difference coefficients anchor))
         (lw-polynomial-leading coefficients)))
 :hints (("Goal" :induct (lw-polynomial-divided-difference coefficients anchor)
          :expand ((lw-polynomial-divided-difference coefficients anchor))
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-divided-difference) lw-polynomial-leading lw-pdl-consp-quotient lw-pdl-constant-evaluation lw-complex-coefficientsp endp lw-pdl-left-commutes lw-pdl-left-distributes lw-pdl-fold-constants lw-pdl-times-negative lw-pdl-negative-times lw-pdl-zero-times lw-pdl-minus-one lw-pdl-double-negative lw-pdl-add-cancel lw-pdl-double lw-pdl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-divided-difference-nonempty
 (implies (and (consp coefficients) (consp (cdr coefficients)))
  (consp (lw-polynomial-divided-difference coefficients anchor)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-pdl-consp-quotient lw-pdl-left-commutes lw-pdl-left-distributes lw-pdl-fold-constants lw-pdl-times-negative lw-pdl-negative-times lw-pdl-zero-times lw-pdl-minus-one lw-pdl-double-negative lw-pdl-add-cancel lw-pdl-double lw-pdl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-pdl-add-difference
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-add b (lw-complex-sub a b)) a))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-pdl-left-commutes lw-pdl-left-distributes lw-pdl-fold-constants lw-pdl-times-negative lw-pdl-negative-times lw-pdl-zero-times lw-pdl-minus-one lw-pdl-double-negative lw-pdl-add-cancel lw-pdl-double lw-pdl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-synthetic-decomposition
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (lw-complexp anchor))
  (equal (lw-complex-polynomial coefficients point 0)
   (lw-complex-add (lw-complex-polynomial coefficients anchor 0)
    (lw-complex-mul (lw-complex-sub point anchor)
     (lw-complex-polynomial (lw-polynomial-divided-difference coefficients anchor) point 0)))))
 :rule-classes nil
 :hints (("Goal"
  :use (lw-polynomial-divided-difference-identity
        (:instance lw-pdl-add-difference
          (a (lw-complex-polynomial coefficients point 0))
          (b (lw-complex-polynomial coefficients anchor 0))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial-rational lw-pdl-left-commutes lw-pdl-left-distributes lw-pdl-fold-constants lw-pdl-times-negative lw-pdl-negative-times lw-pdl-zero-times lw-pdl-minus-one lw-pdl-double-negative lw-pdl-add-cancel lw-pdl-double lw-pdl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
