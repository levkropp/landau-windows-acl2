(in-package "ACL2")

(include-book "polynomial-addition")
(include-book "polynomial-derivatives")

; Exact coefficient identities for sums and constant terms.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-polynomial lw-complex-coefficient-at
          lw-polynomial-add lw-polynomial-add-constant
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes)))

(local (defthm lw-psc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psc-times-negative (a b) (b a)))
                 :in-theory (disable lw-psc-times-negative)))))

(local (defthm lw-psc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psc-left-commutes)))))

(local (defun lw-psc-induct (left right offset)
 (if (or (endp left) (endp right)) offset
  (lw-psc-induct (cdr left) (cdr right) (+ 1 offset)))))

(local (defthm lw-psc-sum-swap
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
  (equal (lw-complex-add (lw-complex-add a b) (lw-complex-add c d))
         (lw-complex-add (lw-complex-add a c) (lw-complex-add b d))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-add-coefficient
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right)
               (natp target) (natp offset))
  (equal (lw-complex-coefficient-at (lw-polynomial-add left right) target offset)
         (lw-complex-add (lw-complex-coefficient-at left target offset)
                         (lw-complex-coefficient-at right target offset))))
 :hints (("Goal"
  :induct (lw-psc-induct left right offset)
  :in-theory (union-theories
 '((:induction lw-psc-induct) lw-polynomial-add lw-polynomial-add-valid lw-complex-coefficient-at lw-complex-coefficientsp endp lw-complex-add-zero lw-complex-add-commutative lw-complex-ring-rational lw-complex-coefficient-at-rational lw-psc-sum-swap (:executable-counterpart lw-complexp) lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-add-constant-zero-coefficient
 (implies (and (lw-complexp constant) (lw-complex-coefficientsp coefficients))
  (equal (lw-complex-coefficient-at (lw-polynomial-add-constant constant coefficients) 0 0)
         (lw-complex-add constant (lw-complex-coefficient-at coefficients 0 0))))
 :hints (("Goal"
  :use (lw-polynomial-add-constant-valid
        (:instance lw-polynomial-add-constant-evaluation (point (cons 0 0)))
        lw-complex-polynomial-at-zero
        (:instance lw-complex-polynomial-at-zero (coefficients (lw-polynomial-add-constant constant coefficients))))
  :in-theory (union-theories
 '(lw-complexp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

