(in-package "ACL2")

(include-book "polynomial-quadratic-bounds")

; Exact truncation identities and bounded tails for finite polynomials.
; The padded prefix also handles requested counts beyond the list length.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-horner lw-complex-coefficient-at
          lw-polynomial-pad lw-polynomial-coefficient-caps
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes
          lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-ppb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppb-times-negative)))))

(local (defthm lw-ppb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppb-left-commutes)))))

(defun lw-polynomial-drop (coefficients count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) coefficients (lw-polynomial-drop (cdr coefficients) (- count 1))))

(defthm lw-polynomial-drop-valid
 (implies (and (lw-complex-coefficientsp coefficients) (natp count))
  (and (lw-complex-coefficientsp (lw-polynomial-drop coefficients count))
       (implies (lw-polynomial-coefficient-caps coefficients cap)
                (lw-polynomial-coefficient-caps (lw-polynomial-drop coefficients count) cap))))
 :hints (("Goal" :induct (lw-polynomial-drop coefficients count)
  :in-theory (union-theories
   '(lw-polynomial-drop lw-polynomial-coefficient-caps lw-complex-coefficientsp endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (defun lw-ppb-prefix-induct (coefficients count offset)
 (declare (xargs :measure (nfix count)))
 (if (zp count) (list coefficients offset)
  (lw-ppb-prefix-induct (cdr coefficients) (- count 1) (+ 1 offset)))))

(local (defthm lw-ppb-nil-polynomial
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-polynomial)))))

(local (defthm lw-ppb-nil-coefficient
 (equal (lw-complex-coefficient-at nil target offset) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-coefficient-at)))))

(defthm lw-polynomial-pad-prefix-coefficient
 (implies (and (lw-complex-coefficientsp coefficients) (natp count) (natp offset) (natp target)
               (< target (+ offset count)))
  (equal (lw-complex-coefficient-at (lw-polynomial-pad coefficients count) target offset)
         (lw-complex-coefficient-at coefficients target offset)))
 :hints (("Goal" :induct (lw-ppb-prefix-induct coefficients count offset)
  :in-theory (union-theories
   '((:induction lw-ppb-prefix-induct) lw-polynomial-pad lw-complex-coefficient-at lw-complex-coefficientsp lw-complex-add-zero lw-complexp lw-ppb-nil-coefficient lw-complex-coefficient-at-below-offset lw-complex-coefficient-at-rational endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-polynomial-pad-nth
 (implies (and (lw-complex-coefficientsp coefficients) (natp count) (natp index) (< index count))
  (equal (nth index (lw-polynomial-pad coefficients count))
         (lw-complex-coefficient-at coefficients index 0)))
 :hints (("Goal"
  :use (lw-polynomial-pad-valid
        (:instance lw-polynomial-pad-prefix-coefficient (target index) (offset 0))
        (:instance lw-complex-coefficient-at-nth (coefficients (lw-polynomial-pad coefficients count))
         (target index) (offset 0)))
  :in-theory (union-theories
   '( lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ppb-common-head
 (implies (and (lw-complexp head) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-add head left) (lw-complex-add head right))
         (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-add lw-complex-sub lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defthm lw-polynomial-prefix-tail-identity
 (implies (and (lw-complex-coefficientsp coefficients) (natp count) (natp offset) (lw-complexp point))
  (equal
   (lw-complex-sub (lw-complex-polynomial coefficients point offset)
                   (lw-complex-polynomial (lw-polynomial-pad coefficients count) point offset))
   (lw-complex-polynomial (lw-polynomial-drop coefficients count) point (+ offset count))))
 :hints (("Goal" :induct (lw-ppb-prefix-induct coefficients count offset)
  :in-theory (union-theories
   '((:induction lw-ppb-prefix-induct) lw-polynomial-drop lw-polynomial-pad lw-polynomial-pad-valid lw-complex-polynomial lw-complex-coefficientsp lw-ppb-nil-polynomial lw-ppb-common-head lw-complex-polynomial-rational lw-complex-power-rational lw-complex-ring-rational lw-complexp lw-complex-mul-zero lw-complex-add-zero lw-complex-sub-zero endp lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-complex-polynomial-prefix-tail-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-polynomial-coefficient-caps coefficients cap)
               (rationalp cap) (<= 0 cap) (natp count) (lw-complex-diskp point radius) (<= radius 1/2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                   (lw-complex-polynomial (lw-polynomial-pad coefficients count) point 0))
   (* 2 cap (lw-rational-power radius count))))
 :hints (("Goal"
  :use (lw-polynomial-drop-valid lw-complex-disk-data
        (:instance lw-polynomial-prefix-tail-identity (offset 0))
        (:instance lw-complex-polynomial-coefficient-tail-bound
         (coefficients (lw-polynomial-drop coefficients count)) (offset count)))
  :in-theory (union-theories
   '( lw-ppb-left-commutes lw-ppb-left-distributes lw-ppb-fold-constants lw-ppb-times-negative lw-ppb-negative-times lw-ppb-zero-times lw-ppb-minus-one lw-ppb-double-negative lw-ppb-add-cancel lw-ppb-double lw-ppb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (in-theory (disable lw-polynomial-drop)))

