(in-package "ACL2")

(include-book "unit-square-linear-index")

; Rational square radius: max of the absolute real and imaginary coordinates.
; It avoids square roots and gives exact clearance from the unit square.

(local (defthm lw-csr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-csr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-csr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-csr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-csr-times-negative (a b) (b a)))
                 :in-theory (disable lw-csr-times-negative)))))

(local (defthm lw-csr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-csr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-csr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-csr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-csr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-csr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-csr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-csr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-csr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-csr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-csr-left-commutes)))))
(defun lw-complex-square-radius (point) (max (abs (car point)) (abs (cdr point))))

(defthm lw-complex-square-radius-data
 (implies (lw-complexp point)
  (and (rationalp (lw-complex-square-radius point)) (<= 0 (lw-complex-square-radius point))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-square-radius lw-complexp max abs lw-csr-left-commutes lw-csr-left-distributes lw-csr-fold-constants lw-csr-times-negative lw-csr-negative-times lw-csr-zero-times lw-csr-minus-one lw-csr-double-negative lw-csr-add-cancel lw-csr-double lw-csr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-complex-square-radius-difference
 (implies (and (lw-complexp a) (lw-complexp b))
  (<= (abs (- (lw-complex-square-radius a) (lw-complex-square-radius b)))
      (lw-complex-square-radius (lw-complex-sub a b))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-square-radius lw-complexp lw-complex-sub max abs lw-csr-left-commutes lw-csr-left-distributes lw-csr-fold-constants lw-csr-times-negative lw-csr-negative-times lw-csr-zero-times lw-csr-minus-one lw-csr-double-negative lw-csr-add-cancel lw-csr-double lw-csr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-complex-square-radius-norm
 (implies (lw-complexp point)
  (<= (* (lw-complex-square-radius point) (lw-complex-square-radius point))
      (lw-complex-norm-square point)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-square-radius lw-complex-norm-square lw-complexp max abs lw-csr-left-commutes lw-csr-left-distributes lw-csr-fold-constants lw-csr-times-negative lw-csr-negative-times lw-csr-zero-times lw-csr-minus-one lw-csr-double-negative lw-csr-add-cancel lw-csr-double lw-csr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :nonlinearp t :do-not-induct t)))

(local (defthm lw-csr-square-order
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= a b))
  (<= (* a a) (* b b)))
 :rule-classes nil
 :hints (("Goal" :nonlinearp t))))

(defthm lw-complex-square-distance-lower
 (implies (and (lw-complexp a) (lw-complexp b))
  (let ((gap (abs (- (lw-complex-square-radius a) (lw-complex-square-radius b)))))
   (<= (* gap gap) (lw-complex-norm-square (lw-complex-sub a b)))))
 :hints (("Goal"
  :use (lw-complex-square-radius-difference
        (:instance lw-complex-square-radius-data (point a))
        (:instance lw-complex-square-radius-data (point b))
        (:instance lw-complex-square-radius-data (point (lw-complex-sub a b)))
        (:instance lw-complex-square-radius-norm (point (lw-complex-sub a b)))
        (:instance lw-csr-square-order
          (a (abs (- (lw-complex-square-radius a) (lw-complex-square-radius b))))
          (b (lw-complex-square-radius (lw-complex-sub a b)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-ring-rational abs lw-csr-left-commutes lw-csr-left-distributes lw-csr-fold-constants lw-csr-times-negative lw-csr-negative-times lw-csr-zero-times lw-csr-minus-one lw-csr-double-negative lw-csr-add-cancel lw-csr-double lw-csr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
