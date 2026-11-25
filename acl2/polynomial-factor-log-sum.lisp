(in-package "ACL2")

(include-book "polynomial-factor-coefficients")
(include-book "polynomial-affine-derivatives")
(include-book "complex-quotients")

; The logarithmic derivative is the sum of reciprocal linear factors.

(local (defthm lw-fls-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-fls-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-fls-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-fls-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-fls-times-negative (a b) (b a)))
                 :in-theory (disable lw-fls-times-negative)))))

(local (defthm lw-fls-zero-times (equal (* 0 a) 0)))

(local (defthm lw-fls-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-fls-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-fls-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-fls-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-fls-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-fls-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-fls-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-fls-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-fls-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-fls-left-commutes)))))

(defun lw-polynomial-factor-log-sum (roots point)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     (cons 0 0)
   (lw-complex-add (lw-complex-reciprocal (lw-complex-sub point (car roots)))
                   (lw-polynomial-factor-log-sum (cdr roots) point))))

(local (defthm lw-fls-no-zero-factor
 (implies (and (lw-complexp p) (lw-complexp h)
               (not (equal (lw-complex-mul p h) (cons 0 0))))
  (and (not (equal p (cons 0 0))) (not (equal h (cons 0 0)))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-mul-zero lw-complex-mul-commutative (:executable-counterpart lw-complexp) lw-fls-left-commutes lw-fls-left-distributes lw-fls-fold-constants lw-fls-times-negative lw-fls-negative-times lw-fls-zero-times lw-fls-minus-one lw-fls-double-negative lw-fls-add-cancel lw-fls-double lw-fls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-fls-linear
 (implies (and (lw-complexp point) (lw-complexp root))
  (equal (lw-complex-add (lw-complex-scale -1 root) (lw-complex-mul (cons 1 0) point))
         (lw-complex-sub point root)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-fls-left-commutes lw-fls-left-distributes lw-fls-fold-constants lw-fls-times-negative lw-fls-negative-times lw-fls-zero-times lw-fls-minus-one lw-fls-double-negative lw-fls-add-cancel lw-fls-double lw-fls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-fls-linear-after-one
 (implies (and (lw-complexp point) (lw-complexp root))
  (equal (lw-complex-add (lw-complex-scale -1 root) point) (lw-complex-sub point root)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-fls-left-commutes lw-fls-left-distributes lw-fls-fold-constants lw-fls-times-negative lw-fls-negative-times lw-fls-zero-times lw-fls-minus-one lw-fls-double-negative lw-fls-add-cancel lw-fls-double lw-fls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-fls-constant-derivative
 (implies (lw-complexp point)
  (equal (lw-complex-polynomial-derivative (list leading) point) (cons 0 0)))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial-derivative lw-complex-polynomial lw-complex-mul-zero lw-complex-add-zero (:executable-counterpart lw-complexp) endp lw-fls-left-commutes lw-fls-left-distributes lw-fls-fold-constants lw-fls-times-negative lw-fls-negative-times lw-fls-zero-times lw-fls-minus-one lw-fls-double-negative lw-fls-add-cancel lw-fls-double lw-fls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-fls-unit-quotient
 (implies (lw-complexp value)
  (and (equal (lw-complex-quotient (cons 1 0) value) (lw-complex-reciprocal value))
       (equal (lw-complex-quotient (cons 0 0) value) (cons 0 0))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-quotient lw-complex-reciprocal-rational lw-complex-mul-one lw-complex-mul-zero lw-fls-left-commutes lw-fls-left-distributes lw-fls-fold-constants lw-fls-times-negative lw-fls-negative-times lw-fls-zero-times lw-fls-minus-one lw-fls-double-negative lw-fls-add-cancel lw-fls-double lw-fls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-polynomial-factor-log-derivative
 (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
               (not (equal (lw-polynomial-linear-factor-value roots leading point) (cons 0 0))))
  (equal (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-factor-coefficients roots leading) point)
                            (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0))
         (lw-polynomial-factor-log-sum roots point)))
 :hints (("Goal" :induct (lw-polynomial-factor-coefficients roots leading)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-coefficients lw-polynomial-linear-factor-value lw-polynomial-factor-log-sum lw-ray-pointsp lw-fls-constant-derivative lw-polynomial-factor-coefficients-valid lw-polynomial-factor-coefficients-evaluation lw-polynomial-linear-factor-value-rational lw-complex-coefficientsp lw-complex-polynomial-rational lw-complex-polynomial-derivative-rational lw-complex-scale-rational lw-fls-linear lw-fls-linear-after-one lw-fls-unit-quotient lw-complex-ring-rational lw-complex-mul-one (:executable-counterpart lw-complexp) endp lw-fls-left-commutes lw-fls-left-distributes lw-fls-fold-constants lw-fls-times-negative lw-fls-negative-times lw-fls-zero-times lw-fls-minus-one lw-fls-double-negative lw-fls-add-cancel lw-fls-double lw-fls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-polynomial-multiply-linear-derivative
           (constant (lw-complex-scale -1 (car roots))) (slope (cons 1 0)) (coefficients (lw-polynomial-factor-coefficients (cdr roots) leading)))
          (:instance lw-polynomial-multiply-linear-evaluation
           (constant (lw-complex-scale -1 (car roots))) (slope (cons 1 0)) (coefficients (lw-polynomial-factor-coefficients (cdr roots) leading)))
          (:instance lw-fls-no-zero-factor (p (lw-complex-sub point (car roots))) (h (lw-polynomial-linear-factor-value (cdr roots) leading point)))
          (:instance lw-complex-quotient-product-rule (p (lw-complex-sub point (car roots))) (h (lw-polynomial-linear-factor-value (cdr roots) leading point)) (dp (cons 1 0)) (dh (lw-complex-polynomial-derivative (lw-polynomial-factor-coefficients (cdr roots) leading) point))))
    :do-not-induct t))))
