; Horner convolution constructs actual coefficient lists for products.
(in-package "ACL2")
(include-book "polynomial-affine")
(include-book "polynomial-addition")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner
                 lw-polynomial-add-constant lw-polynomial-multiply-coefficients)))
(local (defthm lw-ppr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppr-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppr-times-negative)))))

(local (defthm lw-ppr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppr-left-commutes)))))

(local (defthm lw-ppr-polynomial-nil
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial endp lw-ppr-left-commutes lw-ppr-left-distributes lw-ppr-fold-constants lw-ppr-times-negative lw-ppr-negative-times lw-ppr-zero-times lw-ppr-minus-one lw-ppr-double-negative lw-ppr-add-cancel lw-ppr-double lw-ppr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppr-multiply-horner
 (implies (and (lw-complexp constant) (lw-complexp point) (lw-complexp tail) (lw-complexp value))
 (equal (lw-complex-mul (lw-complex-add constant (lw-complex-mul point tail)) value)
        (lw-complex-add (lw-complex-mul constant value)
                        (lw-complex-mul point (lw-complex-mul tail value)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-mul lw-ppr-left-commutes lw-ppr-left-distributes lw-ppr-fold-constants lw-ppr-times-negative lw-ppr-negative-times lw-ppr-zero-times lw-ppr-minus-one lw-ppr-double-negative lw-ppr-add-cancel lw-ppr-double lw-ppr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-polynomial-product (left right)
 (if (endp left) nil
  (lw-polynomial-add
   (lw-polynomial-multiply-coefficients (car left) right)
   (lw-polynomial-multiply-linear (cons 0 0) (cons 1 0)
    (lw-polynomial-product (cdr left) right)))))

(local (in-theory (disable lw-polynomial-product)))

(defthm lw-polynomial-product-valid
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right))
 (lw-complex-coefficientsp (lw-polynomial-product left right)))
 :hints (("Goal" :induct (lw-polynomial-product left right)
 :in-theory (union-theories
 '(lw-polynomial-product lw-complex-coefficientsp endp lw-polynomial-add-valid lw-polynomial-multiply-coefficients-valid lw-polynomial-multiply-linear-valid (:executable-counterpart lw-complexp) lw-ppr-left-commutes lw-ppr-left-distributes lw-ppr-fold-constants lw-ppr-times-negative lw-ppr-negative-times lw-ppr-zero-times lw-ppr-minus-one lw-ppr-double-negative lw-ppr-add-cancel lw-ppr-double lw-ppr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))))

(defthm lw-polynomial-product-evaluation
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (lw-complexp point))
 (equal (lw-complex-polynomial (lw-polynomial-product left right) point 0)
        (lw-complex-mul (lw-complex-polynomial left point 0) (lw-complex-polynomial right point 0))))
 :hints (("Goal" :induct (lw-polynomial-product left right)
 :in-theory (union-theories
 '(lw-polynomial-product lw-complex-coefficientsp endp lw-polynomial-product-valid lw-polynomial-add-valid lw-polynomial-multiply-coefficients-valid lw-polynomial-multiply-linear-valid lw-polynomial-add-evaluation lw-polynomial-multiply-coefficients-evaluation lw-polynomial-multiply-linear-evaluation lw-complex-polynomial-horner lw-complex-polynomial-rational lw-ppr-polynomial-nil lw-ppr-multiply-horner lw-complex-mul-zero lw-complex-mul-one lw-complex-add-zero lw-complex-ring-rational (:executable-counterpart lw-complexp) lw-ppr-left-commutes lw-ppr-left-distributes lw-ppr-fold-constants lw-ppr-times-negative lw-ppr-negative-times lw-ppr-zero-times lw-ppr-minus-one lw-ppr-double-negative lw-ppr-add-cancel lw-ppr-double lw-ppr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not '(generalize fertilize))))

