(in-package "ACL2")

(include-book "polynomial-affine")
(include-book "polynomial-factor-roots")

; Represent the product of the generated linear factors by its coefficients.

(local (defthm lw-fcp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-fcp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-fcp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-fcp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-fcp-times-negative (a b) (b a)))
                 :in-theory (disable lw-fcp-times-negative)))))

(local (defthm lw-fcp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-fcp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-fcp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-fcp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-fcp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-fcp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-fcp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-fcp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-fcp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-fcp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-fcp-left-commutes)))))

(defun lw-polynomial-factor-coefficients (roots leading)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     (list leading)
   (lw-polynomial-multiply-linear
    (lw-complex-scale -1 (car roots)) (cons 1 0)
    (lw-polynomial-factor-coefficients (cdr roots) leading))))

(defthm lw-polynomial-factor-coefficients-valid
 (implies (and (lw-ray-pointsp roots) (lw-complexp leading))
  (lw-complex-coefficientsp (lw-polynomial-factor-coefficients roots leading)))
 :hints (("Goal" :induct (lw-polynomial-factor-coefficients roots leading)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-coefficients lw-ray-pointsp lw-complex-coefficientsp lw-polynomial-multiply-linear-valid lw-complex-scale-rational (:executable-counterpart lw-complexp) endp lw-fcp-left-commutes lw-fcp-left-distributes lw-fcp-fold-constants lw-fcp-times-negative lw-fcp-negative-times lw-fcp-zero-times lw-fcp-minus-one lw-fcp-double-negative lw-fcp-add-cancel lw-fcp-double lw-fcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-fcp-single-evaluation
 (implies (and (lw-complexp leading) (lw-complexp point))
  (equal (lw-complex-polynomial (list leading) point 0) leading))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial lw-complexp lw-complex-power lw-complex-mul lw-complex-add lw-complex-scale endp lw-fcp-left-commutes lw-fcp-left-distributes lw-fcp-fold-constants lw-fcp-times-negative lw-fcp-negative-times lw-fcp-zero-times lw-fcp-minus-one lw-fcp-double-negative lw-fcp-add-cancel lw-fcp-double lw-fcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-fcp-monomial
 (implies (and (lw-complexp point) (lw-complexp root))
  (equal (lw-complex-add (lw-complex-scale -1 root) (lw-complex-mul (cons 1 0) point))
         (lw-complex-sub point root)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-fcp-left-commutes lw-fcp-left-distributes lw-fcp-fold-constants lw-fcp-times-negative lw-fcp-negative-times lw-fcp-zero-times lw-fcp-minus-one lw-fcp-double-negative lw-fcp-add-cancel lw-fcp-double lw-fcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-factor-coefficients-evaluation
 (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point))
  (equal (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0)
         (lw-polynomial-linear-factor-value roots leading point)))
 :hints (("Goal" :induct (lw-polynomial-factor-coefficients roots leading)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-coefficients lw-polynomial-linear-factor-value lw-ray-pointsp lw-polynomial-factor-coefficients-valid lw-polynomial-multiply-linear-evaluation lw-complex-scale-rational lw-fcp-monomial lw-fcp-single-evaluation (:executable-counterpart lw-complexp) endp lw-fcp-left-commutes lw-fcp-left-distributes lw-fcp-fold-constants lw-fcp-times-negative lw-fcp-negative-times lw-fcp-zero-times lw-fcp-minus-one lw-fcp-double-negative lw-fcp-add-cancel lw-fcp-double lw-fcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
