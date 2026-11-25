(in-package "ACL2")

(include-book "polynomial-factor-paths")

; Recursive rational annulus and Lipschitz budgets for a factor family.

(local (defthm lw-pfm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfm-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfm-times-negative)))))

(local (defthm lw-pfm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfm-left-commutes)))))
(defun lw-polynomial-factor-lower (roots leading)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) (lw-complex-nonzero-lower leading)
  (* (lw-unit-square-root-gap (car roots)) (lw-polynomial-factor-lower (cdr roots) leading))))
(defun lw-polynomial-factor-upper (roots leading)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) (lw-complex-l1 leading)
  (* (lw-unit-square-root-cap (car roots)) (lw-polynomial-factor-upper (cdr roots) leading))))
(defun lw-polynomial-factor-lipschitz (roots leading)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) 0
  (+ (* (lw-unit-square-root-cap (car roots)) (lw-polynomial-factor-lipschitz (cdr roots) leading))
     (lw-polynomial-factor-upper (cdr roots) leading))))

(local (defthm lw-pfm-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfm-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfm-cap-data
 (implies (lw-complexp root)
  (and (rationalp (lw-unit-square-root-cap root)) (<= 2 (lw-unit-square-root-cap root))))
 :hints (("Goal" :use ((:instance lw-complex-l1-bound (point root)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-cap lw-pfm-sum-rational lw-pfm-left-commutes lw-pfm-left-distributes lw-pfm-fold-constants lw-pfm-times-negative lw-pfm-negative-times lw-pfm-zero-times lw-pfm-minus-one lw-pfm-double-negative lw-pfm-add-cancel lw-pfm-double lw-pfm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-factor-lower-data
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading) (not (equal leading (cons 0 0))))
  (and (rationalp (lw-polynomial-factor-lower roots leading))
       (< 0 (lw-polynomial-factor-lower roots leading))))
 :hints (("Goal" :induct (lw-polynomial-factor-lower roots leading)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-lower) lw-polynomial-factor-lower lw-unit-square-roots-awayp lw-pfm-product-rational endp lw-pfm-left-commutes lw-pfm-left-distributes lw-pfm-fold-constants lw-pfm-times-negative lw-pfm-negative-times lw-pfm-zero-times lw-pfm-minus-one lw-pfm-double-negative lw-pfm-add-cancel lw-pfm-double lw-pfm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-nonzero-lower-valid (point leading))
                  (:instance lw-unit-square-root-gap-data (root (car roots)))
                  (:instance lw-pfm-positive-product
                    (a (lw-unit-square-root-gap (car roots)))
                    (b (lw-polynomial-factor-lower (cdr roots) leading))))
            :do-not-induct t))))

(defthm lw-polynomial-factor-upper-data
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading))
  (and (rationalp (lw-polynomial-factor-upper roots leading))
       (<= 0 (lw-polynomial-factor-upper roots leading))))
 :hints (("Goal" :induct (lw-polynomial-factor-upper roots leading)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-upper) lw-polynomial-factor-upper lw-unit-square-roots-awayp lw-pfm-product-rational endp lw-pfm-left-commutes lw-pfm-left-distributes lw-pfm-fold-constants lw-pfm-times-negative lw-pfm-negative-times lw-pfm-zero-times lw-pfm-minus-one lw-pfm-double-negative lw-pfm-add-cancel lw-pfm-double lw-pfm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-pfm-cap-data (root (car roots)))
                  (:instance lw-complex-l1-bound (point leading))
                  (:instance lw-pfm-multiply-order (a 0)
                    (b (lw-polynomial-factor-upper (cdr roots) leading))
                    (factor (lw-unit-square-root-cap (car roots)))))
            :do-not-induct t))))

(defthm lw-polynomial-factor-lipschitz-data
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading))
  (and (rationalp (lw-polynomial-factor-lipschitz roots leading))
       (<= 0 (lw-polynomial-factor-lipschitz roots leading))))
 :hints (("Goal" :induct (lw-polynomial-factor-lipschitz roots leading)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-lipschitz) lw-polynomial-factor-lipschitz lw-unit-square-roots-awayp lw-pfm-product-rational lw-pfm-sum-rational endp lw-pfm-left-commutes lw-pfm-left-distributes lw-pfm-fold-constants lw-pfm-times-negative lw-pfm-negative-times lw-pfm-zero-times lw-pfm-minus-one lw-pfm-double-negative lw-pfm-add-cancel lw-pfm-double lw-pfm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-pfm-cap-data (root (car roots)))
                  (:instance lw-polynomial-factor-upper-data (roots (cdr roots)))
                  (:instance lw-pfm-multiply-order (a 0)
                    (b (lw-polynomial-factor-lipschitz (cdr roots) leading))
                    (factor (lw-unit-square-root-cap (car roots)))))
            :do-not-induct t))))
