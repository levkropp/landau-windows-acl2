(in-package "ACL2")

(include-book "polynomial-factor-differences")

; One positive domain step controls every partial product and factor path.

(local (defthm lw-pfs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfs-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfs-times-negative)))))

(local (defthm lw-pfs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfs-left-commutes)))))
(defun lw-polynomial-factor-mesh-step (roots leading)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) 1
  (let* ((tail-step (lw-polynomial-factor-mesh-step (cdr roots) leading))
         (budget (lw-ray-product-step-budget
          (lw-unit-square-root-gap (car roots)) (lw-unit-square-root-cap (car roots))
          (lw-polynomial-factor-lower (cdr roots) leading) (lw-polynomial-factor-upper (cdr roots) leading)))
         (denominator (+ 1 (lw-polynomial-factor-lipschitz (cdr roots) leading)))
         (candidate (if (equal denominator 0) 0 (* budget (/ denominator)))))
   (if (< candidate tail-step) candidate tail-step))))

(local (defthm lw-pfs-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfs-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfs-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfs-cap-data
 (implies (lw-complexp root)
  (and (rationalp (lw-unit-square-root-cap root)) (<= 2 (lw-unit-square-root-cap root))))
 :hints (("Goal" :use ((:instance lw-complex-l1-bound (point root)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-cap lw-pfs-sum-rational lw-pfs-left-commutes lw-pfs-left-distributes lw-pfs-fold-constants lw-pfs-times-negative lw-pfs-negative-times lw-pfs-zero-times lw-pfs-minus-one lw-pfs-double-negative lw-pfs-add-cancel lw-pfs-double lw-pfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-pfs-common-step
 (implies (and (rationalp target) (< 0 target) (rationalp budget) (< 0 budget)
               (rationalp gain) (<= 0 gain))
  (let* ((candidate (* budget (/ (+ 1 gain))))
         (step (if (< candidate target) candidate target)))
   (and (rationalp step) (< 0 step) (<= step target) (<= step budget)
        (<= (* gain step) budget))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value (+ 1 gain)))
        (:instance lw-pfs-positive-product (a budget) (b (/ (+ 1 gain))))
        (:instance lw-pfs-inverse-factor (divisor (+ 1 gain)) (coefficient budget)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pfs-product-rational lw-pfs-sum-rational lw-pfs-inverse-rational lw-pfs-left-commutes lw-pfs-left-distributes lw-pfs-fold-constants lw-pfs-times-negative lw-pfs-negative-times lw-pfs-zero-times lw-pfs-minus-one lw-pfs-double-negative lw-pfs-add-cancel lw-pfs-double lw-pfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t))))

(defthm lw-polynomial-factor-mesh-step-data
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading) (not (equal leading (cons 0 0))))
  (and (rationalp (lw-polynomial-factor-mesh-step roots leading))
       (< 0 (lw-polynomial-factor-mesh-step roots leading))))
 :hints (("Goal" :induct (lw-polynomial-factor-mesh-step roots leading)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-mesh-step) lw-polynomial-factor-mesh-step lw-unit-square-roots-awayp endp lw-pfs-left-commutes lw-pfs-left-distributes lw-pfs-fold-constants lw-pfs-times-negative lw-pfs-negative-times lw-pfs-zero-times lw-pfs-minus-one lw-pfs-double-negative lw-pfs-add-cancel lw-pfs-double lw-pfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-unit-square-root-gap-data (root (car roots)))
        (:instance lw-pfs-cap-data (root (car roots)))
        (:instance lw-polynomial-factor-lower-data (roots (cdr roots)))
        (:instance lw-polynomial-factor-upper-data (roots (cdr roots)))
        (:instance lw-polynomial-factor-lipschitz-data (roots (cdr roots)))
        (:instance lw-ray-product-step-budget-valid
          (lower-left (lw-unit-square-root-gap (car roots))) (upper-left (lw-unit-square-root-cap (car roots)))
          (lower-right (lw-polynomial-factor-lower (cdr roots) leading)) (upper-right (lw-polynomial-factor-upper (cdr roots) leading)))
        (:instance lw-pfs-common-step
          (target (lw-polynomial-factor-mesh-step (cdr roots) leading))
          (budget (lw-ray-product-step-budget
          (lw-unit-square-root-gap (car roots)) (lw-unit-square-root-cap (car roots))
          (lw-polynomial-factor-lower (cdr roots) leading) (lw-polynomial-factor-upper (cdr roots) leading))) (gain (lw-polynomial-factor-lipschitz (cdr roots) leading)))) :do-not-induct t))))

(defthm lw-polynomial-factor-mesh-step-bounds
 (implies (and (lw-unit-square-roots-awayp roots) (consp roots)
               (lw-complexp leading) (not (equal leading (cons 0 0))))
  (let ((step (lw-polynomial-factor-mesh-step roots leading)) (budget (lw-ray-product-step-budget
          (lw-unit-square-root-gap (car roots)) (lw-unit-square-root-cap (car roots))
          (lw-polynomial-factor-lower (cdr roots) leading) (lw-polynomial-factor-upper (cdr roots) leading))))
   (and (rationalp budget) (< 0 budget)
        (<= step (lw-polynomial-factor-mesh-step (cdr roots) leading))
        (<= step budget)
        (<= (* (lw-polynomial-factor-lipschitz (cdr roots) leading) step) budget))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-factor-mesh-step-data (roots (cdr roots))) (:instance lw-unit-square-root-gap-data (root (car roots)))
        (:instance lw-pfs-cap-data (root (car roots)))
        (:instance lw-polynomial-factor-lower-data (roots (cdr roots)))
        (:instance lw-polynomial-factor-upper-data (roots (cdr roots)))
        (:instance lw-polynomial-factor-lipschitz-data (roots (cdr roots)))
        (:instance lw-ray-product-step-budget-valid
          (lower-left (lw-unit-square-root-gap (car roots))) (upper-left (lw-unit-square-root-cap (car roots)))
          (lower-right (lw-polynomial-factor-lower (cdr roots) leading)) (upper-right (lw-polynomial-factor-upper (cdr roots) leading)))
        (:instance lw-pfs-common-step
          (target (lw-polynomial-factor-mesh-step (cdr roots) leading))
          (budget (lw-ray-product-step-budget
          (lw-unit-square-root-gap (car roots)) (lw-unit-square-root-cap (car roots))
          (lw-polynomial-factor-lower (cdr roots) leading) (lw-polynomial-factor-upper (cdr roots) leading))) (gain (lw-polynomial-factor-lipschitz (cdr roots) leading))))
  :expand ((lw-polynomial-factor-mesh-step roots leading))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-roots-awayp endp lw-pfs-left-commutes lw-pfs-left-distributes lw-pfs-fold-constants lw-pfs-times-negative lw-pfs-negative-times lw-pfs-zero-times lw-pfs-minus-one lw-pfs-double-negative lw-pfs-add-cancel lw-pfs-double lw-pfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
