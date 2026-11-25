(in-package "ACL2")

(include-book "polynomial-factor-step-budget")

; A common mesh makes the product index the sum of its linear-factor counts.

(local (defthm lw-pfi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfi-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfi-times-negative)))))

(local (defthm lw-pfi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfi-left-commutes)))))
(local (defthm lw-pfi-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfi-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfi-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pfi-cap-data
 (implies (lw-complexp root)
  (and (rationalp (lw-unit-square-root-cap root)) (<= 2 (lw-unit-square-root-cap root))))
 :hints (("Goal" :use ((:instance lw-complex-l1-bound (point root)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-cap lw-pfi-sum-rational lw-pfi-left-commutes lw-pfi-left-distributes lw-pfi-fold-constants lw-pfi-times-negative lw-pfi-negative-times lw-pfi-zero-times lw-pfi-minus-one lw-pfi-double-negative lw-pfi-add-cancel lw-pfi-double lw-pfi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))
(local (defthm lw-pfi-pair
 (implies (consp roots) (equal (cons (car roots) (cdr roots)) roots))
 :hints (("Goal" :in-theory (theory 'ground-zero)))))

(local (defthm lw-pfi-head-product
 (implies (and (consp roots) (lw-unit-square-roots-awayp roots) (lw-complexp leading) (lw-ray-pointsp points))
  (equal (lw-polynomial-factor-path-values roots leading points)
   (lw-ray-pointwise-products (lw-ray-translate-points (car roots) points)
                              (lw-polynomial-factor-path-values (cdr roots) leading points))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-factor-path-product (root (car roots)) (roots (cdr roots))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-roots-awayp lw-unit-square-roots-away-data lw-pfi-pair endp lw-pfi-left-commutes lw-pfi-left-distributes lw-pfi-fold-constants lw-pfi-times-negative lw-pfi-negative-times lw-pfi-zero-times lw-pfi-minus-one lw-pfi-double-negative lw-pfi-add-cancel lw-pfi-double lw-pfi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-pfi-transfer
 (implies (and (rationalp error) (rationalp step) (rationalp gain) (<= 0 gain)
               (rationalp budget) (<= error step) (<= step budget) (<= (* gain step) budget))
  (and (<= error budget) (<= (* gain error) budget)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance lw-pfi-multiply-order (a error) (b step) (factor gain)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pfi-left-commutes lw-pfi-left-distributes lw-pfi-fold-constants lw-pfi-times-negative lw-pfi-negative-times lw-pfi-zero-times lw-pfi-minus-one lw-pfi-double-negative lw-pfi-add-cancel lw-pfi-double lw-pfi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-factor-square-index
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
               (posp count) (<= (* 2 (/ count)) (lw-polynomial-factor-mesh-step roots leading)))
  (equal (lw-ray-polygon-index (lw-polynomial-factor-path-values roots leading (lw-unit-square-boundary count)))
         (lw-unit-square-factor-count roots)))
 :hints (("Goal" :induct (lw-unit-square-roots-awayp roots)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-unit-square-roots-awayp) lw-unit-square-roots-awayp lw-unit-square-factor-count lw-polynomial-constant-factor-path-index lw-pfi-product-rational lw-pfi-inverse-rational endp lw-pfi-left-commutes lw-pfi-left-distributes lw-pfi-fold-constants lw-pfi-times-negative lw-pfi-negative-times lw-pfi-zero-times lw-pfi-minus-one lw-pfi-double-negative lw-pfi-add-cancel lw-pfi-double lw-pfi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use
            (lw-polynomial-factor-mesh-step-data lw-polynomial-factor-mesh-step-bounds
             (:instance lw-polynomial-factor-lower-data (roots (cdr roots)))
             (:instance lw-polynomial-factor-upper-data (roots (cdr roots)))
             (:instance lw-polynomial-factor-lipschitz-data (roots (cdr roots)))
             (:instance lw-unit-square-roots-away-data (roots (cdr roots)))
             (:instance lw-unit-square-root-gap-data (root (car roots)))
             (:instance lw-pfi-cap-data (root (car roots)))
             lw-unit-square-boundary-points lw-unit-square-boundary-data lw-unit-square-boundary-step
             (:instance lw-unit-square-linear-boundary-annulus (root (car roots)))
             (:instance lw-ray-translate-points-data (root (car roots)) (points (lw-unit-square-boundary count)))
             (:instance lw-polynomial-factor-path-annulus (roots (cdr roots)) (points (lw-unit-square-boundary count)))
             (:instance lw-polynomial-factor-path-data (roots (cdr roots)) (points (lw-unit-square-boundary count)))
             (:instance lw-polynomial-factor-path-closed (roots (cdr roots)) (points (lw-unit-square-boundary count)))
             (:instance lw-ray-translate-path-step (root (car roots)) (points (lw-unit-square-boundary count)) (error (* 2 (/ count))))
             (:instance lw-polynomial-factor-path-step (roots (cdr roots)) (points (lw-unit-square-boundary count)) (error (* 2 (/ count))))
             (:instance lw-pfi-transfer (error (* 2 (/ count)))
               (step (lw-polynomial-factor-mesh-step roots leading))
               (gain (lw-polynomial-factor-lipschitz (cdr roots) leading)) (budget (lw-ray-product-step-budget
          (lw-unit-square-root-gap (car roots)) (lw-unit-square-root-cap (car roots))
          (lw-polynomial-factor-lower (cdr roots) leading) (lw-polynomial-factor-upper (cdr roots) leading))))
             (:instance lw-ray-path-step-enlarge (points (lw-ray-translate-points (car roots) (lw-unit-square-boundary count))) (delta (* 2 (/ count))) (larger (lw-ray-product-step-budget
          (lw-unit-square-root-gap (car roots)) (lw-unit-square-root-cap (car roots))
          (lw-polynomial-factor-lower (cdr roots) leading) (lw-polynomial-factor-upper (cdr roots) leading))))
             (:instance lw-ray-path-step-enlarge (points (lw-polynomial-factor-path-values (cdr roots) leading (lw-unit-square-boundary count)))
               (delta (* (lw-polynomial-factor-lipschitz (cdr roots) leading) (* 2 (/ count)))) (larger (lw-ray-product-step-budget
          (lw-unit-square-root-gap (car roots)) (lw-unit-square-root-cap (car roots))
          (lw-polynomial-factor-lower (cdr roots) leading) (lw-polynomial-factor-upper (cdr roots) leading))))
             (:instance lw-ray-product-index-at-computed-step
               (left (lw-ray-translate-points (car roots) (lw-unit-square-boundary count))) (right (lw-polynomial-factor-path-values (cdr roots) leading (lw-unit-square-boundary count)))
               (lower-left (lw-unit-square-root-gap (car roots))) (upper-left (lw-unit-square-root-cap (car roots)))
               (lower-right (lw-polynomial-factor-lower (cdr roots) leading)) (upper-right (lw-polynomial-factor-upper (cdr roots) leading)))
             (:instance lw-unit-square-translated-boundary-index (root (car roots)))
             (:instance lw-pfi-head-product (points (lw-unit-square-boundary count))))
            :do-not-induct t))))

(defun lw-polynomial-factor-mesh-count (roots leading)
 (* 4 (lw-unit-square-mesh-factor (lw-polynomial-factor-mesh-step roots leading))))

(defthm lw-polynomial-factor-mesh-count-data
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading) (not (equal leading (cons 0 0))))
  (and (posp (lw-polynomial-factor-mesh-count roots leading))
       (<= (* 2 (/ (lw-polynomial-factor-mesh-count roots leading)))
           (lw-polynomial-factor-mesh-step roots leading))))
 :hints (("Goal"
  :use (lw-polynomial-factor-mesh-step-data
        (:instance lw-unit-square-mesh-factor-data (error (lw-polynomial-factor-mesh-step roots leading))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-mesh-count lw-pfi-left-commutes lw-pfi-left-distributes lw-pfi-fold-constants lw-pfi-times-negative lw-pfi-negative-times lw-pfi-zero-times lw-pfi-minus-one lw-pfi-double-negative lw-pfi-add-cancel lw-pfi-double lw-pfi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-factor-computed-winding
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading) (not (equal leading (cons 0 0))))
  (let ((index (lw-ray-polygon-index
                (lw-polynomial-factor-path-values roots leading
                 (lw-unit-square-boundary (lw-polynomial-factor-mesh-count roots leading))))))
   (and (posp (lw-polynomial-factor-mesh-count roots leading))
        (equal index (lw-unit-square-factor-count roots))
        (<= 0 index) (<= index (len roots)))))
 :hints (("Goal"
  :use (lw-polynomial-factor-mesh-count-data lw-unit-square-factor-count-data
        (:instance lw-polynomial-factor-square-index (count (lw-polynomial-factor-mesh-count roots leading))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pfi-left-commutes lw-pfi-left-distributes lw-pfi-fold-constants lw-pfi-times-negative lw-pfi-negative-times lw-pfi-zero-times lw-pfi-minus-one lw-pfi-double-negative lw-pfi-add-cancel lw-pfi-double lw-pfi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
