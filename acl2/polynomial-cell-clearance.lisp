; Computed polynomial clearance on every rational point of a grid cell.
(in-package "ACL2")
(include-book "square-cells")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp lw-complex-polynomial
 lw-polynomial-grid-point lw-polynomial-grid-step lw-polynomial-grid-radius lw-polynomial-grid-value
 lw-polynomial-lipschitz-cap lw-square-containsp lw-square-cell-containsp)))
(local (defthm lw-pcl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcl-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcl-times-negative)))))

(local (defthm lw-pcl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcl-left-commutes)))))
(defun lw-polynomial-cell-variation (coefficients anchor side count)
 (* 2 (lw-polynomial-grid-step side count)
      (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))))
(defun lw-polynomial-cell-activep (coefficients anchor side count epsilon row column)
 (lw-complex-diskp (lw-polynomial-grid-value coefficients anchor side count row column)
 (+ epsilon (lw-polynomial-cell-variation coefficients anchor side count))))
(local (in-theory (disable lw-polynomial-cell-variation lw-polynomial-cell-activep)))

(defthm lw-polynomial-cell-variation-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
 (rationalp side) (< 0 side) (posp count))
 (and (rationalp (lw-polynomial-cell-variation coefficients anchor side count))
      (<= 0 (lw-polynomial-cell-variation coefficients anchor side count))))
 :hints (("Goal"
 :use (lw-polynomial-grid-radius-data lw-polynomial-grid-step-data
       (:instance lw-polynomial-lipschitz-cap-data (bound (lw-polynomial-grid-radius anchor side))))
 :in-theory (union-theories
 '(lw-polynomial-cell-variation lw-pcl-left-commutes lw-pcl-left-distributes lw-pcl-fold-constants lw-pcl-times-negative lw-pcl-negative-times lw-pcl-zero-times lw-pcl-minus-one lw-pcl-double-negative lw-pcl-add-cancel lw-pcl-double lw-pcl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t)))

(defthm lw-polynomial-cell-variation-bound
 (implies (and (lw-complex-coefficientsp coefficients)
 (lw-square-cell-containsp anchor side count row column point))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                  (lw-polynomial-grid-value coefficients anchor side count row column))
  (lw-polynomial-cell-variation coefficients anchor side count)))
 :hints (("Goal"
 :use (lw-square-cell-in-square lw-square-contained-in-disk lw-square-cell-distance
       lw-polynomial-grid-point-bounds lw-polynomial-grid-radius-data lw-polynomial-grid-step-data
       (:instance lw-complex-polynomial-lipschitz
        (left point) (right (lw-polynomial-grid-point anchor side count row column))
        (bound (lw-polynomial-grid-radius anchor side)) (step (* 2 (lw-polynomial-grid-step side count)))))
 :in-theory (union-theories
 '(lw-square-cell-containsp lw-polynomial-cell-variation lw-polynomial-grid-value lw-pcl-left-commutes lw-pcl-left-distributes lw-pcl-fold-constants lw-pcl-times-negative lw-pcl-negative-times lw-pcl-zero-times lw-pcl-minus-one lw-pcl-double-negative lw-pcl-add-cancel lw-pcl-double lw-pcl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-pcl-small-other
 (implies (and (lw-complexp left) (lw-complexp right)
 (lw-complex-diskp (lw-complex-sub left right) radius) (lw-complex-diskp left epsilon))
 (lw-complex-diskp right (+ epsilon radius)))
 :hints (("Goal"
 :use ((:instance lw-complex-sub-disk (left left) (right (lw-complex-sub left right)) (radius epsilon) (other-radius radius))
       (:instance lw-complex-subtract-cancel (a left) (b right)))
 :in-theory (union-theories
 '( lw-pcl-left-commutes lw-pcl-left-distributes lw-pcl-fold-constants lw-pcl-times-negative lw-pcl-negative-times lw-pcl-zero-times lw-pcl-minus-one lw-pcl-double-negative lw-pcl-add-cancel lw-pcl-double lw-pcl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-polynomial-small-value-forces-active
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp epsilon) (<= 0 epsilon)
 (lw-square-cell-containsp anchor side count row column point)
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) epsilon))
 (lw-polynomial-cell-activep coefficients anchor side count epsilon row column))
 :hints (("Goal"
 :use (lw-polynomial-cell-variation-bound
       (:instance lw-complex-polynomial-rational (point point) (offset 0))
       lw-polynomial-grid-value-rational
       (:instance lw-pcl-small-other
        (left (lw-complex-polynomial coefficients point 0))
        (right (lw-polynomial-grid-value coefficients anchor side count row column))
        (radius (lw-polynomial-cell-variation coefficients anchor side count))))
 :in-theory (union-theories
 '(lw-polynomial-cell-activep lw-square-cell-containsp lw-pcl-left-commutes lw-pcl-left-distributes lw-pcl-fold-constants lw-pcl-times-negative lw-pcl-negative-times lw-pcl-zero-times lw-pcl-minus-one lw-pcl-double-negative lw-pcl-add-cancel lw-pcl-double lw-pcl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-inactive-cell-excludes-small
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp epsilon) (<= 0 epsilon)
 (lw-square-cell-containsp anchor side count row column point)
 (not (lw-polynomial-cell-activep coefficients anchor side count epsilon row column)))
 (not (lw-complex-diskp (lw-complex-polynomial coefficients point 0) epsilon)))
 :hints (("Goal" :use lw-polynomial-small-value-forces-active
 :in-theory (union-theories
 '( lw-pcl-left-commutes lw-pcl-left-distributes lw-pcl-fold-constants lw-pcl-times-negative lw-pcl-negative-times lw-pcl-zero-times lw-pcl-minus-one lw-pcl-double-negative lw-pcl-add-cancel lw-pcl-double lw-pcl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-active-cell-value-bound
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp epsilon) (<= 0 epsilon)
 (lw-square-cell-containsp anchor side count row column point)
 (lw-polynomial-cell-activep coefficients anchor side count epsilon row column))
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
 (+ epsilon (* 2 (lw-polynomial-cell-variation coefficients anchor side count)))))
 :hints (("Goal"
 :use (lw-polynomial-cell-variation-bound
       (:instance lw-complex-polynomial-rational (point point) (offset 0))
       lw-polynomial-grid-value-rational
       (:instance lw-complex-difference-symmetric
        (left (lw-complex-polynomial coefficients point 0))
        (right (lw-polynomial-grid-value coefficients anchor side count row column))
        (radius (lw-polynomial-cell-variation coefficients anchor side count)))
       (:instance lw-pcl-small-other
        (left (lw-polynomial-grid-value coefficients anchor side count row column))
        (right (lw-complex-polynomial coefficients point 0))
        (epsilon (+ epsilon (lw-polynomial-cell-variation coefficients anchor side count)))
        (radius (lw-polynomial-cell-variation coefficients anchor side count))))
 :in-theory (union-theories
 '(lw-polynomial-cell-activep lw-square-cell-containsp lw-polynomial-cell-variation-data fold-consts-in-+ lw-pcl-left-commutes lw-pcl-left-distributes lw-pcl-fold-constants lw-pcl-times-negative lw-pcl-negative-times lw-pcl-zero-times lw-pcl-minus-one lw-pcl-double-negative lw-pcl-add-cancel lw-pcl-double lw-pcl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
