; The retained small-value cover carries the entire finite boundary index.
(in-package "ACL2")
(include-book "polynomial-sublevel-cover")
(include-book "polynomial-cell-index")
(local (in-theory (disable lw-complexp lw-complex-diskp lw-complex-sub lw-complex-norm-square lw-complex-dot
 lw-complex-positive-halfplanep lw-ray-quadrilateral-index lw-polynomial-grid-value lw-polynomial-grid-point
 lw-polynomial-grid-step lw-polynomial-grid-radius lw-polynomial-lipschitz-cap lw-polynomial-cell-activep
 lw-polynomial-cell-variation lw-polynomial-cell-index lw-polynomial-cell-row-index lw-polynomial-cell-rows-index
 lw-polynomial-all-cell-index lw-polynomial-sublevel-cover-row lw-polynomial-sublevel-cover-rows lw-polynomial-sublevel-cover)))
(local (defthm lw-pco-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pco-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pco-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pco-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pco-times-negative (a b) (b a)))
                 :in-theory (disable lw-pco-times-negative)))))

(local (defthm lw-pco-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pco-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pco-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pco-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pco-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pco-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pco-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pco-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pco-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pco-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pco-left-commutes)))))
(defun lw-polynomial-cover-index (coefficients anchor side count addresses)
 (if (endp addresses) 0
 (+ (lw-polynomial-cell-index coefficients anchor side count (caar addresses) (cdar addresses))
    (lw-polynomial-cover-index coefficients anchor side count (cdr addresses)))))
(local (in-theory (disable lw-polynomial-cover-index)))

(defthm lw-polynomial-cover-index-integer
 (integerp (lw-polynomial-cover-index coefficients anchor side count addresses))
 :hints (("Goal" :induct (lw-polynomial-cover-index coefficients anchor side count addresses)
 :in-theory (union-theories
 '(lw-polynomial-cover-index lw-polynomial-cell-index-integer endp lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-polynomial-cover-index-append
 (equal (lw-polynomial-cover-index coefficients anchor side count (append left right))
 (+ (lw-polynomial-cover-index coefficients anchor side count left)
    (lw-polynomial-cover-index coefficients anchor side count right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(lw-polynomial-cover-index lw-polynomial-cover-index-integer lw-polynomial-cell-index-integer append endp lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pco-cell-zero
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d) (rationalp epsilon) (< 0 epsilon)
 (not (lw-complex-diskp a epsilon))
 (lw-complex-diskp (lw-complex-sub b a) epsilon)
 (lw-complex-diskp (lw-complex-sub c a) epsilon)
 (lw-complex-diskp (lw-complex-sub d a) epsilon))
 (equal (lw-ray-quadrilateral-index a b c d) 0))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-norm-square (point a) (radius epsilon))
       (:instance lw-complex-dot-self (point a))
       (:instance lw-pco-positive-product (a epsilon) (b epsilon))
       (:instance lw-complex-disk-positive-halfplane (anchor a) (point b) (radius epsilon))
       (:instance lw-complex-disk-positive-halfplane (anchor a) (point c) (radius epsilon))
       (:instance lw-complex-disk-positive-halfplane (anchor a) (point d) (radius epsilon))
       (:instance lw-ray-quadrilateral-halfplane-zero (h a)))
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-polynomial-inactive-cell-index-zero
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp count) (natp row) (< row count) (natp column) (< column count) (rationalp epsilon) (< 0 epsilon)
 (not (lw-polynomial-cell-activep coefficients anchor side count epsilon row column)))
 (equal (lw-polynomial-cell-index coefficients anchor side count row column) 0))
 :hints (("Goal"
 :use (lw-polynomial-cell-variation-data
 (:instance lw-polynomial-grid-value-rational (row row) (column column))
 (:instance lw-polynomial-grid-value-rational (row row) (column (+ 1 column)))
 (:instance lw-polynomial-grid-value-rational (row (+ 1 row)) (column (+ 1 column)))
 (:instance lw-polynomial-grid-value-rational (row (+ 1 row)) (column column))
 (:instance lw-polynomial-grid-cell-variation (dr 0) (dc 1) (epsilon (+ epsilon (lw-polynomial-cell-variation coefficients anchor side count))))
 (:instance lw-polynomial-grid-cell-variation (dr 1) (dc 1) (epsilon (+ epsilon (lw-polynomial-cell-variation coefficients anchor side count))))
 (:instance lw-polynomial-grid-cell-variation (dr 1) (dc 0) (epsilon (+ epsilon (lw-polynomial-cell-variation coefficients anchor side count))))
 (:instance lw-pco-cell-zero
  (a (lw-polynomial-grid-value coefficients anchor side count row column)) (b (lw-polynomial-grid-value coefficients anchor side count row (+ 1 column)))
  (c (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) (+ 1 column))) (d (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) column)) (epsilon (+ epsilon (lw-polynomial-cell-variation coefficients anchor side count)))))
 :in-theory (union-theories
 '(lw-polynomial-cell-activep lw-polynomial-cell-index lw-polynomial-cell-variation lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-nonzero-cell-active
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp count) (natp row) (< row count) (natp column) (< column count) (rationalp epsilon) (< 0 epsilon)
 (not (equal (lw-polynomial-cell-index coefficients anchor side count row column) 0)))
 (lw-polynomial-cell-activep coefficients anchor side count epsilon row column))
 :hints (("Goal" :use lw-polynomial-inactive-cell-index-zero :in-theory (union-theories
 '( lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-cover-row-index-conservation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp count) (natp row) (< row count) (natp column) (natp remaining) (<= (+ column remaining) count)
 (rationalp epsilon) (< 0 epsilon))
 (equal (lw-polynomial-cover-index coefficients anchor side count
  (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining))
 (lw-polynomial-cell-row-index coefficients anchor side count row column remaining)))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-row coefficients anchor side count epsilon row column remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-row lw-polynomial-cover-index lw-polynomial-cell-row-index lw-polynomial-cell-index-integer lw-polynomial-cell-row-index-integer lw-polynomial-cover-index-integer fold-consts-in-+ endp lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use (lw-polynomial-inactive-cell-index-zero) :do-not-induct t))))

(defthm lw-polynomial-cover-rows-index-conservation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp count) (natp row) (natp remaining) (<= (+ row remaining) count) (rationalp epsilon) (< 0 epsilon))
 (equal (lw-polynomial-cover-index coefficients anchor side count
  (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining))
 (lw-polynomial-cell-rows-index coefficients anchor side count row remaining)))
 :hints (("Goal" :induct (lw-polynomial-sublevel-cover-rows coefficients anchor side count epsilon row remaining)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover-rows lw-polynomial-cover-index-append lw-polynomial-cell-rows-index lw-polynomial-cell-row-index-integer lw-polynomial-cell-rows-index-integer lw-polynomial-cover-index lw-polynomial-cover-index-integer fold-consts-in-+ endp lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-cover-row-index-conservation (column 0) (remaining count))) :do-not-induct t))))

(defthm lw-polynomial-sublevel-cover-index-conservation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp count) (rationalp epsilon) (< 0 epsilon))
 (equal (lw-polynomial-cover-index coefficients anchor side count (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))
 (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side count))))
 :hints (("Goal"
 :use ((:instance lw-polynomial-cover-rows-index-conservation (row 0) (remaining count))
       lw-polynomial-all-cell-index-boundary)
 :in-theory (union-theories
 '(lw-polynomial-sublevel-cover lw-polynomial-all-cell-index lw-pco-left-commutes lw-pco-left-distributes lw-pco-fold-constants lw-pco-times-negative lw-pco-negative-times lw-pco-zero-times lw-pco-minus-one lw-pco-double-negative lw-pco-add-cancel lw-pco-double lw-pco-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
