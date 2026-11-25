; Exact polynomial cell indices and their sum over the actual grid.
(in-package "ACL2")
(include-book "polynomial-grid")
(local (in-theory (disable lw-polynomial-grid lw-polynomial-grid-row lw-polynomial-grid-rows lw-polynomial-grid-value
 lw-ray-quadrilateral-index lw-ray-crossing lw-ray-row-strip-index lw-ray-grid-cell-index)))
(local (defthm lw-pci-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pci-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pci-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pci-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pci-times-negative (a b) (b a)))
                 :in-theory (disable lw-pci-times-negative)))))

(local (defthm lw-pci-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pci-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pci-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pci-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pci-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pci-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pci-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pci-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pci-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pci-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pci-left-commutes)))))
(defun lw-polynomial-cell-index (coefficients anchor side count row column)
 (lw-ray-quadrilateral-index
  (lw-polynomial-grid-value coefficients anchor side count row column)
  (lw-polynomial-grid-value coefficients anchor side count row (+ 1 column))
  (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) (+ 1 column))
  (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) column)))
(defun lw-polynomial-cell-row-index (coefficients anchor side count row column remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) 0
 (+ (lw-polynomial-cell-index coefficients anchor side count row column)
    (lw-polynomial-cell-row-index coefficients anchor side count row (+ 1 column) (- remaining 1)))))
(defun lw-polynomial-cell-rows-index (coefficients anchor side count row remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) 0
 (+ (lw-polynomial-cell-row-index coefficients anchor side count row 0 count)
    (lw-polynomial-cell-rows-index coefficients anchor side count (+ 1 row) (- remaining 1)))))
(defun lw-polynomial-all-cell-index (coefficients anchor side count)
 (lw-polynomial-cell-rows-index coefficients anchor side count 0 count))
(local (in-theory (disable lw-polynomial-cell-index lw-polynomial-cell-row-index lw-polynomial-cell-rows-index lw-polynomial-all-cell-index)))

(defthm lw-polynomial-cell-index-integer
 (integerp (lw-polynomial-cell-index coefficients anchor side count row column))
 :hints (("Goal"
 :use ((:instance lw-ray-crossing-data
  (a (lw-polynomial-grid-value coefficients anchor side count row column))
  (b (lw-polynomial-grid-value coefficients anchor side count row (+ 1 column))))
 (:instance lw-ray-crossing-data
 (a (lw-polynomial-grid-value coefficients anchor side count row (+ 1 column)))
 (b (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) (+ 1 column))))
 (:instance lw-ray-crossing-data
 (a (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) (+ 1 column)))
 (b (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) column)))
 (:instance lw-ray-crossing-data
 (a (lw-polynomial-grid-value coefficients anchor side count (+ 1 row) column))
 (b (lw-polynomial-grid-value coefficients anchor side count row column))) )
 :in-theory (union-theories
 '(lw-polynomial-cell-index lw-ray-quadrilateral-index lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-polynomial-cell-row-index-integer
 (integerp (lw-polynomial-cell-row-index coefficients anchor side count row column remaining))
 :hints (("Goal" :induct (lw-polynomial-cell-row-index coefficients anchor side count row column remaining)
 :in-theory (union-theories
 '(lw-polynomial-cell-row-index lw-polynomial-cell-index-integer lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-polynomial-cell-rows-index-integer
 (integerp (lw-polynomial-cell-rows-index coefficients anchor side count row remaining))
 :hints (("Goal" :induct (lw-polynomial-cell-rows-index coefficients anchor side count row remaining)
 :in-theory (union-theories
 '(lw-polynomial-cell-rows-index lw-polynomial-cell-row-index-integer lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(local (defthm lw-pci-heads
 (and (equal (consp (lw-polynomial-grid-row coefficients anchor side count row column remaining)) (not (zp remaining)))
      (equal (consp (lw-polynomial-grid-rows coefficients anchor side count row remaining)) (not (zp remaining)))
      (implies (not (zp remaining))
       (and (equal (car (lw-polynomial-grid-row coefficients anchor side count row column remaining))
                   (lw-polynomial-grid-value coefficients anchor side count row column))
            (equal (car (lw-polynomial-grid-rows coefficients anchor side count row remaining))
                   (lw-polynomial-grid-row coefficients anchor side count row 0 (+ 1 count))))))
 :hints (("Goal" :expand ((lw-polynomial-grid-row coefficients anchor side count row column remaining)
 (lw-polynomial-grid-rows coefficients anchor side count row remaining))
 :do-not-induct t :in-theory (union-theories
 '(lw-polynomial-grid-row lw-polynomial-grid-rows lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pci-grid-zeros
 (and (equal (lw-polynomial-grid-row coefficients anchor side count row column 0) nil)
      (equal (lw-polynomial-grid-rows coefficients anchor side count row 0) nil))
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-grid-row lw-polynomial-grid-rows lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pci-grid-single-row
 (equal (lw-polynomial-grid-row coefficients anchor side count row column 1)
 (list (lw-polynomial-grid-value coefficients anchor side count row column)))
 :hints (("Goal" :expand ((lw-polynomial-grid-row coefficients anchor side count row column 1))
 :in-theory (union-theories
 '(lw-pci-grid-zeros lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pci-grid-single-rows
 (equal (lw-polynomial-grid-rows coefficients anchor side count row 1)
 (list (lw-polynomial-grid-row coefficients anchor side count row 0 (+ 1 count))))
 :hints (("Goal" :expand ((lw-polynomial-grid-rows coefficients anchor side count row 1))
 :in-theory (union-theories
 '(lw-pci-grid-zeros lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-cell-row-index-as-strip
 (implies (and (natp column) (natp remaining))
 (equal
 (lw-ray-row-strip-index
  (lw-polynomial-grid-row coefficients anchor side count row column (+ 1 remaining))
  (lw-polynomial-grid-row coefficients anchor side count (+ 1 row) column (+ 1 remaining)))
 (lw-polynomial-cell-row-index coefficients anchor side count row column remaining)))
 :hints (("Goal" :induct (lw-polynomial-cell-row-index coefficients anchor side count row column remaining)
 :expand ((lw-polynomial-grid-row coefficients anchor side count row column (+ 1 remaining))
          (lw-polynomial-grid-row coefficients anchor side count (+ 1 row) column (+ 1 remaining)))
 :in-theory (union-theories
 '(lw-polynomial-cell-row-index lw-polynomial-cell-index lw-ray-row-strip-index lw-pci-heads lw-pci-grid-zeros lw-pci-grid-single-row lw-polynomial-cell-index-integer lw-polynomial-cell-row-index-integer fold-consts-in-+ endp lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-cell-rows-index-as-grid
 (implies (and (posp count) (natp row) (natp remaining))
 (equal (lw-ray-grid-cell-index (lw-polynomial-grid-rows coefficients anchor side count row (+ 1 remaining)))
        (lw-polynomial-cell-rows-index coefficients anchor side count row remaining)))
 :hints (("Goal" :induct (lw-polynomial-cell-rows-index coefficients anchor side count row remaining)
 :expand ((lw-polynomial-grid-rows coefficients anchor side count row (+ 1 remaining)))
 :in-theory (union-theories
 '(lw-polynomial-cell-rows-index lw-ray-grid-cell-index lw-pci-heads lw-polynomial-cell-row-index-as-strip lw-pci-grid-zeros lw-pci-grid-single-rows lw-polynomial-cell-row-index-integer lw-polynomial-cell-rows-index-integer fold-consts-in-+ endp lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-all-cell-index-boundary
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (posp count))
 (equal (lw-polynomial-all-cell-index coefficients anchor side count)
        (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side count))))
 :hints (("Goal"
 :use (lw-polynomial-grid-data
       (:instance lw-polynomial-cell-rows-index-as-grid (row 0) (remaining count))
       (:instance lw-ray-grid-internal-edges-cancel (rows (lw-polynomial-grid coefficients anchor side count)) (width (+ 1 count))))
 :in-theory (union-theories
 '(lw-polynomial-grid lw-polynomial-all-cell-index lw-pci-left-commutes lw-pci-left-distributes lw-pci-fold-constants lw-pci-times-negative lw-pci-negative-times lw-pci-zero-times lw-pci-minus-one lw-pci-double-negative lw-pci-add-cancel lw-pci-double lw-pci-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
