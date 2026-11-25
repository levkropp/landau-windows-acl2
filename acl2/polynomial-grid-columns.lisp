; Actual top rows and side columns of the rectangular polynomial grid.
(in-package "ACL2")
(include-book "polynomial-grid")
(local (in-theory (disable lw-polynomial-grid-row lw-polynomial-grid-rows lw-polynomial-grid-value
 lw-ray-row-last lw-ray-path-last lw-ray-grid-last-row lw-ray-grid-left lw-ray-grid-right)))
(local (defthm lw-pgc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pgc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pgc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pgc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pgc-times-negative (a b) (b a)))
                 :in-theory (disable lw-pgc-times-negative)))))

(local (defthm lw-pgc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pgc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pgc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pgc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pgc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pgc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pgc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pgc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pgc-left-commutes)))))
(defun lw-polynomial-grid-column (coefficients anchor side count column row remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (lw-polynomial-grid-value coefficients anchor side count row column)
       (lw-polynomial-grid-column coefficients anchor side count column (+ 1 row) (- remaining 1)))))
(local (in-theory (disable lw-polynomial-grid-column)))

(local (defthm lw-pgc-heads
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
 '(lw-polynomial-grid-row lw-polynomial-grid-rows lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pgc-row-last-cons
 (equal (lw-ray-row-last (cons current points)) (if (endp points) current (lw-ray-row-last points)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-row-last lw-ray-path-last endp lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pgc-grid-last-cons
 (equal (lw-ray-grid-last-row (cons current rows)) (if (endp rows) current (lw-ray-grid-last-row rows)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-last-row lw-ray-path-last endp lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pgc-zeros
 (and (equal (lw-polynomial-grid-row coefficients anchor side count row column 0) nil)
      (equal (lw-polynomial-grid-rows coefficients anchor side count row 0) nil))
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-grid-row lw-polynomial-grid-rows lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pgc-single-row
 (equal (lw-polynomial-grid-row coefficients anchor side count row column 1)
 (list (lw-polynomial-grid-value coefficients anchor side count row column)))
 :hints (("Goal" :expand ((lw-polynomial-grid-row coefficients anchor side count row column 1))
 :in-theory (union-theories
 '(lw-pgc-zeros lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pgc-single-rows
 (equal (lw-polynomial-grid-rows coefficients anchor side count row 1)
 (list (lw-polynomial-grid-row coefficients anchor side count row 0 (+ 1 count))))
 :hints (("Goal" :expand ((lw-polynomial-grid-rows coefficients anchor side count row 1))
 :in-theory (union-theories
 '(lw-pgc-zeros lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-grid-row-last
 (implies (and (natp column) (posp remaining))
 (equal (lw-ray-row-last (lw-polynomial-grid-row coefficients anchor side count row column remaining))
        (lw-polynomial-grid-value coefficients anchor side count row (+ column remaining -1))))
 :hints (("Goal" :induct (lw-polynomial-grid-row coefficients anchor side count row column remaining)
 :expand ((lw-polynomial-grid-row coefficients anchor side count row column remaining))
 :in-theory (union-theories
 '((:induction lw-polynomial-grid-row) lw-pgc-heads lw-pgc-row-last-cons lw-pgc-zeros lw-pgc-single-row fold-consts-in-+ endp lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-grid-rows-last
 (implies (and (natp row) (posp remaining))
 (equal (lw-ray-grid-last-row (lw-polynomial-grid-rows coefficients anchor side count row remaining))
        (lw-polynomial-grid-row coefficients anchor side count (+ row remaining -1) 0 (+ 1 count))))
 :hints (("Goal" :induct (lw-polynomial-grid-rows coefficients anchor side count row remaining)
 :expand ((lw-polynomial-grid-rows coefficients anchor side count row remaining))
 :in-theory (union-theories
 '((:induction lw-polynomial-grid-rows) lw-pgc-heads lw-pgc-grid-last-cons lw-pgc-zeros lw-pgc-single-rows fold-consts-in-+ endp lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-grid-left-column
 (implies (and (posp count) (natp row) (natp remaining))
 (equal (lw-ray-grid-left (lw-polynomial-grid-rows coefficients anchor side count row remaining))
        (lw-polynomial-grid-column coefficients anchor side count 0 row remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-rows coefficients anchor side count row remaining)
 :in-theory (union-theories
 '(lw-polynomial-grid-rows lw-polynomial-grid-column lw-ray-grid-left lw-pgc-heads endp lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-grid-right-column
 (implies (and (posp count) (natp row) (natp remaining))
 (equal (lw-ray-grid-right (lw-polynomial-grid-rows coefficients anchor side count row remaining))
        (lw-polynomial-grid-column coefficients anchor side count count row remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-rows coefficients anchor side count row remaining)
 :in-theory (union-theories
 '(lw-polynomial-grid-rows lw-polynomial-grid-column lw-ray-grid-right lw-polynomial-grid-row-last fold-consts-in-+ endp lw-pgc-left-commutes lw-pgc-left-distributes lw-pgc-fold-constants lw-pgc-times-negative lw-pgc-negative-times lw-pgc-zero-times lw-pgc-minus-one lw-pgc-double-negative lw-pgc-add-cancel lw-pgc-double lw-pgc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
