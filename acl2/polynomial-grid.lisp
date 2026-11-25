; Exact rational polynomial samples on a finite square grid.
(in-package "ACL2")
(include-book "grid-root-search")
(include-book "polynomial-lipschitz")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
 lw-complex-diskp lw-diskp lw-complex-norm-square lw-complex-l1 lw-complex-polynomial lw-complex-coefficientsp
 lw-ray-gridp lw-ray-grid-near-check lw-ray-row-near-check lw-ray-grid-small-search lw-ray-pointsp lw-polynomial-lipschitz-cap)))
(local (defthm lw-pgr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pgr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pgr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pgr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pgr-times-negative (a b) (b a)))
                 :in-theory (disable lw-pgr-times-negative)))))

(local (defthm lw-pgr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pgr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pgr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pgr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pgr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pgr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pgr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pgr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pgr-left-commutes)))))
(defun lw-polynomial-grid-radius (anchor side) (+ 1 (lw-complex-l1 anchor) (* 2 side)))
(defun lw-polynomial-grid-step (side count) (* side (/ count)))
(defun lw-polynomial-grid-point (anchor side count row column)
 (cons (+ (car anchor) (* (lw-polynomial-grid-step side count) column))
       (+ (cdr anchor) (* (lw-polynomial-grid-step side count) row))))
(defun lw-polynomial-grid-value (coefficients anchor side count row column)
 (lw-complex-polynomial coefficients (lw-polynomial-grid-point anchor side count row column) 0))
(defun lw-polynomial-grid-row (coefficients anchor side count row column remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (lw-polynomial-grid-value coefficients anchor side count row column)
       (lw-polynomial-grid-row coefficients anchor side count row (+ 1 column) (- remaining 1)))))
(defun lw-polynomial-grid-rows (coefficients anchor side count row remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (lw-polynomial-grid-row coefficients anchor side count row 0 (+ 1 count))
       (lw-polynomial-grid-rows coefficients anchor side count (+ 1 row) (- remaining 1)))))
(defun lw-polynomial-grid (coefficients anchor side count)
 (lw-polynomial-grid-rows coefficients anchor side count 0 (+ 1 count)))

(local (in-theory (disable lw-polynomial-grid-radius lw-polynomial-grid-step lw-polynomial-grid-point lw-polynomial-grid-value lw-polynomial-grid-row lw-polynomial-grid-rows lw-polynomial-grid)))

(defthm lw-polynomial-grid-step-data
 (implies (and (rationalp side) (< 0 side) (posp count))
 (and (rationalp (lw-polynomial-grid-step side count)) (< 0 (lw-polynomial-grid-step side count))))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-positive (value count))
       (:instance lw-pgr-positive-product (a side) (b (/ count))))
 :in-theory (union-theories
 '(lw-polynomial-grid-step lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-grid-radius-data
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side))
 (and (rationalp (lw-polynomial-grid-radius anchor side)) (< 0 (lw-polynomial-grid-radius anchor side))))
 :hints (("Goal" :use ((:instance lw-complex-l1-bound (point anchor)))
 :in-theory (union-theories
 '(lw-polynomial-grid-radius lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(local (defthm lw-pgr-coordinate
 (implies (and (rationalp side) (< 0 side) (posp count) (natp index) (<= index count))
 (and (rationalp (* (lw-polynomial-grid-step side count) index))
      (<= 0 (* (lw-polynomial-grid-step side count) index))
      (<= (* (lw-polynomial-grid-step side count) index) side)))
 :hints (("Goal"
 :use ((:instance lw-positive-division-bound (numerator (* side index)) (divisor count) (bound side))
       (:instance lw-pgr-multiply-order (a index) (b count) (factor side)))
 :in-theory (union-theories
 '(lw-polynomial-grid-step lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-pgr-abs-add
 (implies (and (rationalp value) (rationalp shift) (<= 0 shift) (rationalp side) (<= shift side))
 (<= (abs (+ value shift)) (+ (abs value) side)))
 :hints (("Goal" :in-theory (union-theories
 '(abs lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-polynomial-grid-point-rational
 (implies (and (lw-complexp anchor) (rationalp side) (posp count) (natp row) (natp column))
 (lw-complexp (lw-polynomial-grid-point anchor side count row column)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-grid-point lw-polynomial-grid-step lw-complexp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-grid-point-bounds
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
 (natp row) (<= row count) (natp column) (<= column count))
 (let ((point (lw-polynomial-grid-point anchor side count row column)))
 (and (lw-complexp point)
      (<= (car anchor) (car point)) (<= (car point) (+ (car anchor) side))
      (<= (cdr anchor) (cdr point)) (<= (cdr point) (+ (cdr anchor) side))
      (lw-complex-diskp point (lw-polynomial-grid-radius anchor side)))))
 :hints (("Goal"
 :use (lw-polynomial-grid-point-rational lw-polynomial-grid-radius-data
       (:instance lw-pgr-coordinate (index row))
       (:instance lw-pgr-coordinate (index column))
       (:instance lw-pgr-abs-add (value (car anchor)) (shift (* (lw-polynomial-grid-step side count) column)))
       (:instance lw-pgr-abs-add (value (cdr anchor)) (shift (* (lw-polynomial-grid-step side count) row)))
       (:instance lw-complex-l1-bound (point (lw-polynomial-grid-point anchor side count row column)))
       (:instance lw-complex-disk-enlarge (point (lw-polynomial-grid-point anchor side count row column))
        (radius (lw-complex-l1 (lw-polynomial-grid-point anchor side count row column))) (cap (lw-polynomial-grid-radius anchor side))))
 :in-theory (union-theories
 '(lw-polynomial-grid-point lw-polynomial-grid-radius lw-complexp lw-complex-l1 lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-grid-point-cell-distance
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count) (natp row) (natp column)
 (or (equal dr 0) (equal dr 1)) (or (equal dc 0) (equal dc 1)))
 (lw-complex-diskp (lw-complex-sub
 (lw-polynomial-grid-point anchor side count (+ row dr) (+ column dc))
 (lw-polynomial-grid-point anchor side count row column)) (* 2 (lw-polynomial-grid-step side count))))
 :hints (("Goal" :use (lw-polynomial-grid-step-data)
 :in-theory (union-theories
 '(lw-polynomial-grid-point lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)))

(defthm lw-polynomial-grid-value-rational
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (posp count) (natp row) (natp column))
 (lw-complexp (lw-polynomial-grid-value coefficients anchor side count row column)))
 :hints (("Goal"
 :use (lw-polynomial-grid-point-rational
       (:instance lw-complex-polynomial-rational (point (lw-polynomial-grid-point anchor side count row column)) (offset 0)))
 :in-theory (union-theories
 '(lw-polynomial-grid-value lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(defthm lw-polynomial-grid-cell-variation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp count) (natp row) (< row count) (natp column) (< column count)
 (or (equal dr 0) (equal dr 1)) (or (equal dc 0) (equal dc 1))
 (rationalp epsilon) (< 0 epsilon) (<= (* 2 (lw-polynomial-grid-step side count) (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) epsilon))
 (lw-complex-diskp (lw-complex-sub (lw-polynomial-grid-value coefficients anchor side count (+ row dr) (+ column dc)) (lw-polynomial-grid-value coefficients anchor side count row column)) epsilon))
 :hints (("Goal"
 :use (lw-polynomial-grid-radius-data lw-polynomial-grid-step-data lw-polynomial-grid-point-bounds
       (:instance lw-polynomial-grid-point-bounds (row (+ row dr)) (column (+ column dc)))
       lw-polynomial-grid-point-cell-distance
       (:instance lw-polynomial-lipschitz-cap-data (bound (lw-polynomial-grid-radius anchor side)))
       (:instance lw-complex-polynomial-lipschitz (bound (lw-polynomial-grid-radius anchor side)) (left (lw-polynomial-grid-point anchor side count (+ row dr) (+ column dc))) (right (lw-polynomial-grid-point anchor side count row column)) (step (* 2 (lw-polynomial-grid-step side count))))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-polynomial-grid-value coefficients anchor side count (+ row dr) (+ column dc)) (lw-polynomial-grid-value coefficients anchor side count row column))) (radius (* 2 (lw-polynomial-grid-step side count) (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side)))) (cap epsilon)))
 :in-theory (union-theories
 '(lw-polynomial-grid-value lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-grid-row-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (posp count)
 (natp row) (natp column) (natp remaining))
 (and (lw-ray-pointsp (lw-polynomial-grid-row coefficients anchor side count row column remaining))
      (equal (len (lw-polynomial-grid-row coefficients anchor side count row column remaining)) remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-row coefficients anchor side count row column remaining)
 :in-theory (union-theories
 '(lw-polynomial-grid-row lw-ray-pointsp len endp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp '(:use (lw-polynomial-grid-value-rational) :do-not-induct t)))
 :rule-classes nil)

(defthm lw-polynomial-grid-rows-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (posp count)
 (natp row) (natp remaining))
 (and (lw-ray-gridp (lw-polynomial-grid-rows coefficients anchor side count row remaining) (+ 1 count))
      (equal (len (lw-polynomial-grid-rows coefficients anchor side count row remaining)) remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-rows coefficients anchor side count row remaining)
 :in-theory (union-theories
 '(lw-polynomial-grid-rows lw-ray-gridp len endp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-grid-row-data (column 0) (remaining (+ 1 count))))
 :do-not-induct t)))
 :rule-classes nil)

(defthm lw-polynomial-grid-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (posp count))
 (and (lw-ray-gridp (lw-polynomial-grid coefficients anchor side count) (+ 1 count))
      (equal (len (lw-polynomial-grid coefficients anchor side count)) (+ 1 count))))
 :hints (("Goal" :use ((:instance lw-polynomial-grid-rows-data (row 0) (remaining (+ 1 count))))
 :in-theory (union-theories
 '(lw-polynomial-grid lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(local (defun lw-pgr-nth-induct (offset remaining index)
 (declare (xargs :measure (nfix index) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (zp remaining) (zp index)) (list offset remaining index)
 (lw-pgr-nth-induct (+ 1 offset) (- remaining 1) (- index 1)))))

(local (defthm lw-pgr-heads
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
 '(lw-polynomial-grid-row lw-polynomial-grid-rows lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-grid-row-nth
 (implies (and (natp column) (natp remaining) (natp index) (< index remaining))
 (equal (nth index (lw-polynomial-grid-row coefficients anchor side count row column remaining))
 (lw-polynomial-grid-value coefficients anchor side count row (+ column index))))
 :hints (("Goal" :induct (lw-pgr-nth-induct column remaining index)
 :in-theory (union-theories
 '(lw-pgr-heads (:induction lw-pgr-nth-induct) lw-polynomial-grid-row nth endp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-grid-rows-nth
 (implies (and (natp row) (natp remaining) (natp index) (< index remaining))
 (equal (nth index (lw-polynomial-grid-rows coefficients anchor side count row remaining))
 (lw-polynomial-grid-row coefficients anchor side count (+ row index) 0 (+ 1 count))))
 :hints (("Goal" :induct (lw-pgr-nth-induct row remaining index)
 :in-theory (union-theories
 '(lw-pgr-heads (:induction lw-pgr-nth-induct) lw-polynomial-grid-rows nth endp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-grid-access
 (implies (and (posp count) (natp row) (<= row count) (natp column) (<= column count))
 (equal (nth column (nth row (lw-polynomial-grid coefficients anchor side count)))
 (lw-polynomial-grid-value coefficients anchor side count row column)))
 :hints (("Goal"
 :use ((:instance lw-polynomial-grid-rows-nth (row 0) (remaining (+ 1 count)) (index row))
       (:instance lw-polynomial-grid-row-nth (column 0) (remaining (+ 1 count)) (index column)))
 :in-theory (union-theories
 '(lw-polynomial-grid lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(local (defthm lw-pgr-tails
 (implies (not (zp remaining))
 (and (equal (cdr (lw-polynomial-grid-row coefficients anchor side count row column remaining))
             (lw-polynomial-grid-row coefficients anchor side count row (+ 1 column) (- remaining 1)))
      (equal (cdr (lw-polynomial-grid-rows coefficients anchor side count row remaining))
             (lw-polynomial-grid-rows coefficients anchor side count (+ 1 row) (- remaining 1)))))
 :hints (("Goal" :expand ((lw-polynomial-grid-row coefficients anchor side count row column remaining)
 (lw-polynomial-grid-rows coefficients anchor side count row remaining))
 :in-theory (union-theories
 '( lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-grid-row-near
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp count) (natp row) (< row count) (natp column) (natp remaining)
 (<= (+ column remaining) (+ 1 count)) (rationalp epsilon) (< 0 epsilon)
 (<= (* 2 (lw-polynomial-grid-step side count) (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) epsilon))
 (lw-ray-row-near-check
  (lw-polynomial-grid-row coefficients anchor side count row column remaining)
  (lw-polynomial-grid-row coefficients anchor side count (+ 1 row) column remaining) epsilon))
 :hints (("Goal" :induct (lw-polynomial-grid-row coefficients anchor side count row column remaining)
 :in-theory (union-theories
 '(lw-pgr-heads lw-pgr-tails lw-polynomial-grid-row lw-ray-row-near-check endp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-grid-cell-variation (dr 0) (dc 1))
         (:instance lw-polynomial-grid-cell-variation (dr 1) (dc 1))
         (:instance lw-polynomial-grid-cell-variation (dr 1) (dc 0)))
 :do-not-induct t))))

(defthm lw-polynomial-grid-rows-near
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp count) (natp row) (natp remaining) (<= (+ row remaining) (+ 1 count))
 (rationalp epsilon) (< 0 epsilon) (<= (* 2 (lw-polynomial-grid-step side count) (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) epsilon))
 (lw-ray-grid-near-check (lw-polynomial-grid-rows coefficients anchor side count row remaining) epsilon))
 :hints (("Goal" :induct (lw-polynomial-grid-rows coefficients anchor side count row remaining)
 :in-theory (union-theories
 '(lw-pgr-heads lw-pgr-tails lw-polynomial-grid-rows lw-ray-grid-near-check endp lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-grid-row-near (column 0) (remaining (+ 1 count))))
 :do-not-induct t))))

(defthm lw-polynomial-grid-near
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp count) (rationalp epsilon) (< 0 epsilon) (<= (* 2 (lw-polynomial-grid-step side count) (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) epsilon))
 (lw-ray-grid-near-check (lw-polynomial-grid coefficients anchor side count) epsilon))
 :hints (("Goal" :use ((:instance lw-polynomial-grid-rows-near (row 0) (remaining (+ 1 count))))
 :in-theory (union-theories
 '(lw-polynomial-grid lw-pgr-left-commutes lw-pgr-left-distributes lw-pgr-fold-constants lw-pgr-times-negative lw-pgr-negative-times lw-pgr-zero-times lw-pgr-minus-one lw-pgr-double-negative lw-pgr-add-cancel lw-pgr-double lw-pgr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))



