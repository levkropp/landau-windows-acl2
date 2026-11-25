; A nonzero finite boundary index forces bounded search to find a small value.
(in-package "ACL2")
(include-book "grid-index")
(local (in-theory (disable lw-complexp lw-complex-det lw-complex-dot lw-complex-positive-halfplanep
 lw-ray-crossing lw-ray-triangle-index lw-ray-path-index lw-ray-path-last lw-ray-polygon-index lw-ray-pointsp
 lw-complex-diskp lw-complex-sub lw-complex-norm-square lw-ray-gridp lw-ray-grid-cell-index lw-ray-grid-boundary-index lw-ray-row-strip-index)))
(local (defthm lw-grs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-grs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-grs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-grs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-grs-times-negative (a b) (b a)))
                 :in-theory (disable lw-grs-times-negative)))))

(local (defthm lw-grs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-grs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-grs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-grs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-grs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-grs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-grs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-grs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-grs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-grs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-grs-left-commutes)))))
(defun lw-ray-row-near-check (bottom top epsilon)
 (declare (xargs :measure (acl2-count bottom) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp bottom) (endp (cdr bottom))) t
 (and (lw-complex-diskp (lw-complex-sub (cadr bottom) (car bottom)) epsilon)
      (lw-complex-diskp (lw-complex-sub (cadr top) (car bottom)) epsilon)
      (lw-complex-diskp (lw-complex-sub (car top) (car bottom)) epsilon)
      (lw-ray-row-near-check (cdr bottom) (cdr top) epsilon))))
(defun lw-ray-grid-near-check (rows epsilon)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp rows) (endp (cdr rows))) t
 (and (lw-ray-row-near-check (car rows) (cadr rows) epsilon)
      (lw-ray-grid-near-check (cdr rows) epsilon))))
(defun lw-ray-row-avoids (row epsilon)
 (declare (xargs :measure (acl2-count row) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp row) t (and (not (lw-complex-diskp (car row) epsilon)) (lw-ray-row-avoids (cdr row) epsilon))))
(defun lw-ray-grid-avoids (rows epsilon)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp rows) t (and (lw-ray-row-avoids (car rows) epsilon) (lw-ray-grid-avoids (cdr rows) epsilon))))
(defun lw-ray-row-small-search (row epsilon)
 (declare (xargs :measure (acl2-count row) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp row) nil
  (if (lw-complex-diskp (car row) epsilon) 0
   (let ((index (lw-ray-row-small-search (cdr row) epsilon))) (if (natp index) (+ 1 index) nil)))))
(defun lw-ray-grid-small-search (rows epsilon)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp rows) nil
  (let ((column (lw-ray-row-small-search (car rows) epsilon)))
   (if (natp column) (cons 0 column)
    (let ((address (lw-ray-grid-small-search (cdr rows) epsilon)))
     (if (consp address) (cons (+ 1 (car address)) (cdr address)) nil))))))

(local (in-theory (disable lw-ray-row-near-check lw-ray-grid-near-check lw-ray-row-avoids lw-ray-grid-avoids lw-ray-row-small-search lw-ray-grid-small-search)))
(local (defthm lw-grs-length-natural (natp (len points))
 :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-ray-row-small-search-type
 (or (natp (lw-ray-row-small-search row epsilon)) (equal (lw-ray-row-small-search row epsilon) nil))
 :hints (("Goal" :induct (lw-ray-row-small-search row epsilon)
 :in-theory (union-theories
 '(lw-ray-row-small-search endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-row-small-search-data
 (implies (natp (lw-ray-row-small-search row epsilon))
 (and (< (lw-ray-row-small-search row epsilon) (len row))
      (lw-complex-diskp (nth (lw-ray-row-small-search row epsilon) row) epsilon)))
 :hints (("Goal" :induct (lw-ray-row-small-search row epsilon)
 :in-theory (union-theories
 '(lw-ray-row-small-search lw-grs-length-natural len nth endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-row-small-search-failure
 (equal (lw-ray-row-avoids row epsilon) (not (natp (lw-ray-row-small-search row epsilon))))
 :hints (("Goal" :induct (lw-ray-row-small-search row epsilon)
 :in-theory (union-theories
 '(lw-ray-row-small-search lw-ray-row-avoids endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-grid-small-search-failure
 (equal (lw-ray-grid-avoids rows epsilon) (not (consp (lw-ray-grid-small-search rows epsilon))))
 :hints (("Goal" :induct (lw-ray-grid-small-search rows epsilon)
 :in-theory (union-theories
 '(lw-ray-grid-small-search lw-ray-grid-avoids lw-ray-row-small-search-failure endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-grs-nonempty-length
 (implies (consp points) (< 0 (len points)))
 :hints (("Goal" :use ((:instance lw-grs-length-natural (points (cdr points))))
 :in-theory (union-theories
 '(len endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-ray-grid-small-search-data
 (implies (consp (lw-ray-grid-small-search rows epsilon))
 (let ((row (car (lw-ray-grid-small-search rows epsilon))) (column (cdr (lw-ray-grid-small-search rows epsilon))))
 (and (natp row) (< row (len rows)) (natp column) (< column (len (nth row rows)))
      (lw-complex-diskp (nth column (nth row rows)) epsilon))))
 :hints (("Goal" :induct (lw-ray-grid-small-search rows epsilon)
 :in-theory (union-theories
 '(lw-ray-grid-small-search lw-grs-length-natural len nth endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-row-small-search-data (row (car rows)))
         (:instance lw-grs-nonempty-length (points rows))) :do-not-induct t))))


(local (defthm lw-grs-points-head
 (implies (and (lw-ray-pointsp points) (consp points)) (lw-complexp (car points)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-pointsp endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(local (defthm lw-grs-cell-zero
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d) (rationalp epsilon) (< 0 epsilon)
 (not (lw-complex-diskp a epsilon))
 (lw-complex-diskp (lw-complex-sub b a) epsilon)
 (lw-complex-diskp (lw-complex-sub c a) epsilon)
 (lw-complex-diskp (lw-complex-sub d a) epsilon))
 (equal (lw-ray-quadrilateral-index a b c d) 0))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-norm-square (point a) (radius epsilon))
       (:instance lw-complex-dot-self (point a))
       (:instance lw-grs-positive-product (a epsilon) (b epsilon))
       (:instance lw-complex-disk-positive-halfplane (anchor a) (point b) (radius epsilon))
       (:instance lw-complex-disk-positive-halfplane (anchor a) (point c) (radius epsilon))
       (:instance lw-complex-disk-positive-halfplane (anchor a) (point d) (radius epsilon))
       (:instance lw-ray-quadrilateral-halfplane-zero (h a)))
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-ray-row-near-avoids-index-zero
 (implies (and (lw-ray-pointsp bottom) (lw-ray-pointsp top) (equal (len bottom) (len top))
 (rationalp epsilon) (< 0 epsilon) (lw-ray-row-avoids bottom epsilon) (lw-ray-row-near-check bottom top epsilon))
 (equal (lw-ray-row-strip-index bottom top) 0))
 :hints (("Goal" :induct (lw-ray-row-near-check bottom top epsilon)
 :in-theory (union-theories
 '(lw-ray-row-strip-index lw-ray-row-near-check lw-ray-row-avoids lw-ray-pointsp lw-grs-length-natural len endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-grs-cell-zero (a (car bottom)) (b (cadr bottom)) (c (cadr top)) (d (car top)))
         (:instance lw-grs-nonempty-length (points (cdr bottom)))
         (:instance lw-grs-nonempty-length (points (cdr top)))
         (:instance lw-grs-points-head (points (cdr bottom)))
         (:instance lw-grs-points-head (points (cdr top))))
 :do-not-induct t))))

(defthm lw-ray-grid-near-avoids-index-zero
 (implies (and (posp width) (lw-ray-gridp rows width) (rationalp epsilon) (< 0 epsilon)
 (lw-ray-grid-avoids rows epsilon) (lw-ray-grid-near-check rows epsilon))
 (equal (lw-ray-grid-cell-index rows) 0))
 :hints (("Goal" :induct (lw-ray-grid-cell-index rows)
 :in-theory (union-theories
 '(lw-ray-grid-cell-index lw-ray-grid-near-check lw-ray-grid-avoids lw-ray-gridp endp lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-row-near-avoids-index-zero (bottom (car rows)) (top (cadr rows))))
 :do-not-induct t))))

(defthm lw-ray-grid-nonzero-index-search-complete
 (implies (and (posp width) (lw-ray-gridp rows width) (rationalp epsilon) (< 0 epsilon)
 (lw-ray-grid-near-check rows epsilon) (not (equal (lw-ray-grid-boundary-index rows) 0)))
 (consp (lw-ray-grid-small-search rows epsilon)))
 :hints (("Goal"
 :use (lw-ray-grid-small-search-failure lw-ray-grid-near-avoids-index-zero lw-ray-grid-internal-edges-cancel)
 :in-theory (union-theories
 '( lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-ray-grid-nonzero-index-search-witness
 (implies (and (posp width) (lw-ray-gridp rows width) (rationalp epsilon) (< 0 epsilon)
 (lw-ray-grid-near-check rows epsilon) (not (equal (lw-ray-grid-boundary-index rows) 0)))
 (let ((address (lw-ray-grid-small-search rows epsilon)))
 (and (consp address) (natp (car address)) (< (car address) (len rows))
      (natp (cdr address)) (< (cdr address) (len (nth (car address) rows)))
      (lw-complex-diskp (nth (cdr address) (nth (car address) rows)) epsilon))))
 :hints (("Goal"
 :use (lw-ray-grid-nonzero-index-search-complete lw-ray-grid-small-search-data)
 :in-theory (union-theories
 '( lw-grs-left-commutes lw-grs-left-distributes lw-grs-fold-constants lw-grs-times-negative lw-grs-negative-times lw-grs-zero-times lw-grs-minus-one lw-grs-double-negative lw-grs-add-cancel lw-grs-double lw-grs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


