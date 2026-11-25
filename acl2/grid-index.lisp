; Exact cancellation of internal edges in a finite rectangular grid.
(in-package "ACL2")
(include-book "polygon-index")
(local (in-theory (disable lw-complexp lw-complex-det lw-complex-dot lw-complex-positive-halfplanep
 lw-ray-crossing lw-ray-triangle-index lw-ray-path-index lw-ray-path-last lw-ray-polygon-index lw-ray-pointsp)))
(local (defthm lw-gwi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-gwi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-gwi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-gwi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-gwi-times-negative (a b) (b a)))
                 :in-theory (disable lw-gwi-times-negative)))))

(local (defthm lw-gwi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-gwi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-gwi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-gwi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-gwi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-gwi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-gwi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-gwi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-gwi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-gwi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-gwi-left-commutes)))))
(defun lw-ray-row-index (row) (lw-ray-path-index (car row) (cdr row)))
(defun lw-ray-row-last (row) (lw-ray-path-last (car row) (cdr row)))
(defun lw-ray-row-strip-index (bottom top)
 (declare (xargs :measure (acl2-count bottom) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp bottom) (endp (cdr bottom))) 0
 (+ (lw-ray-quadrilateral-index (car bottom) (cadr bottom) (cadr top) (car top))
    (lw-ray-row-strip-index (cdr bottom) (cdr top)))))
(defun lw-ray-gridp (rows width)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp rows) (equal rows nil)
 (and (lw-ray-pointsp (car rows)) (equal (len (car rows)) width) (lw-ray-gridp (cdr rows) width))))
(defun lw-ray-grid-left (rows)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp rows) nil (cons (caar rows) (lw-ray-grid-left (cdr rows)))))
(defun lw-ray-grid-right (rows)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp rows) nil (cons (lw-ray-row-last (car rows)) (lw-ray-grid-right (cdr rows)))))
(defun lw-ray-grid-last-row (rows) (lw-ray-path-last (car rows) (cdr rows)))
(defun lw-ray-grid-cell-index (rows)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp rows) (endp (cdr rows))) 0
 (+ (lw-ray-row-strip-index (car rows) (cadr rows)) (lw-ray-grid-cell-index (cdr rows)))))
(defun lw-ray-grid-boundary-index (rows)
 (if (endp rows) 0
 (+ (lw-ray-row-index (car rows)) (- (lw-ray-row-index (lw-ray-grid-last-row rows)))
    (lw-ray-row-index (lw-ray-grid-right rows)) (- (lw-ray-row-index (lw-ray-grid-left rows))))))

(local (in-theory (disable lw-ray-row-index lw-ray-row-last lw-ray-row-strip-index lw-ray-gridp lw-ray-grid-left lw-ray-grid-right lw-ray-grid-last-row lw-ray-grid-cell-index lw-ray-grid-boundary-index)))

(local (defthm lw-gwi-length-natural (natp (len points))
 :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-gwi-equal-length-consp
 (implies (and (equal (len bottom) (len top)))
 (equal (consp bottom) (consp top)))
 :hints (("Goal"
 :use ((:instance lw-gwi-length-natural (points (cdr bottom)))
       (:instance lw-gwi-length-natural (points (cdr top))))
 :in-theory (union-theories
 '(len endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(local (defthm lw-gwi-quadrilateral-integer
 (integerp (lw-ray-quadrilateral-index a b c d))
 :hints (("Goal" :use (lw-ray-crossing-data
       (:instance lw-ray-crossing-data (a b) (b c))
       (:instance lw-ray-crossing-data (a c) (b d))
       (:instance lw-ray-crossing-data (a d) (b a)))
 :in-theory (union-theories
 '(lw-ray-quadrilateral-index lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-gwi-row-numbers
 (and (integerp (lw-ray-row-index row)) (integerp (lw-ray-row-strip-index bottom top)))
 :hints (("Goal" :induct (lw-ray-row-strip-index bottom top)
 :in-theory (union-theories
 '(lw-ray-row-strip-index lw-gwi-quadrilateral-integer lw-ray-row-index lw-ray-path-index-integer lw-ray-crossing-data endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-row-strip-boundary
 (implies (and (lw-ray-pointsp bottom) (lw-ray-pointsp top) (consp bottom) (consp top) (equal (len bottom) (len top)))
 (equal (lw-ray-row-strip-index bottom top)
 (+ (lw-ray-row-index bottom) (- (lw-ray-row-index top))
    (lw-ray-crossing (lw-ray-row-last bottom) (lw-ray-row-last top))
    (- (lw-ray-crossing (car bottom) (car top))))))
 :hints (("Goal" :induct (lw-ray-row-strip-index bottom top)
 :in-theory (union-theories
 '(lw-gwi-length-natural lw-ray-row-strip-index lw-ray-quadrilateral-index lw-ray-row-index lw-ray-row-last lw-ray-path-index lw-ray-path-last lw-ray-pointsp lw-ray-path-index-integer len endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-gwi-equal-length-consp (bottom (cdr bottom)) (top (cdr top)))
         (:instance lw-ray-crossing-reverse (a (car top)) (b (cadr top)))
         (:instance lw-ray-crossing-reverse (a (car bottom)) (b (car top)))
         (:instance lw-ray-crossing-data (a (car bottom)) (b (cadr bottom)))
         (:instance lw-ray-crossing-data (a (cadr bottom)) (b (cadr top)))
         (:instance lw-ray-crossing-data (a (car top)) (b (cadr top)))
         (:instance lw-ray-crossing-data (a (car bottom)) (b (car top)))
         (:instance lw-ray-crossing-data (a (lw-ray-path-last (car bottom) (cdr bottom))) (b (lw-ray-path-last (car top) (cdr top)))))
 :do-not-induct t))))


(local (defthm lw-gwi-row-index-cons
 (equal (lw-ray-row-index (cons current points))
 (if (endp points) 0 (+ (lw-ray-crossing current (car points)) (lw-ray-row-index points))))
 :hints (("Goal" :use ((:instance lw-ray-crossing-data (a current) (b (car points)))
       (:instance lw-ray-path-index-integer (current (car points)) (points (cdr points))))
 :in-theory (union-theories
 '(lw-ray-row-index lw-ray-path-index endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-gwi-last-row-step
 (implies (consp (cdr rows)) (equal (lw-ray-grid-last-row rows) (lw-ray-grid-last-row (cdr rows))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-last-row lw-ray-path-last endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-gwi-last-row-base
 (implies (endp (cdr rows)) (equal (lw-ray-grid-last-row rows) (car rows)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-last-row lw-ray-path-last endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-grid-cell-index-integer
 (integerp (lw-ray-grid-cell-index rows))
 :hints (("Goal" :induct (lw-ray-grid-cell-index rows)
 :in-theory (union-theories
 '(lw-ray-grid-cell-index endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-gwi-row-numbers (row (car rows)) (bottom (car rows)) (top (cadr rows))))
 :do-not-induct t)))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-ray-grid-boundary-index-integer
 (integerp (lw-ray-grid-boundary-index rows))
 :hints (("Goal"
 :use ((:instance lw-gwi-row-numbers (row (car rows)))
       (:instance lw-gwi-row-numbers (row (lw-ray-grid-last-row rows)))
       (:instance lw-gwi-row-numbers (row (lw-ray-grid-right rows)))
       (:instance lw-gwi-row-numbers (row (lw-ray-grid-left rows))))
 :in-theory (union-theories
 '(lw-ray-grid-boundary-index endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes (:rewrite :type-prescription))

(local (defthm lw-gwi-column-heads
 (and (equal (consp (lw-ray-grid-left rows)) (consp rows))
      (equal (consp (lw-ray-grid-right rows)) (consp rows))
      (implies (consp rows)
       (and (equal (car (lw-ray-grid-left rows)) (caar rows))
            (equal (car (lw-ray-grid-right rows)) (lw-ray-row-last (car rows))))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-left lw-ray-grid-right endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-grid-internal-edges-cancel
 (implies (and (posp width) (lw-ray-gridp rows width))
 (equal (lw-ray-grid-cell-index rows) (lw-ray-grid-boundary-index rows)))
 :hints (("Goal" :induct (lw-ray-grid-cell-index rows)
 :in-theory (union-theories
 '(lw-gwi-column-heads lw-ray-grid-cell-index lw-ray-grid-boundary-index lw-ray-grid-left lw-ray-grid-right lw-ray-gridp lw-gwi-row-index-cons lw-gwi-last-row-step lw-gwi-last-row-base lw-gwi-length-natural len endp lw-gwi-left-commutes lw-gwi-left-distributes lw-gwi-fold-constants lw-gwi-times-negative lw-gwi-negative-times lw-gwi-zero-times lw-gwi-minus-one lw-gwi-double-negative lw-gwi-add-cancel lw-gwi-double lw-gwi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-row-strip-boundary (bottom (car rows)) (top (cadr rows)))
         (:instance lw-gwi-row-numbers (row (car rows)) (bottom (car rows)) (top (cadr rows)))
         (:instance lw-gwi-row-numbers (row (cadr rows)))
         (:instance lw-gwi-row-numbers (row (lw-ray-grid-last-row (cdr rows))))
         (:instance lw-gwi-row-numbers (row (lw-ray-grid-left (cdr rows))))
         (:instance lw-gwi-row-numbers (row (lw-ray-grid-right (cdr rows))))
         (:instance lw-ray-grid-cell-index-integer (rows (cdr rows)))
         (:instance lw-ray-crossing-data (a (lw-ray-row-last (car rows))) (b (lw-ray-row-last (cadr rows))))
         (:instance lw-ray-crossing-data (a (caar rows)) (b (caadr rows))))
 :do-not-induct t))))


