(in-package "ACL2")

(include-book "polynomial-global-root-mesh")

; Rational approximate roots of every represented nonconstant polynomial.
; No root, nonzero-index certificate, or cell witness is supplied as a hypothesis.

(local (defthm lw-par-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-par-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-par-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-par-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-par-times-negative (a b) (b a)))
                 :in-theory (disable lw-par-times-negative)))))

(local (defthm lw-par-zero-times (equal (* 0 a) 0)))

(local (defthm lw-par-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-par-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-par-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-par-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-par-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-par-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-par-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-par-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-par-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-par-left-commutes)))))
(defun lw-polynomial-global-root-address (coefficients epsilon)
 (lw-ray-grid-small-search (lw-polynomial-global-root-grid coefficients epsilon) epsilon))
(defun lw-polynomial-global-root-unit-point (coefficients epsilon)
 (lw-polynomial-grid-point (cons -1 -1) 2 (lw-polynomial-global-root-count coefficients epsilon)
  (car (lw-polynomial-global-root-address coefficients epsilon))
  (cdr (lw-polynomial-global-root-address coefficients epsilon))))
(defun lw-polynomial-global-root-point (coefficients epsilon)
 (lw-complex-scale (lw-polynomial-leading-radius coefficients)
                   (lw-polynomial-global-root-unit-point coefficients epsilon)))

(local (defthm lw-par-length-natural (natp (len rows))
 :hints (("Goal" :induct (len rows) :in-theory (union-theories
 '(len endp lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))
(local (defun lw-par-nth-induct (rows index)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp rows) (zp index)) (list rows index)
 (lw-par-nth-induct (cdr rows) (- index 1)))))
(local (defthm lw-par-grid-row-width
 (implies (and (lw-ray-gridp rows width) (natp index) (< index (len rows)))
 (equal (len (nth index rows)) width))
 :hints (("Goal" :induct (lw-par-nth-induct rows index)
 :in-theory (union-theories
 '((:induction lw-par-nth-induct) lw-par-length-natural lw-ray-gridp nth len endp lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))


(local (defthm lw-par-positive-lower-degree
 (implies (and (consp coefficients) (consp (cdr coefficients)))
          (posp (len (lw-polynomial-without-leading coefficients))))
 :hints (("Goal" :expand ((lw-polynomial-without-leading coefficients))
          :in-theory (union-theories
 '(fold-consts-in-+ len lw-par-length-natural lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))


(defthm lw-polynomial-global-root-search-complete
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon))
  (consp (lw-polynomial-global-root-address coefficients epsilon)))
 :hints (("Goal"
  :use (lw-polynomial-global-root-count-data lw-polynomial-global-root-grid-data
        lw-polynomial-global-root-grid-index
        (:instance lw-par-positive-lower-degree)
        (:instance lw-ray-grid-nonzero-index-search-complete
          (rows (lw-polynomial-global-root-grid coefficients epsilon))
          (width (+ 1 (lw-polynomial-global-root-count coefficients epsilon)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-address lw-par-length-natural lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-global-root-address-data
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon)
               (consp (lw-polynomial-global-root-address coefficients epsilon)))
  (let ((row (car (lw-polynomial-global-root-address coefficients epsilon)))
        (column (cdr (lw-polynomial-global-root-address coefficients epsilon)))
        (count (lw-polynomial-global-root-count coefficients epsilon)))
   (and (natp row) (<= row count) (natp column) (<= column count)
        (lw-complex-diskp
         (lw-polynomial-grid-value (lw-polynomial-outer-coefficients coefficients)
                                   (cons -1 -1) 2 count row column) epsilon))))
 :hints (("Goal"
  :use (lw-polynomial-global-root-count-data lw-polynomial-global-root-grid-data lw-polynomial-leading-radius-data
        (:instance lw-polynomial-rescale-valid (factor (lw-polynomial-leading-radius coefficients)) (offset 0))
        (:instance lw-ray-grid-small-search-data (rows (lw-polynomial-global-root-grid coefficients epsilon)))
        (:instance lw-par-grid-row-width
          (rows (lw-polynomial-global-root-grid coefficients epsilon))
          (width (+ 1 (lw-polynomial-global-root-count coefficients epsilon)))
          (index (car (lw-polynomial-global-root-address coefficients epsilon))))
        (:instance lw-polynomial-grid-access
          (coefficients (lw-polynomial-outer-coefficients coefficients)) (anchor (cons -1 -1)) (side 2)
          (count (lw-polynomial-global-root-count coefficients epsilon))
          (row (car (lw-polynomial-global-root-address coefficients epsilon)))
          (column (cdr (lw-polynomial-global-root-address coefficients epsilon)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-address lw-polynomial-global-root-grid lw-polynomial-outer-coefficients lw-complexp lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
(local (defthm lw-par-unit-square-disk
 (implies (and (lw-complexp point) (<= -1 (car point)) (<= (car point) 1)
               (<= -1 (cdr point)) (<= (cdr point) 1))
  (lw-complex-diskp point 2))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-diskp lw-diskp lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-global-root-unit-point-sound
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon)
               (consp (lw-polynomial-global-root-address coefficients epsilon)))
  (and (lw-complex-diskp (lw-polynomial-global-root-unit-point coefficients epsilon) 2)
       (lw-complex-diskp
        (lw-complex-polynomial (lw-polynomial-outer-coefficients coefficients)
                               (lw-polynomial-global-root-unit-point coefficients epsilon) 0) epsilon)))
 :hints (("Goal"
  :use (lw-polynomial-global-root-count-data lw-polynomial-global-root-address-data
        (:instance lw-polynomial-grid-point-bounds (anchor (cons -1 -1)) (side 2)
          (count (lw-polynomial-global-root-count coefficients epsilon))
          (row (car (lw-polynomial-global-root-address coefficients epsilon)))
          (column (cdr (lw-polynomial-global-root-address coefficients epsilon))))
        (:instance lw-par-unit-square-disk (point (lw-polynomial-global-root-unit-point coefficients epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-unit-point lw-polynomial-grid-value lw-complexp lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
(defthm lw-polynomial-approximate-root
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (rationalp epsilon) (< 0 epsilon))
  (and (consp (lw-polynomial-global-root-address coefficients epsilon))
       (lw-complexp (lw-polynomial-global-root-point coefficients epsilon))
       (lw-complex-diskp (lw-polynomial-global-root-point coefficients epsilon)
                         (* 2 (lw-polynomial-leading-radius coefficients)))
       (lw-complex-diskp
        (lw-complex-polynomial coefficients (lw-polynomial-global-root-point coefficients epsilon) 0) epsilon)))
 :hints (("Goal"
  :use (lw-polynomial-global-root-search-complete lw-polynomial-global-root-unit-point-sound
        lw-polynomial-leading-radius-data
        (:instance lw-complex-scale-disk
          (point (lw-polynomial-global-root-unit-point coefficients epsilon))
          (radius 2) (factor (lw-polynomial-leading-radius coefficients)))
        (:instance lw-polynomial-rescale-evaluation
          (factor (lw-polynomial-leading-radius coefficients)) (offset 0)
          (point (lw-polynomial-global-root-unit-point coefficients epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-global-root-point lw-polynomial-outer-coefficients lw-complex-disk-data lw-complex-scale-rational abs lw-par-left-commutes lw-par-left-distributes lw-par-fold-constants lw-par-times-negative lw-par-negative-times lw-par-zero-times lw-par-minus-one lw-par-double-negative lw-par-add-cancel lw-par-double lw-par-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
