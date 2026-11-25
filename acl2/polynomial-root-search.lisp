; Computed mesh and guaranteed rational approximate root from a nonzero finite index.
(in-package "ACL2")
(include-book "polynomial-grid")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
 lw-complex-diskp lw-diskp lw-complex-norm-square lw-complex-l1 lw-complex-polynomial lw-complex-coefficientsp
 lw-ray-gridp lw-ray-grid-near-check lw-ray-grid-small-search lw-ray-pointsp lw-polynomial-lipschitz-cap
 lw-polynomial-grid lw-polynomial-grid-row lw-polynomial-grid-rows lw-polynomial-grid-point lw-polynomial-grid-value lw-polynomial-grid-step lw-polynomial-grid-radius
 lw-ray-grid-boundary-index lw-ceiling-rational)))
(local (defthm lw-prs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-prs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-prs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-prs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-prs-times-negative (a b) (b a)))
                 :in-theory (disable lw-prs-times-negative)))))

(local (defthm lw-prs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-prs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-prs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-prs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-prs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-prs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-prs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-prs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-prs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-prs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-prs-left-commutes)))))
(defun lw-polynomial-root-count (coefficients anchor side epsilon)
 (+ 1 (lw-ceiling-rational (* 4 side (+ 1 (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) (/ epsilon)))))
(defun lw-polynomial-root-grid (coefficients anchor side epsilon)
 (lw-polynomial-grid coefficients anchor side (lw-polynomial-root-count coefficients anchor side epsilon)))
(defun lw-polynomial-root-address (coefficients anchor side epsilon)
 (lw-ray-grid-small-search (lw-polynomial-root-grid coefficients anchor side epsilon) epsilon))
(defun lw-polynomial-root-point (coefficients anchor side epsilon)
 (lw-polynomial-grid-point anchor side (lw-polynomial-root-count coefficients anchor side epsilon) (car (lw-polynomial-root-address coefficients anchor side epsilon)) (cdr (lw-polynomial-root-address coefficients anchor side epsilon))))
(defun lw-polynomial-root-index (coefficients anchor side epsilon)
 (lw-ray-grid-boundary-index (lw-polynomial-root-grid coefficients anchor side epsilon)))

(local (in-theory (disable lw-polynomial-root-count lw-polynomial-root-grid lw-polynomial-root-address lw-polynomial-root-point lw-polynomial-root-index)))

(local (defthm lw-prs-count-aux
 (implies (and (rationalp side) (< 0 side) (rationalp mass) (<= 0 mass) (rationalp epsilon) (< 0 epsilon))
 (let ((count (+ 1 (lw-ceiling-rational (* 4 side (+ 1 mass) (/ epsilon))))))
 (and (posp count) (<= (* 2 side (/ count) mass) epsilon))))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-positive (value epsilon))
       (:instance lw-prs-positive-product (a side) (b (+ 1 mass)))
       (:instance lw-prs-positive-product (a (* 4 side (+ 1 mass))) (b (/ epsilon)))
       (:instance lw-ceiling-rational-natural (value (* 4 side (+ 1 mass) (/ epsilon))))
       (:instance lw-ceiling-rational-bracket (value (* 4 side (+ 1 mass) (/ epsilon))))
       (:instance lw-prs-multiply-order (a 0) (b mass) (factor side))
       (:instance lw-prs-multiply-order (a (* 4 side (+ 1 mass) (/ epsilon))) (b (+ 1 (lw-ceiling-rational (* 4 side (+ 1 mass) (/ epsilon))))) (factor epsilon))
       (:instance lw-prs-inverse-factor (divisor epsilon) (coefficient (* 4 side (+ 1 mass))))
       (:instance lw-positive-division-bound (numerator (* 2 side mass)) (divisor (+ 1 (lw-ceiling-rational (* 4 side (+ 1 mass) (/ epsilon))))) (bound epsilon)))
 :in-theory (union-theories
 '( lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-polynomial-root-count-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon))
 (and (posp (lw-polynomial-root-count coefficients anchor side epsilon))
      (<= (* 2 (lw-polynomial-grid-step side (lw-polynomial-root-count coefficients anchor side epsilon)) (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-grid-radius-data
       (:instance lw-polynomial-lipschitz-cap-data (bound (lw-polynomial-grid-radius anchor side)))
       (:instance lw-prs-count-aux (mass (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side)))))
 :in-theory (union-theories
 '(lw-polynomial-root-count lw-polynomial-grid-step lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-root-grid-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon))
 (and (posp (lw-polynomial-root-count coefficients anchor side epsilon)) (lw-ray-gridp (lw-polynomial-root-grid coefficients anchor side epsilon) (+ 1 (lw-polynomial-root-count coefficients anchor side epsilon)))
      (equal (len (lw-polynomial-root-grid coefficients anchor side epsilon)) (+ 1 (lw-polynomial-root-count coefficients anchor side epsilon)))
      (lw-ray-grid-near-check (lw-polynomial-root-grid coefficients anchor side epsilon) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-root-count-data
       (:instance lw-polynomial-grid-data (count (lw-polynomial-root-count coefficients anchor side epsilon)))
       (:instance lw-polynomial-grid-near (count (lw-polynomial-root-count coefficients anchor side epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-root-grid lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-root-search-complete
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon) (not (equal (lw-polynomial-root-index coefficients anchor side epsilon) 0)))
 (consp (lw-polynomial-root-address coefficients anchor side epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-root-grid-data
       (:instance lw-ray-grid-nonzero-index-search-complete (rows (lw-polynomial-root-grid coefficients anchor side epsilon)) (width (+ 1 (lw-polynomial-root-count coefficients anchor side epsilon)))))
 :in-theory (union-theories
 '(lw-polynomial-root-address lw-polynomial-root-index lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(local (defthm lw-prs-length-natural (natp (len rows))
 :hints (("Goal" :induct (len rows) :in-theory (union-theories
 '(len endp lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))
(local (defun lw-prs-nth-induct (rows index)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp rows) (zp index)) (list rows index)
 (lw-prs-nth-induct (cdr rows) (- index 1)))))
(local (defthm lw-prs-grid-row-width
 (implies (and (lw-ray-gridp rows width) (natp index) (< index (len rows)))
 (equal (len (nth index rows)) width))
 :hints (("Goal" :induct (lw-prs-nth-induct rows index)
 :in-theory (union-theories
 '((:induction lw-prs-nth-induct) lw-prs-length-natural lw-ray-gridp nth len endp lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-root-address-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon) (consp (lw-polynomial-root-address coefficients anchor side epsilon)))
 (and (natp (car (lw-polynomial-root-address coefficients anchor side epsilon))) (<= (car (lw-polynomial-root-address coefficients anchor side epsilon)) (lw-polynomial-root-count coefficients anchor side epsilon)) (natp (cdr (lw-polynomial-root-address coefficients anchor side epsilon))) (<= (cdr (lw-polynomial-root-address coefficients anchor side epsilon)) (lw-polynomial-root-count coefficients anchor side epsilon))
      (lw-complex-diskp (lw-polynomial-grid-value coefficients anchor side (lw-polynomial-root-count coefficients anchor side epsilon) (car (lw-polynomial-root-address coefficients anchor side epsilon)) (cdr (lw-polynomial-root-address coefficients anchor side epsilon))) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-root-grid-data
       (:instance lw-ray-grid-small-search-data (rows (lw-polynomial-root-grid coefficients anchor side epsilon)))
       (:instance lw-prs-grid-row-width (rows (lw-polynomial-root-grid coefficients anchor side epsilon)) (width (+ 1 (lw-polynomial-root-count coefficients anchor side epsilon))) (index (car (lw-polynomial-root-address coefficients anchor side epsilon))))
       (:instance lw-polynomial-grid-access (count (lw-polynomial-root-count coefficients anchor side epsilon)) (row (car (lw-polynomial-root-address coefficients anchor side epsilon))) (column (cdr (lw-polynomial-root-address coefficients anchor side epsilon)))))
 :in-theory (union-theories
 '(lw-polynomial-root-address lw-polynomial-root-grid lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-root-point-sound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon) (consp (lw-polynomial-root-address coefficients anchor side epsilon)))
 (and (lw-complexp (lw-polynomial-root-point coefficients anchor side epsilon))
      (<= (car anchor) (car (lw-polynomial-root-point coefficients anchor side epsilon))) (<= (car (lw-polynomial-root-point coefficients anchor side epsilon)) (+ (car anchor) side))
      (<= (cdr anchor) (cdr (lw-polynomial-root-point coefficients anchor side epsilon))) (<= (cdr (lw-polynomial-root-point coefficients anchor side epsilon)) (+ (cdr anchor) side))
      (lw-complex-diskp (lw-complex-polynomial coefficients (lw-polynomial-root-point coefficients anchor side epsilon) 0) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-root-count-data lw-polynomial-root-address-data
       (:instance lw-polynomial-grid-point-bounds (count (lw-polynomial-root-count coefficients anchor side epsilon)) (row (car (lw-polynomial-root-address coefficients anchor side epsilon))) (column (cdr (lw-polynomial-root-address coefficients anchor side epsilon)))))
 :in-theory (union-theories
 '(lw-polynomial-root-point lw-polynomial-grid-value lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-root-search-witness
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon) (not (equal (lw-polynomial-root-index coefficients anchor side epsilon) 0)))
 (and (consp (lw-polynomial-root-address coefficients anchor side epsilon)) (lw-complexp (lw-polynomial-root-point coefficients anchor side epsilon))
      (<= (car anchor) (car (lw-polynomial-root-point coefficients anchor side epsilon))) (<= (car (lw-polynomial-root-point coefficients anchor side epsilon)) (+ (car anchor) side))
      (<= (cdr anchor) (cdr (lw-polynomial-root-point coefficients anchor side epsilon))) (<= (cdr (lw-polynomial-root-point coefficients anchor side epsilon)) (+ (cdr anchor) side))
      (lw-complex-diskp (lw-complex-polynomial coefficients (lw-polynomial-root-point coefficients anchor side epsilon) 0) epsilon)))
 :hints (("Goal" :use (lw-polynomial-root-search-complete lw-polynomial-root-point-sound)
 :in-theory (union-theories
 '( lw-prs-left-commutes lw-prs-left-distributes lw-prs-fold-constants lw-prs-times-negative lw-prs-negative-times lw-prs-zero-times lw-prs-minus-one lw-prs-double-negative lw-prs-add-cancel lw-prs-double lw-prs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)


