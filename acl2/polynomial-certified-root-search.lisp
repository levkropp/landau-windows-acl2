; One fixed coarse square certificate yields approximate roots at every accuracy.
(in-package "ACL2")
(include-book "polynomial-square-refinement")
(include-book "polynomial-root-search")
(local (in-theory (disable lw-complexp lw-complex-polynomial lw-polynomial-root-count lw-polynomial-grid-step
 lw-polynomial-grid-radius lw-polynomial-lipschitz-cap lw-polynomial-grid lw-polynomial-grid-value
 lw-polynomial-grid-point lw-ray-grid-boundary-index lw-ray-grid-small-search lw-polynomial-square-boundary-check)))
(local (defthm lw-pcr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcr-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcr-times-negative)))))

(local (defthm lw-pcr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcr-left-commutes)))))
(defun lw-polynomial-certified-root-count (coefficients anchor side coarse epsilon)
 (* coarse (lw-polynomial-root-count coefficients anchor side epsilon)))
(defun lw-polynomial-certified-root-grid (coefficients anchor side coarse epsilon)
 (lw-polynomial-grid coefficients anchor side (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)))
(defun lw-polynomial-certified-root-address (coefficients anchor side coarse epsilon)
 (lw-ray-grid-small-search (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon) epsilon))
(defun lw-polynomial-certified-root-point (coefficients anchor side coarse epsilon)
 (lw-polynomial-grid-point anchor side (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)
  (car (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))
  (cdr (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))))
(defun lw-polynomial-certified-root-index (coefficients anchor side coarse epsilon)
 (lw-ray-grid-boundary-index (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon)))
(local (in-theory (disable lw-polynomial-certified-root-count lw-polynomial-certified-root-grid
 lw-polynomial-certified-root-address lw-polynomial-certified-root-point lw-polynomial-certified-root-index)))

(local (defthm lw-pcr-count-multiple
 (implies (and (posp coarse) (posp base))
 (and (posp (* coarse base)) (<= base (* coarse base))))
 :hints (("Goal"
 :use ((:instance lw-pcr-positive-product (a coarse) (b base))
       (:instance lw-pcr-multiply-order (a 1) (b coarse) (factor base)))
 :in-theory (union-theories
 '( lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(local (defthm lw-pcr-variation-multiple
 (implies (and (rationalp side) (<= 0 side) (rationalp mass) (<= 0 mass) (posp coarse) (posp base))
 (<= (* 2 side (/ (* coarse base)) mass) (* 2 side (/ base) mass)))
 :hints (("Goal"
 :use (lw-pcr-count-multiple
       (:instance lw-reciprocal-antitone (left base) (right (* coarse base)))
       (:instance lw-pcr-multiply-order (a (/ (* coarse base))) (b (/ base)) (factor (* 2 side mass))))
 :in-theory (union-theories
 '( lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-polynomial-certified-root-count-data
 (implies (and (posp coarse) (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
 (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon))
 (and (posp (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon))
      (<= (* 2 (lw-polynomial-grid-step side (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon))
               (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side))) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-root-count-data lw-polynomial-grid-radius-data
       (:instance lw-polynomial-lipschitz-cap-data (bound (lw-polynomial-grid-radius anchor side)))
       (:instance lw-pcr-count-multiple (base (lw-polynomial-root-count coefficients anchor side epsilon)))
       (:instance lw-pcr-variation-multiple (base (lw-polynomial-root-count coefficients anchor side epsilon))
        (mass (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side)))))
 :in-theory (union-theories
 '(lw-polynomial-certified-root-count lw-polynomial-grid-step lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-certified-root-grid-data
 (implies (and (posp coarse) (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon))
 (and (posp (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)) (lw-ray-gridp (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon) (+ 1 (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)))
      (equal (len (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon)) (+ 1 (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)))
      (lw-ray-grid-near-check (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-certified-root-count-data
       (:instance lw-polynomial-grid-data (count (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)))
       (:instance lw-polynomial-grid-near (count (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-certified-root-grid lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil)

(local (defthm lw-pcr-length-natural (natp (len rows))
 :hints (("Goal" :induct (len rows) :in-theory (union-theories
 '(len endp lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defun lw-pcr-nth-induct (rows index)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (endp rows) (zp index)) (list rows index)
 (lw-pcr-nth-induct (cdr rows) (- index 1)))))

(local (defthm lw-pcr-grid-row-width
 (implies (and (lw-ray-gridp rows width) (natp index) (< index (len rows)))
 (equal (len (nth index rows)) width))
 :hints (("Goal" :induct (lw-pcr-nth-induct rows index)
 :in-theory (union-theories
 '((:induction lw-pcr-nth-induct) lw-pcr-length-natural lw-ray-gridp nth len endp lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-certified-root-address-data
 (implies (and (posp coarse) (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon) (consp (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)))
 (and (natp (car (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))) (<= (car (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)) (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)) (natp (cdr (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))) (<= (cdr (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)) (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon))
      (lw-complex-diskp (lw-polynomial-grid-value coefficients anchor side (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon) (car (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)) (cdr (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-certified-root-grid-data
       (:instance lw-ray-grid-small-search-data (rows (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon)))
       (:instance lw-pcr-grid-row-width (rows (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon)) (width (+ 1 (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon))) (index (car (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))))
       (:instance lw-polynomial-grid-access (count (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)) (row (car (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))) (column (cdr (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)))))
 :in-theory (union-theories
 '(lw-polynomial-certified-root-address lw-polynomial-certified-root-grid lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-certified-root-point-sound
 (implies (and (posp coarse) (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon) (consp (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)))
 (and (lw-complexp (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon))
      (<= (car anchor) (car (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon))) (<= (car (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon)) (+ (car anchor) side))
      (<= (cdr anchor) (cdr (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon))) (<= (cdr (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon)) (+ (cdr anchor) side))
      (lw-complex-diskp (lw-complex-polynomial coefficients (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon) 0) epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-certified-root-count-data lw-polynomial-certified-root-address-data
       (:instance lw-polynomial-grid-point-bounds (count (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)) (row (car (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))) (column (cdr (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)))))
 :in-theory (union-theories
 '(lw-polynomial-certified-root-point lw-polynomial-grid-value lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil)

(defthm lw-polynomial-certified-root-index-stable
 (implies (and (posp coarse) (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
 (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse))
 (equal (lw-polynomial-certified-root-index coefficients anchor side coarse epsilon)
        (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse))))
 :hints (("Goal"
 :use (lw-polynomial-root-count-data
       (:instance lw-polynomial-square-refinement-index (factor (lw-polynomial-root-count coefficients anchor side epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-certified-root-index lw-polynomial-certified-root-grid lw-polynomial-certified-root-count lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-certified-root-search-complete
 (implies (and (posp coarse) (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
 (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse)
 (not (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse)) 0)))
 (consp (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-certified-root-grid-data lw-polynomial-certified-root-index-stable
       (:instance lw-ray-grid-nonzero-index-search-complete
        (rows (lw-polynomial-certified-root-grid coefficients anchor side coarse epsilon))
        (width (+ 1 (lw-polynomial-certified-root-count coefficients anchor side coarse epsilon)))))
 :in-theory (union-theories
 '(lw-polynomial-certified-root-address lw-polynomial-certified-root-index lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-certified-root-search-witness
 (implies (and (posp coarse) (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
 (rationalp side) (< 0 side) (rationalp epsilon) (< 0 epsilon)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse)
 (not (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse)) 0)))
 (and (consp (lw-polynomial-certified-root-address coefficients anchor side coarse epsilon))
      (lw-complexp (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon))
      (<= (car anchor) (car (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon)))
      (<= (car (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon)) (+ (car anchor) side))
      (<= (cdr anchor) (cdr (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon)))
      (<= (cdr (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon)) (+ (cdr anchor) side))
      (lw-complex-diskp (lw-complex-polynomial coefficients
        (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon) 0) epsilon)))
 :hints (("Goal" :use (lw-polynomial-certified-root-search-complete lw-polynomial-certified-root-point-sound)
 :in-theory (union-theories
 '( lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
