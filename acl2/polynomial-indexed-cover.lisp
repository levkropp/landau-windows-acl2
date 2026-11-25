; Resolved covers inherit a fixed coarse index and return an index-carrying cell.
(in-package "ACL2")
(include-book "polynomial-cover-search")
(include-book "polynomial-resolved-cover")
(local (in-theory (disable lw-polynomial-resolved-cover-count lw-polynomial-certified-root-count lw-polynomial-root-count
 lw-square-spatial-count lw-polynomial-sublevel-cover lw-polynomial-sublevel-index-address lw-polynomial-cell-variation
 lw-polynomial-cell-index lw-polynomial-cell-activep lw-polynomial-cover-index lw-polynomial-grid-step
 lw-polynomial-grid-value lw-polynomial-grid lw-ray-grid-boundary-index lw-square-containsp)))
(local (defthm lw-pic-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pic-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pic-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pic-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pic-times-negative (a b) (b a)))
                 :in-theory (disable lw-pic-times-negative)))))

(local (defthm lw-pic-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pic-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pic-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pic-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pic-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pic-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pic-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pic-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pic-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pic-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pic-left-commutes)))))
(defun lw-polynomial-indexed-cover-count (coefficients anchor side coarse width epsilon)
 (* coarse (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
(defun lw-polynomial-indexed-cover (coefficients anchor side coarse width epsilon)
 (lw-polynomial-sublevel-cover coefficients anchor side
  (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon) epsilon))
(defun lw-polynomial-indexed-cover-address (coefficients anchor side coarse width epsilon)
 (lw-polynomial-sublevel-index-address coefficients anchor side
  (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon) epsilon))
(local (in-theory (disable lw-polynomial-indexed-cover-count lw-polynomial-indexed-cover lw-polynomial-indexed-cover-address)))

(local (defthm lw-pic-count-multiple
 (implies (and (posp coarse) (posp base))
 (and (posp (* coarse base)) (<= base (* coarse base))))
 :hints (("Goal" :use ((:instance lw-pic-positive-product (a coarse) (b base))
       (:instance lw-pic-multiply-order (a 1) (b coarse) (factor base)))
 :in-theory (union-theories
 '( lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))
(local (defthm lw-pic-step-decrease
 (implies (and (rationalp side) (<= 0 side) (posp small) (posp large) (<= small large))
 (<= (lw-polynomial-grid-step side large) (lw-polynomial-grid-step side small)))
 :hints (("Goal" :use ((:instance lw-reciprocal-antitone (left small) (right large))
       (:instance lw-pic-multiply-order (a (/ large)) (b (/ small)) (factor side)))
 :in-theory (union-theories
 '(lw-polynomial-grid-step lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-polynomial-indexed-cover-count-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp coarse) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (let ((count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
 (and (posp count) (rationalp (lw-polynomial-grid-step side count)) (< 0 (lw-polynomial-grid-step side count))
      (<= (lw-polynomial-grid-step side count) width)
      (rationalp (lw-polynomial-cell-variation coefficients anchor side count))
      (<= 0 (lw-polynomial-cell-variation coefficients anchor side count))
      (<= (lw-polynomial-cell-variation coefficients anchor side count) epsilon))))
 :hints (("Goal"
 :use (lw-square-spatial-count-data lw-polynomial-resolved-cover-count-data
       (:instance lw-pic-positive-product (a coarse) (b (lw-square-spatial-count side width)))
       (:instance lw-pic-count-multiple (base (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
       (:instance lw-polynomial-certified-root-count-data (coarse (* coarse (lw-square-spatial-count side width))))
       (:instance lw-pic-step-decrease (small (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)) (large (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
       (:instance lw-polynomial-grid-step-data (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
       (:instance lw-polynomial-cell-variation-data (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-indexed-cover-count lw-polynomial-resolved-cover-count lw-polynomial-certified-root-count lw-polynomial-cell-variation lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-indexed-cover-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp coarse) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (let ((count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
 (and (lw-square-address-listp (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon) count)
      (lw-polynomial-active-coverp coefficients anchor side count epsilon
       (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon))
      (<= (len (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon)) (* count count)))))
 :hints (("Goal" :use (lw-polynomial-indexed-cover-count-data
       (:instance lw-polynomial-sublevel-cover-data (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-indexed-cover lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-indexed-cover-grid-index
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp coarse) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse))
 (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
        (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse))))
 :hints (("Goal"
 :use (lw-polynomial-resolved-cover-count-data
       (:instance lw-polynomial-square-refinement-index (factor (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-indexed-cover-count lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-indexed-cover-index
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp coarse) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse))
 (equal (lw-polynomial-cover-index coefficients anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)
         (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon))
        (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse))))
 :hints (("Goal" :use (lw-polynomial-indexed-cover-count-data lw-polynomial-indexed-cover-grid-index
       (:instance lw-polynomial-sublevel-cover-index-conservation (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-indexed-cover lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-indexed-cover-complete
 (implies (and (lw-complex-coefficientsp coefficients) (lw-square-containsp anchor side point)
 (posp coarse) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) epsilon))
 (and (member-equal (lw-square-cell-address anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon) point)
                    (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon))
      (lw-square-cover-containsp anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon) point
                    (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon))))
 :hints (("Goal" :use (lw-polynomial-indexed-cover-count-data
       (:instance lw-polynomial-sublevel-cover-complete (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-indexed-cover lw-square-containsp lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-indexed-cover-value-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp coarse) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (lw-square-cover-containsp anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon) point
  (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon)))
 (and (lw-square-containsp anchor side point)
      (lw-complex-diskp (lw-complex-polynomial coefficients point 0) (* 3 epsilon))))
 :hints (("Goal"
 :use (lw-polynomial-indexed-cover-count-data
       (:instance lw-polynomial-sublevel-cover-value-bound (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
       (:instance lw-square-cover-in-square (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon))
        (addresses (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial coefficients point 0))
        (radius (+ epsilon (* 2 (lw-polynomial-cell-variation coefficients anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon))))) (cap (* 3 epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-indexed-cover lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-indexed-cover-address-witness
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp coarse) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse)
 (not (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse)) 0)))
 (let ((address (lw-polynomial-indexed-cover-address coefficients anchor side coarse width epsilon)) (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
 (and (consp address) (member-equal address (lw-polynomial-indexed-cover coefficients anchor side coarse width epsilon))
      (natp (car address)) (< (car address) count) (natp (cdr address)) (< (cdr address) count)
      (lw-polynomial-cell-activep coefficients anchor side count epsilon (car address) (cdr address))
      (not (equal (lw-polynomial-cell-index coefficients anchor side count (car address) (cdr address)) 0))
      (lw-complex-diskp (lw-polynomial-grid-value coefficients anchor side count (car address) (cdr address)) (* 2 epsilon)))))
 :hints (("Goal"
 :use (lw-polynomial-indexed-cover-count-data lw-polynomial-indexed-cover-grid-index
       (:instance lw-polynomial-sublevel-index-address-witness (count (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))
       (:instance lw-complex-disk-enlarge
        (point (lw-polynomial-grid-value coefficients anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)
         (car (lw-polynomial-indexed-cover-address coefficients anchor side coarse width epsilon))
         (cdr (lw-polynomial-indexed-cover-address coefficients anchor side coarse width epsilon))))
        (radius (+ epsilon (lw-polynomial-cell-variation coefficients anchor side (lw-polynomial-indexed-cover-count coefficients anchor side coarse width epsilon)))) (cap (* 2 epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-indexed-cover lw-polynomial-indexed-cover-address lw-pic-left-commutes lw-pic-left-distributes lw-pic-fold-constants lw-pic-times-negative lw-pic-negative-times lw-pic-zero-times lw-pic-minus-one lw-pic-double-negative lw-pic-add-cancel lw-pic-double lw-pic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
