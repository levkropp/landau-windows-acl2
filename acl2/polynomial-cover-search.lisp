; Bounded selection of a nonzero-index cell from a retained cover.
(in-package "ACL2")
(include-book "polynomial-cover-index")
(local (in-theory (disable lw-polynomial-cell-index lw-polynomial-cover-index lw-square-address-listp
 lw-polynomial-sublevel-cover lw-polynomial-cell-activep lw-polynomial-grid-value lw-polynomial-cell-variation)))
(local (defthm lw-pcs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcs-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcs-times-negative)))))

(local (defthm lw-pcs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcs-left-commutes)))))
(defun lw-polynomial-cover-index-search (coefficients anchor side count addresses)
 (if (endp addresses) nil
 (if (not (equal (lw-polynomial-cell-index coefficients anchor side count (caar addresses) (cdar addresses)) 0))
     (car addresses)
 (lw-polynomial-cover-index-search coefficients anchor side count (cdr addresses)))))
(defun lw-polynomial-sublevel-index-address (coefficients anchor side count epsilon)
 (lw-polynomial-cover-index-search coefficients anchor side count
 (lw-polynomial-sublevel-cover coefficients anchor side count epsilon)))
(local (in-theory (disable lw-polynomial-cover-index-search lw-polynomial-sublevel-index-address)))

(defthm lw-polynomial-cover-index-search-type
 (implies (lw-square-address-listp addresses count)
 (or (consp (lw-polynomial-cover-index-search coefficients anchor side count addresses))
     (equal (lw-polynomial-cover-index-search coefficients anchor side count addresses) nil)))
 :hints (("Goal" :induct (lw-polynomial-cover-index-search coefficients anchor side count addresses)
 :in-theory (union-theories
 '(lw-polynomial-cover-index-search lw-square-address-listp endp lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-cover-index-search-sound
 (implies (consp (lw-polynomial-cover-index-search coefficients anchor side count addresses))
 (let ((address (lw-polynomial-cover-index-search coefficients anchor side count addresses)))
 (and (member-equal address addresses)
      (not (equal (lw-polynomial-cell-index coefficients anchor side count (car address) (cdr address)) 0)))))
 :hints (("Goal" :induct (lw-polynomial-cover-index-search coefficients anchor side count addresses)
 :in-theory (union-theories
 '(lw-polynomial-cover-index-search member-equal endp lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-cover-index-search-complete
 (implies (and (lw-square-address-listp addresses count)
 (not (equal (lw-polynomial-cover-index coefficients anchor side count addresses) 0)))
 (consp (lw-polynomial-cover-index-search coefficients anchor side count addresses)))
 :hints (("Goal" :induct (lw-polynomial-cover-index-search coefficients anchor side count addresses)
 :in-theory (union-theories
 '(lw-polynomial-cover-index-search lw-polynomial-cover-index lw-square-address-listp lw-polynomial-cover-index-integer lw-polynomial-cell-index-integer endp lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-sublevel-index-address-witness
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (posp count) (rationalp epsilon) (< 0 epsilon)
 (not (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side count)) 0)))
 (let ((address (lw-polynomial-sublevel-index-address coefficients anchor side count epsilon)))
 (and (consp address) (member-equal address (lw-polynomial-sublevel-cover coefficients anchor side count epsilon))
      (natp (car address)) (< (car address) count) (natp (cdr address)) (< (cdr address) count)
      (lw-polynomial-cell-activep coefficients anchor side count epsilon (car address) (cdr address))
      (not (equal (lw-polynomial-cell-index coefficients anchor side count (car address) (cdr address)) 0))
      (lw-complex-diskp (lw-polynomial-grid-value coefficients anchor side count (car address) (cdr address))
                       (+ epsilon (lw-polynomial-cell-variation coefficients anchor side count))))))
 :hints (("Goal"
 :use (lw-polynomial-sublevel-cover-index-conservation lw-polynomial-sublevel-cover-data
       (:instance lw-polynomial-cover-index-search-complete
        (addresses (lw-polynomial-sublevel-cover coefficients anchor side count epsilon)))
       (:instance lw-polynomial-cover-index-search-sound
        (addresses (lw-polynomial-sublevel-cover coefficients anchor side count epsilon)))
       (:instance lw-polynomial-sublevel-cover-member-data
        (address (lw-polynomial-sublevel-index-address coefficients anchor side count epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-sublevel-index-address lw-polynomial-cell-activep lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
