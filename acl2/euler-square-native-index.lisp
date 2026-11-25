; Precision-independent native Euler indices on canonical square grids and covers.
(in-package "ACL2")
(include-book "euler-polygon-clearance")
(include-book "polynomial-cover-search")
(local (in-theory (disable lw-euler-polygon-index-check lw-euler-polygon-index
 lw-euler-positive-square-model lw-positive-squarep lw-complexp
 lw-polynomial-square-boundary lw-polynomial-grid lw-ray-grid-boundary-index
 lw-polynomial-sublevel-cover lw-polynomial-cover-index lw-polynomial-sublevel-index-address)))
(local (defthm lw-esi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esi-times-negative (a b) (b a)))
                 :in-theory (disable lw-esi-times-negative)))))

(local (defthm lw-esi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esi-left-commutes)))))
(defun lw-euler-square-index-check (anchor side count base-target base-error step eta)
 (and (posp count)
      (lw-euler-polygon-index-check anchor side (lw-polynomial-square-boundary anchor side count) base-target base-error step eta)))
(local (in-theory (disable lw-euler-square-index-check)))

(defthm lw-euler-square-index-stable
 (implies (and (lw-euler-square-index-check anchor side count base-target base-error step eta)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (equal (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side count)) (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side base-target base-error) anchor side count))))
 :hints (("Goal"
 :use ((:instance lw-euler-polygon-index-check-data (points (lw-polynomial-square-boundary anchor side count)))
       (:instance lw-euler-polygon-index-stable (points (lw-polynomial-square-boundary anchor side count)))
       (:instance lw-euler-positive-square-model-valid)
       (:instance lw-euler-positive-square-model-valid (target base-target) (error base-error))
       (:instance lw-polynomial-grid-boundary-as-polygon (coefficients (lw-euler-positive-square-model anchor side target error)))
       (:instance lw-polynomial-grid-boundary-as-polygon (coefficients (lw-euler-positive-square-model anchor side base-target base-error))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-euler-polygon-index lw-positive-squarep lw-esi-left-commutes lw-esi-left-distributes lw-esi-fold-constants lw-esi-times-negative lw-esi-negative-times lw-esi-zero-times lw-esi-minus-one lw-esi-double-negative lw-esi-add-cancel lw-esi-double lw-esi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-cover-index-stable
 (implies (and (lw-euler-square-index-check anchor side count base-target base-error step eta)
               (natp target) (rationalp error) (< 0 error) (<= error eta)
               (rationalp epsilon) (< 0 epsilon))
 (equal
 (lw-polynomial-cover-index (lw-euler-positive-square-model anchor side target error) anchor side count
  (lw-polynomial-sublevel-cover (lw-euler-positive-square-model anchor side target error) anchor side count epsilon))
 (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side base-target base-error) anchor side count))))
 :hints (("Goal"
 :use (lw-euler-square-index-stable
       (:instance lw-euler-positive-square-model-valid)
       (:instance lw-polynomial-sublevel-cover-index-conservation (coefficients (lw-euler-positive-square-model anchor side target error))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-esi-left-commutes lw-esi-left-distributes lw-esi-fold-constants lw-esi-times-negative lw-esi-negative-times lw-esi-zero-times lw-esi-minus-one lw-esi-double-negative lw-esi-add-cancel lw-esi-double lw-esi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-nonzero-index-address
 (implies (and (lw-euler-square-index-check anchor side count base-target base-error step eta)
               (not (equal (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side base-target base-error) anchor side count)) 0))
               (natp target) (rationalp error) (< 0 error) (<= error eta)
               (rationalp epsilon) (< 0 epsilon))
 (let ((address (lw-polynomial-sublevel-index-address (lw-euler-positive-square-model anchor side target error) anchor side count epsilon)))
 (and (consp address)
      (member-equal address (lw-polynomial-sublevel-cover (lw-euler-positive-square-model anchor side target error) anchor side count epsilon))
      (natp (car address)) (< (car address) count) (natp (cdr address)) (< (cdr address) count)
      (not (equal (lw-polynomial-cell-index (lw-euler-positive-square-model anchor side target error) anchor side count (car address) (cdr address)) 0))
      (lw-polynomial-cell-activep (lw-euler-positive-square-model anchor side target error) anchor side count epsilon (car address) (cdr address))
      (lw-complex-diskp
       (lw-polynomial-grid-value (lw-euler-positive-square-model anchor side target error) anchor side count (car address) (cdr address))
       (+ epsilon (lw-polynomial-cell-variation (lw-euler-positive-square-model anchor side target error) anchor side count))))))
 :hints (("Goal"
 :use (lw-euler-square-index-stable
       (:instance lw-euler-positive-square-model-valid)
       (:instance lw-polynomial-sublevel-index-address-witness (coefficients (lw-euler-positive-square-model anchor side target error))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-esi-left-commutes lw-esi-left-distributes lw-esi-fold-constants lw-esi-times-negative lw-esi-negative-times lw-esi-zero-times lw-esi-minus-one lw-esi-double-negative lw-esi-add-cancel lw-esi-double lw-esi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-cover-index-independent-requests
 (implies (and (lw-euler-square-index-check anchor side count base-target base-error step eta)
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (<= left-error eta)
               (rationalp right-error) (< 0 right-error) (<= right-error eta)
               (rationalp left-epsilon) (< 0 left-epsilon)
               (rationalp right-epsilon) (< 0 right-epsilon))
 (equal
 (lw-polynomial-cover-index
  (lw-euler-positive-square-model anchor side left-target left-error) anchor side count
  (lw-polynomial-sublevel-cover
   (lw-euler-positive-square-model anchor side left-target left-error) anchor side count left-epsilon))
 (lw-polynomial-cover-index
  (lw-euler-positive-square-model anchor side right-target right-error) anchor side count
  (lw-polynomial-sublevel-cover
   (lw-euler-positive-square-model anchor side right-target right-error) anchor side count right-epsilon))))
 :hints (("Goal"
 :use ((:instance lw-euler-square-cover-index-stable (target left-target) (error left-error) (epsilon left-epsilon))
       (:instance lw-euler-square-cover-index-stable (target right-target) (error right-error) (epsilon right-epsilon)))
 :in-theory (union-theories
 '( lw-esi-left-commutes lw-esi-left-distributes lw-esi-fold-constants lw-esi-times-negative lw-esi-negative-times lw-esi-zero-times lw-esi-minus-one lw-esi-double-negative lw-esi-add-cancel lw-esi-double lw-esi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

