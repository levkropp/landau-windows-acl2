(in-package "ACL2")

(include-book "polynomial-affine")
(include-book "polynomial-trim")
(include-book "polynomial-square-clearance")

; Exact affine transport between any rational square and the unit square.

(local (defthm lw-psn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psn-times-negative (a b) (b a)))
                 :in-theory (disable lw-psn-times-negative)))))

(local (defthm lw-psn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psn-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psn-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psn-left-commutes)))))
(defun lw-polynomial-square-center (anchor side)
 (cons (+ (car anchor) (* 1/2 side)) (+ (cdr anchor) (* 1/2 side))))
(defun lw-polynomial-square-slope (side) (cons (* 1/2 side) 0))
(defun lw-polynomial-square-forward (anchor side point)
 (lw-complex-add (lw-polynomial-square-center anchor side)
                 (lw-complex-mul (lw-polynomial-square-slope side) point)))
(defun lw-polynomial-square-normalize (coefficients anchor side)
 (lw-polynomial-affine (lw-polynomial-trim coefficients)
  (lw-polynomial-square-center anchor side) (lw-polynomial-square-slope side)))

(local (defthm lw-psn-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-psn-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-psn-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(defthm lw-polynomial-square-map-data
 (implies (and (lw-complexp anchor) (rationalp side))
  (and (lw-complexp (lw-polynomial-square-center anchor side))
       (lw-complexp (lw-polynomial-square-slope side))
       (implies (lw-complexp point) (lw-complexp (lw-polynomial-square-forward anchor side point)))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-center lw-polynomial-square-slope lw-polynomial-square-forward lw-complexp lw-complex-add lw-complex-mul lw-psn-product-rational lw-psn-sum-rational lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-polynomial-square-normalize-valid
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side))
  (and (lw-complex-coefficientsp (lw-polynomial-square-normalize coefficients anchor side))
       (equal (len (lw-polynomial-square-normalize coefficients anchor side)) (len (lw-polynomial-trim coefficients)))))
 :hints (("Goal" :use (lw-polynomial-trim-valid lw-polynomial-square-map-data
                       (:instance lw-polynomial-affine-valid (coefficients (lw-polynomial-trim coefficients))
                         (center (lw-polynomial-square-center anchor side)) (slope (lw-polynomial-square-slope side))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-normalize lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-normalize-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (lw-complexp point))
  (equal (lw-complex-polynomial (lw-polynomial-square-normalize coefficients anchor side) point 0)
         (lw-complex-polynomial coefficients (lw-polynomial-square-forward anchor side point) 0)))
 :hints (("Goal"
  :use (lw-polynomial-trim-valid lw-polynomial-square-map-data
        (:instance lw-polynomial-affine-evaluation (coefficients (lw-polynomial-trim coefficients))
          (center (lw-polynomial-square-center anchor side)) (slope (lw-polynomial-square-slope side)))
        (:instance lw-polynomial-trim-evaluation (point (lw-polynomial-square-forward anchor side point)) (offset 0)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-normalize lw-polynomial-square-forward lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-forward-side
 (implies (and (lw-complexp anchor) (rationalp side) (natp edge) (< edge 4) (rationalp parameter))
  (equal
   (lw-polynomial-square-forward anchor side
    (lw-complex-segment (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                        (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) parameter))
   (lw-complex-segment (lw-polynomial-square-edge-left anchor side edge)
                       (lw-polynomial-square-edge-right anchor side edge) parameter)))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-forward lw-polynomial-square-center lw-polynomial-square-slope lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-complex-mul lw-complexp lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-polynomial-square-forward-grid-point
 (implies (and (lw-complexp anchor) (rationalp side) (posp count) (natp row) (natp column))
  (equal (lw-polynomial-square-forward anchor side (lw-polynomial-grid-point (cons -1 -1) 2 count row column))
         (lw-polynomial-grid-point anchor side count row column)))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-forward lw-polynomial-square-center lw-polynomial-square-slope lw-polynomial-grid-point lw-polynomial-grid-step lw-complex-add lw-complex-mul lw-complexp lw-psn-inverse-rational lw-psn-product-rational lw-psn-sum-rational lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-square-normalize-grid-value
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side)
               (posp count) (natp row) (natp column))
  (equal (lw-polynomial-grid-value (lw-polynomial-square-normalize coefficients anchor side) (cons -1 -1) 2 count row column)
         (lw-polynomial-grid-value coefficients anchor side count row column)))
 :hints (("Goal" :use ((:instance lw-polynomial-grid-point-rational (anchor (cons -1 -1)) (side 2)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-grid-value lw-polynomial-square-normalize-evaluation lw-polynomial-square-forward-grid-point (:executable-counterpart lw-complexp) lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))

(local (defthm lw-psn-grid-row
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side)
               (posp count) (natp row) (natp column) (natp remaining))
  (equal (lw-polynomial-grid-row (lw-polynomial-square-normalize coefficients anchor side) (cons -1 -1) 2 count row column remaining)
         (lw-polynomial-grid-row coefficients anchor side count row column remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-row coefficients anchor side count row column remaining)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-grid-row) lw-polynomial-grid-row lw-polynomial-square-normalize-grid-value lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psn-grid-rows
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side)
               (posp count) (natp row) (natp remaining))
  (equal (lw-polynomial-grid-rows (lw-polynomial-square-normalize coefficients anchor side) (cons -1 -1) 2 count row remaining)
         (lw-polynomial-grid-rows coefficients anchor side count row remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-rows coefficients anchor side count row remaining)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-grid-rows) lw-polynomial-grid-rows lw-psn-grid-row lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-square-normalize-grid
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (posp count))
  (equal (lw-polynomial-grid (lw-polynomial-square-normalize coefficients anchor side) (cons -1 -1) 2 count)
         (lw-polynomial-grid coefficients anchor side count)))
 :hints (("Goal" :use ((:instance lw-psn-grid-rows (row 0) (remaining (+ 1 count))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-grid lw-psn-left-commutes lw-psn-left-distributes lw-psn-fold-constants lw-psn-times-negative lw-psn-negative-times lw-psn-zero-times lw-psn-minus-one lw-psn-double-negative lw-psn-add-cancel lw-psn-double lw-psn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
