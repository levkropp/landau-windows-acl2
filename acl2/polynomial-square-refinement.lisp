; Fixed coarse certificates preserve the actual square-grid boundary index.
(in-package "ACL2")
(include-book "polynomial-line-refinement")
(include-book "polynomial-grid-columns")
(local (in-theory (disable lw-complexp lw-complex-segment lw-complex-add lw-complex-scale
 lw-complex-polynomial lw-polynomial-line-point lw-polynomial-line-value lw-polynomial-line-values
 lw-polynomial-line-crossings lw-polynomial-line-check lw-polynomial-grid lw-polynomial-grid-point
 lw-polynomial-grid-step lw-polynomial-grid-value lw-polynomial-grid-row lw-polynomial-grid-rows
 lw-polynomial-grid-column lw-ray-grid-boundary-index lw-ray-row-index)))
(local (defthm lw-psr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psr-times-negative (a b) (b a)))
                 :in-theory (disable lw-psr-times-negative)))))

(local (defthm lw-psr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psr-left-commutes)))))
(defun lw-polynomial-square-edge-left (anchor side edge)
 (cond ((equal edge 0) anchor)
       ((equal edge 1) (cons (car anchor) (+ (cdr anchor) side)))
       ((equal edge 2) (cons (+ (car anchor) side) (cdr anchor)))
       (t anchor)))
(defun lw-polynomial-square-edge-right (anchor side edge)
 (cond ((equal edge 0) (cons (+ (car anchor) side) (cdr anchor)))
       ((or (equal edge 1) (equal edge 2)) (cons (+ (car anchor) side) (+ (cdr anchor) side)))
       (t (cons (car anchor) (+ (cdr anchor) side)))))
(defun lw-polynomial-square-edge-row (count edge index)
 (if (< edge 2) (if (equal edge 0) 0 count) index))
(defun lw-polynomial-square-edge-column (count edge index)
 (if (< edge 2) index (if (equal edge 2) count 0)))
(defun lw-polynomial-square-edge-values (coefficients anchor side count edge index remaining)
 (if (< edge 2)
 (lw-polynomial-grid-row coefficients anchor side count (lw-polynomial-square-edge-row count edge 0) index remaining)
 (lw-polynomial-grid-column coefficients anchor side count (lw-polynomial-square-edge-column count edge 0) index remaining)))
(defun lw-polynomial-square-crossings (coefficients anchor side count)
 (+ (lw-polynomial-line-crossings coefficients (lw-polynomial-square-edge-left anchor side 0) (lw-polynomial-square-edge-right anchor side 0) count 0 count)
    (- (lw-polynomial-line-crossings coefficients (lw-polynomial-square-edge-left anchor side 1) (lw-polynomial-square-edge-right anchor side 1) count 0 count))
    (lw-polynomial-line-crossings coefficients (lw-polynomial-square-edge-left anchor side 2) (lw-polynomial-square-edge-right anchor side 2) count 0 count)
    (- (lw-polynomial-line-crossings coefficients (lw-polynomial-square-edge-left anchor side 3) (lw-polynomial-square-edge-right anchor side 3) count 0 count))))
(defun lw-polynomial-square-boundary-check (coefficients anchor side count)
 (and
 (lw-polynomial-line-check coefficients (lw-polynomial-square-edge-left anchor side 0)
 (lw-polynomial-square-edge-right anchor side 0) count 0 count
 (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count))
 (lw-polynomial-line-check coefficients (lw-polynomial-square-edge-left anchor side 1)
 (lw-polynomial-square-edge-right anchor side 1) count 0 count
 (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count))
 (lw-polynomial-line-check coefficients (lw-polynomial-square-edge-left anchor side 2)
 (lw-polynomial-square-edge-right anchor side 2) count 0 count
 (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count))
 (lw-polynomial-line-check coefficients (lw-polynomial-square-edge-left anchor side 3)
 (lw-polynomial-square-edge-right anchor side 3) count 0 count
 (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count))))
(local (in-theory (disable lw-polynomial-square-edge-left lw-polynomial-square-edge-right
 lw-polynomial-square-edge-row lw-polynomial-square-edge-column lw-polynomial-square-edge-values
 lw-polynomial-square-crossings lw-polynomial-square-boundary-check)))

(local (defthm lw-psr-edge-rational
 (implies (and (lw-complexp anchor) (rationalp side))
 (and (lw-complexp (lw-polynomial-square-edge-left anchor side edge))
      (lw-complexp (lw-polynomial-square-edge-right anchor side edge))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complexp lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-square-edge-point
 (implies (and (lw-complexp anchor) (rationalp side) (posp count) (natp index) (natp edge) (< edge 4))
 (equal (lw-polynomial-line-point
    (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count index)
 (lw-polynomial-grid-point anchor side count
    (lw-polynomial-square-edge-row count edge index) (lw-polynomial-square-edge-column count edge index))))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
 :use ((:instance inverse-of-* (x count)))
 :in-theory (union-theories
 '(lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-polynomial-square-edge-row lw-polynomial-square-edge-column lw-polynomial-line-point lw-complex-segment lw-complex-add lw-complex-scale lw-polynomial-grid-point lw-polynomial-grid-step lw-complexp lw-psr-inverse-factor fold-consts-in-+ lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-square-edge-as-line
 (implies (and (lw-complexp anchor) (rationalp side) (posp count) (natp index) (natp remaining) (natp edge) (< edge 4))
 (equal (lw-polynomial-square-edge-values coefficients anchor side count edge index remaining)
 (lw-polynomial-line-values coefficients
  (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge)
  count index remaining)))
 :hints (("Goal" :induct (lw-unit-mesh count index remaining)
 :in-theory (union-theories
 '(lw-unit-mesh lw-polynomial-square-edge-values lw-polynomial-square-edge-row lw-polynomial-square-edge-column lw-polynomial-line-values lw-polynomial-line-value lw-polynomial-grid-value lw-polynomial-grid-row lw-polynomial-grid-column lw-polynomial-square-edge-point fold-consts-in-+ lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-psr-heads
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
 '(lw-polynomial-grid-row lw-polynomial-grid-rows lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-grid-boundary-as-crossings
 (implies (and (lw-complexp anchor) (rationalp side) (posp count))
 (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side count))
        (lw-polynomial-square-crossings coefficients anchor side count)))
 :hints (("Goal"
 :use (
 (:instance lw-polynomial-square-edge-as-line (edge 0) (index 0) (remaining (+ 1 count)))
 (:instance lw-polynomial-line-values-index
 (left (lw-polynomial-square-edge-left anchor side 0)) (right (lw-polynomial-square-edge-right anchor side 0))
 (index 0) (remaining count))
 (:instance lw-polynomial-square-edge-as-line (edge 1) (index 0) (remaining (+ 1 count)))
 (:instance lw-polynomial-line-values-index
 (left (lw-polynomial-square-edge-left anchor side 1)) (right (lw-polynomial-square-edge-right anchor side 1))
 (index 0) (remaining count))
 (:instance lw-polynomial-square-edge-as-line (edge 2) (index 0) (remaining (+ 1 count)))
 (:instance lw-polynomial-line-values-index
 (left (lw-polynomial-square-edge-left anchor side 2)) (right (lw-polynomial-square-edge-right anchor side 2))
 (index 0) (remaining count))
 (:instance lw-polynomial-square-edge-as-line (edge 3) (index 0) (remaining (+ 1 count)))
 (:instance lw-polynomial-line-values-index
 (left (lw-polynomial-square-edge-left anchor side 3)) (right (lw-polynomial-square-edge-right anchor side 3))
 (index 0) (remaining count)) )
 :in-theory (union-theories
 '(lw-ray-grid-boundary-index lw-polynomial-grid lw-psr-heads lw-polynomial-grid-rows-last lw-polynomial-grid-left-column lw-polynomial-grid-right-column lw-polynomial-square-edge-values lw-polynomial-square-edge-row lw-polynomial-square-edge-column lw-polynomial-square-crossings lw-ray-row-index-integer lw-polynomial-line-crossings-integer fold-consts-in-+ endp lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-square-refinement-index
 (implies (and (lw-complexp anchor) (rationalp side) (posp coarse) (posp factor)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse))
 (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side (* coarse factor)))
        (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse))))
 :hints (("Goal"
 :use ((:instance lw-psr-positive-product (a coarse) (b factor))
       (:instance lw-polynomial-grid-boundary-as-crossings (count coarse))
       (:instance lw-polynomial-grid-boundary-as-crossings (count (* coarse factor)))
 (:instance lw-psr-edge-rational (edge 0))
 (:instance lw-polynomial-line-refinement-index
 (left (lw-polynomial-square-edge-left anchor side 0)) (right (lw-polynomial-square-edge-right anchor side 0))
 (index 0) (remaining coarse) (bound (lw-polynomial-grid-radius anchor side))
 (radius (lw-polynomial-grid-step side coarse)))
 (:instance lw-psr-edge-rational (edge 1))
 (:instance lw-polynomial-line-refinement-index
 (left (lw-polynomial-square-edge-left anchor side 1)) (right (lw-polynomial-square-edge-right anchor side 1))
 (index 0) (remaining coarse) (bound (lw-polynomial-grid-radius anchor side))
 (radius (lw-polynomial-grid-step side coarse)))
 (:instance lw-psr-edge-rational (edge 2))
 (:instance lw-polynomial-line-refinement-index
 (left (lw-polynomial-square-edge-left anchor side 2)) (right (lw-polynomial-square-edge-right anchor side 2))
 (index 0) (remaining coarse) (bound (lw-polynomial-grid-radius anchor side))
 (radius (lw-polynomial-grid-step side coarse)))
 (:instance lw-psr-edge-rational (edge 3))
 (:instance lw-polynomial-line-refinement-index
 (left (lw-polynomial-square-edge-left anchor side 3)) (right (lw-polynomial-square-edge-right anchor side 3))
 (index 0) (remaining coarse) (bound (lw-polynomial-grid-radius anchor side))
 (radius (lw-polynomial-grid-step side coarse))) )
 :in-theory (union-theories
 '(lw-polynomial-square-boundary-check lw-polynomial-square-crossings lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
