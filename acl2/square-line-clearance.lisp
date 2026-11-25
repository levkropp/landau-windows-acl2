; Canonical square-side clearance and geometry from a sampled perimeter.
(in-package "ACL2")
(include-book "euler-square-native-index")
(local (in-theory (disable lw-ray-row-avoids lw-ray-reverse-points lw-ray-grid-perimeter
 lw-ray-four-path-perimeter lw-polynomial-path-values lw-polynomial-square-boundary
 lw-polynomial-grid lw-polynomial-grid-row lw-polynomial-grid-rows
 lw-polynomial-square-edge-values lw-polynomial-square-edge-row lw-polynomial-square-edge-column
 lw-polynomial-line-point lw-polynomial-line-values lw-polynomial-grid-point
 lw-complexp lw-complex-sub lw-complex-diskp lw-square-containsp)))
(local (defthm lw-slc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-slc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-slc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-slc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-slc-times-negative (a b) (b a)))
                 :in-theory (disable lw-slc-times-negative)))))

(local (defthm lw-slc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-slc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-slc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-slc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-slc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-slc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-slc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-slc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-slc-left-commutes)))))
(local (defthm lw-slc-avoids-boolean
 (booleanp (lw-ray-row-avoids points eta))
 :hints (("Goal" :induct (lw-ray-row-avoids points eta)
 :in-theory (union-theories
 '(lw-ray-row-avoids booleanp endp lw-slc-left-commutes lw-slc-left-distributes lw-slc-fold-constants lw-slc-times-negative lw-slc-negative-times lw-slc-zero-times lw-slc-minus-one lw-slc-double-negative lw-slc-add-cancel lw-slc-double lw-slc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-slc-avoids-append
 (equal (lw-ray-row-avoids (append left right) eta)
        (and (lw-ray-row-avoids left eta) (lw-ray-row-avoids right eta)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(lw-ray-row-avoids append endp lw-slc-left-commutes lw-slc-left-distributes lw-slc-fold-constants lw-slc-times-negative lw-slc-negative-times lw-slc-zero-times lw-slc-minus-one lw-slc-double-negative lw-slc-add-cancel lw-slc-double lw-slc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-slc-avoids-reverse
 (equal (lw-ray-row-avoids (lw-ray-reverse-points points) eta) (lw-ray-row-avoids points eta))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
 :in-theory (union-theories
 '(lw-slc-avoids-boolean lw-ray-reverse-points lw-ray-row-avoids lw-slc-avoids-append append endp lw-slc-left-commutes lw-slc-left-distributes lw-slc-fold-constants lw-slc-times-negative lw-slc-negative-times lw-slc-zero-times lw-slc-minus-one lw-slc-double-negative lw-slc-add-cancel lw-slc-double lw-slc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-slc-grid-heads
 (implies (not (zp remaining))
 (equal (car (lw-polynomial-grid-rows coefficients anchor side count row remaining))
        (lw-polynomial-grid-row coefficients anchor side count row 0 (+ 1 count))))
 :hints (("Goal" :expand ((lw-polynomial-grid-rows coefficients anchor side count row remaining))
 :in-theory (union-theories
 '(lw-polynomial-grid-rows lw-slc-left-commutes lw-slc-left-distributes lw-slc-fold-constants lw-slc-times-negative lw-slc-negative-times lw-slc-zero-times lw-slc-minus-one lw-slc-double-negative lw-slc-add-cancel lw-slc-double lw-slc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-square-boundary-avoids-lines
 (implies (and (lw-complexp anchor) (rationalp side) (posp count) (natp edge) (< edge 4)
 (lw-ray-row-avoids
  (lw-polynomial-path-values coefficients (lw-polynomial-square-boundary anchor side count)) eta))
 (lw-ray-row-avoids
  (lw-polynomial-line-values coefficients (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count 0 (+ 1 count)) eta))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
 :use (lw-polynomial-square-boundary-values
       (:instance lw-polynomial-square-edge-as-line (edge 0) (index 0) (remaining (+ 1 count)))
       (:instance lw-polynomial-square-edge-as-line (edge 1) (index 0) (remaining (+ 1 count)))
       (:instance lw-polynomial-square-edge-as-line (edge 2) (index 0) (remaining (+ 1 count)))
       (:instance lw-polynomial-square-edge-as-line (edge 3) (index 0) (remaining (+ 1 count))))
 :in-theory (union-theories
 '(lw-ray-grid-perimeter lw-ray-four-path-perimeter lw-polynomial-grid lw-slc-grid-heads lw-polynomial-grid-rows-last lw-polynomial-grid-left-column lw-polynomial-grid-right-column lw-polynomial-square-edge-values lw-polynomial-square-edge-row lw-polynomial-square-edge-column lw-slc-avoids-append lw-slc-avoids-reverse fold-consts-in-+ lw-slc-left-commutes lw-slc-left-distributes lw-slc-fold-constants lw-slc-times-negative lw-slc-negative-times lw-slc-zero-times lw-slc-minus-one lw-slc-double-negative lw-slc-add-cancel lw-slc-double lw-slc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-square-line-point-contained
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (natp edge) (< edge 4) (natp index) (<= index count))
 (lw-square-containsp anchor side (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count index)))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
 :use (lw-polynomial-square-edge-point
       (:instance lw-polynomial-grid-point-bounds (row (lw-polynomial-square-edge-row count edge index)) (column (lw-polynomial-square-edge-column count edge index))))
 :in-theory (union-theories
 '(lw-square-containsp lw-polynomial-square-edge-row lw-polynomial-square-edge-column lw-slc-left-commutes lw-slc-left-distributes lw-slc-fold-constants lw-slc-times-negative lw-slc-negative-times lw-slc-zero-times lw-slc-minus-one lw-slc-double-negative lw-slc-add-cancel lw-slc-double lw-slc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-square-line-step-bound
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (natp edge) (< edge 4) (natp index))
 (lw-complex-diskp (lw-complex-sub (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count (+ 1 index)) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count index))
                  (* 2 (lw-polynomial-grid-step side count))))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
 :use (lw-polynomial-square-edge-point
       (:instance lw-polynomial-square-edge-point (index (+ 1 index)))
       (:instance lw-polynomial-grid-point-cell-distance
        (row (lw-polynomial-square-edge-row count edge index)) (column (lw-polynomial-square-edge-column count edge index)) (dr (if (< edge 2) 0 1)) (dc (if (< edge 2) 1 0))))
 :in-theory (union-theories
 '(lw-polynomial-square-edge-row lw-polynomial-square-edge-column fold-consts-in-+ lw-slc-left-commutes lw-slc-left-distributes lw-slc-fold-constants lw-slc-times-negative lw-slc-negative-times lw-slc-zero-times lw-slc-minus-one lw-slc-double-negative lw-slc-add-cancel lw-slc-double lw-slc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

