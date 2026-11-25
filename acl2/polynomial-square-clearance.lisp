(in-package "ACL2")

(include-book "polynomial-mesh-cells")
(include-book "unit-square-clearance")

; A coarse square certificate generates positive clearance on its entire boundary.

(local (defthm lw-psc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psc-times-negative (a b) (b a)))
                 :in-theory (disable lw-psc-times-negative)))))

(local (defthm lw-psc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psc-left-commutes)))))
(defun lw-polynomial-square-clearance (coefficients anchor side count)
 (min (lw-polynomial-line-clearance coefficients (lw-polynomial-square-edge-left anchor side 0) (lw-polynomial-square-edge-right anchor side 0) count 0 count (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count)) (min (lw-polynomial-line-clearance coefficients (lw-polynomial-square-edge-left anchor side 1) (lw-polynomial-square-edge-right anchor side 1) count 0 count (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count)) (min (lw-polynomial-line-clearance coefficients (lw-polynomial-square-edge-left anchor side 2) (lw-polynomial-square-edge-right anchor side 2) count 0 count (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count)) (lw-polynomial-line-clearance coefficients (lw-polynomial-square-edge-left anchor side 3) (lw-polynomial-square-edge-right anchor side 3) count 0 count (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count))))))

(defthm lw-polynomial-square-clearance-data
 (implies (lw-polynomial-square-boundary-check coefficients anchor side count)
  (and (rationalp (lw-polynomial-square-clearance coefficients anchor side count))
       (< 0 (lw-polynomial-square-clearance coefficients anchor side count))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 0)) (right (lw-polynomial-square-edge-right anchor side 0))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 1)) (right (lw-polynomial-square-edge-right anchor side 1))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 2)) (right (lw-polynomial-square-edge-right anchor side 2))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 3)) (right (lw-polynomial-square-edge-right anchor side 3))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-boundary-check lw-polynomial-square-clearance min lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-clearance-edge
 (implies (and (lw-polynomial-square-boundary-check coefficients anchor side count) (natp edge) (< edge 4))
  (and (lw-polynomial-line-check coefficients (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count 0 count
         (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count))
       (<= (lw-polynomial-square-clearance coefficients anchor side count) (lw-polynomial-line-clearance coefficients (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count 0 count (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count)))))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
  :use ((:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 0)) (right (lw-polynomial-square-edge-right anchor side 0))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 1)) (right (lw-polynomial-square-edge-right anchor side 1))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 2)) (right (lw-polynomial-square-edge-right anchor side 2))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side 3)) (right (lw-polynomial-square-edge-right anchor side 3))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-boundary-check lw-polynomial-square-clearance min lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-side-excludes-clearance
 (implies (and (lw-polynomial-square-boundary-check coefficients anchor side count)
               (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (natp edge) (< edge 4) (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (not (lw-complex-diskp
   (lw-complex-polynomial coefficients (lw-complex-segment (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) parameter) 0)
   (lw-polynomial-square-clearance coefficients anchor side count))))
 :hints (("Goal"
  :use (lw-polynomial-square-clearance-data lw-polynomial-square-clearance-edge
        (:instance lw-polynomial-line-clearance-data (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge))
          (index 0) (remaining count) (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-polynomial-whole-line-excludes-clearance (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge))
          (bound (lw-polynomial-grid-radius anchor side)) (radius (lw-polynomial-grid-step side count)))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-polynomial coefficients (lw-complex-segment (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) parameter) 0))
          (radius (lw-polynomial-square-clearance coefficients anchor side count)) (cap (lw-polynomial-line-clearance coefficients (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count 0 count (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side count)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complexp lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-unit-square-edge-number (point)
 (cond ((equal (cdr point) -1) 0) ((equal (cdr point) 1) 1)
       ((equal (car point) 1) 2) (t 3)))
(defun lw-unit-square-edge-parameter (point)
 (* 1/2 (+ 1 (if (< (lw-unit-square-edge-number point) 2) (car point) (cdr point)))))

(local (defthm lw-psc-pair
 (implies (consp point) (equal (cons (car point) (cdr point)) point))
 :hints (("Goal" :in-theory (theory 'ground-zero)))))

(defthm lw-unit-square-edge-data
 (implies (lw-unit-square-pointp point)
  (and (natp (lw-unit-square-edge-number point)) (< (lw-unit-square-edge-number point) 4)
       (rationalp (lw-unit-square-edge-parameter point))
       (<= 0 (lw-unit-square-edge-parameter point)) (<= (lw-unit-square-edge-parameter point) 1)
       (equal point
        (lw-complex-segment
         (lw-polynomial-square-edge-left (cons -1 -1) 2 (lw-unit-square-edge-number point))
         (lw-polynomial-square-edge-right (cons -1 -1) 2 (lw-unit-square-edge-number point))
         (lw-unit-square-edge-parameter point)))))
 :rule-classes nil
 :hints (("Goal"
  :use (lw-unit-square-point-coordinates)
  :cases ((equal (cdr point) -1) (equal (cdr point) 1) (equal (car point) 1))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-edge-number lw-unit-square-edge-parameter lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complex-segment lw-complex-add lw-complex-scale lw-complexp lw-psc-pair lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-unit-square-excludes-clearance
 (implies (and (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (posp count) (lw-unit-square-pointp point))
  (not (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                         (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count))))
 :hints (("Goal"
  :use (lw-unit-square-edge-data
        (:instance lw-polynomial-square-side-excludes-clearance (anchor (cons -1 -1)) (side 2)
          (edge (lw-unit-square-edge-number point)) (parameter (lw-unit-square-edge-parameter point))))
  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-psc-left-commutes lw-psc-left-distributes lw-psc-fold-constants lw-psc-times-negative lw-psc-negative-times lw-psc-zero-times lw-psc-minus-one lw-psc-double-negative lw-psc-add-cancel lw-psc-double lw-psc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
