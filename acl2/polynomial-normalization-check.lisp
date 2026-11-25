(in-package "ACL2")

(include-book "polynomial-normalization-budget")

; Generate the normalized polynomial's checker at the computed refinement.

(local (defthm lw-pnk-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pnk-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pnk-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pnk-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pnk-times-negative (a b) (b a)))
                 :in-theory (disable lw-pnk-times-negative)))))

(local (defthm lw-pnk-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pnk-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pnk-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pnk-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pnk-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pnk-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pnk-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pnk-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnk-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnk-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pnk-left-commutes)))))
(local (defthm lw-pnk-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pnk-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pnk-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pnk-left-commutes lw-pnk-left-distributes lw-pnk-fold-constants lw-pnk-times-negative lw-pnk-negative-times lw-pnk-zero-times lw-pnk-minus-one lw-pnk-double-negative lw-pnk-add-cancel lw-pnk-double lw-pnk-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))
(local (defthm lw-pnk-norm-lower
 (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius)
               (rationalp clearance) (<= 0 clearance) (< radius clearance)
               (not (lw-complex-diskp point clearance)))
  (< (* radius radius) (lw-complex-norm-square point)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance lw-complex-disk-norm-square (radius clearance)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pnk-left-commutes lw-pnk-left-distributes lw-pnk-fold-constants lw-pnk-times-negative lw-pnk-negative-times lw-pnk-zero-times lw-pnk-minus-one lw-pnk-double-negative lw-pnk-add-cancel lw-pnk-double lw-pnk-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-normalization-edge-check
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse)
               (natp edge) (< edge 4) (natp index) (< index (lw-polynomial-normalization-count coefficients anchor side coarse)))
  (lw-polynomial-edge-check (lw-polynomial-square-normalize coefficients anchor side) (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) index) (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) (+ 1 index)) 7 (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse)))))
 :hints (("Goal"
  :use (lw-polynomial-square-normalize-valid lw-polynomial-normalization-count-data
        lw-polynomial-normalization-edge-cap-data
        (:instance lw-polynomial-square-clearance-data (count coarse))
        (:instance lw-unit-square-line-point-data (count (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-unit-square-line-point-data (count (lw-polynomial-normalization-count coefficients anchor side coarse)) (index (+ 1 index)))
        (:instance lw-unit-square-line-point-step (count (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-unit-square-point-annulus (point (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) index)))
        (:instance lw-unit-square-point-annulus (point (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) (+ 1 index))))
        (:instance lw-complex-disk-enlarge (point (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) index)) (radius 2) (cap 7))
        (:instance lw-complex-disk-enlarge (point (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) (+ 1 index))) (radius 2) (cap 7))
        (:instance lw-polynomial-normalized-square-clearance (point (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) index)))
        (:instance lw-reciprocal-positive (value (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-pnk-norm-lower (point (lw-complex-polynomial (lw-polynomial-square-normalize coefficients anchor side) (lw-polynomial-line-point (lw-polynomial-square-edge-left (cons -1 -1) 2 edge)
                 (lw-polynomial-square-edge-right (cons -1 -1) 2 edge) (lw-polynomial-normalization-count coefficients anchor side coarse) index) 0))
          (radius (lw-polynomial-edge-cap (lw-polynomial-square-normalize coefficients anchor side) 7 (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse))))) (clearance (lw-polynomial-square-clearance coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-check lw-complex-polynomial-rational lw-pnk-point-type lw-pnk-inverse-rational lw-pnk-product-rational lw-pnk-left-commutes lw-pnk-left-distributes lw-pnk-fold-constants lw-pnk-times-negative lw-pnk-negative-times lw-pnk-zero-times lw-pnk-minus-one lw-pnk-double-negative lw-pnk-add-cancel lw-pnk-double lw-pnk-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-normalization-line-check
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse)
               (natp edge) (< edge 4) (natp index) (natp remaining) (<= (+ index remaining) (lw-polynomial-normalization-count coefficients anchor side coarse)))
  (lw-polynomial-line-check (lw-polynomial-square-normalize coefficients anchor side)
   (lw-polynomial-square-edge-left (cons -1 -1) 2 edge) (lw-polynomial-square-edge-right (cons -1 -1) 2 edge)
   (lw-polynomial-normalization-count coefficients anchor side coarse) index remaining 7 (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse)))))
 :hints (("Goal"
  :induct (lw-polynomial-line-check (lw-polynomial-square-normalize coefficients anchor side)
   (lw-polynomial-square-edge-left (cons -1 -1) 2 edge) (lw-polynomial-square-edge-right (cons -1 -1) 2 edge)
   (lw-polynomial-normalization-count coefficients anchor side coarse) index remaining 7 (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-check) lw-polynomial-line-check lw-polynomial-normalization-edge-check lw-pnk-left-commutes lw-pnk-left-distributes lw-pnk-fold-constants lw-pnk-times-negative lw-pnk-negative-times lw-pnk-zero-times lw-pnk-minus-one lw-pnk-double-negative lw-pnk-add-cancel lw-pnk-double lw-pnk-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-normalization-boundary-check
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse))
  (lw-polynomial-square-boundary-check (lw-polynomial-square-normalize coefficients anchor side) (cons -1 -1) 2 (lw-polynomial-normalization-count coefficients anchor side coarse)))
 :hints (("Goal"
  :use (lw-polynomial-normalization-count-data
        (:instance lw-polynomial-normalization-line-check (edge 0) (index 0) (remaining (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-polynomial-normalization-line-check (edge 1) (index 0) (remaining (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-polynomial-normalization-line-check (edge 2) (index 0) (remaining (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-polynomial-normalization-line-check (edge 3) (index 0) (remaining (lw-polynomial-normalization-count coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-boundary-check lw-polynomial-grid-radius lw-polynomial-grid-step lw-complex-l1 abs lw-pnk-left-commutes lw-pnk-left-distributes lw-pnk-fold-constants lw-pnk-times-negative lw-pnk-negative-times lw-pnk-zero-times lw-pnk-minus-one lw-pnk-double-negative lw-pnk-add-cancel lw-pnk-double lw-pnk-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
