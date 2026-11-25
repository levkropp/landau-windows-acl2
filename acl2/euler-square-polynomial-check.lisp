(in-package "ACL2")

(include-book "euler-square-line-refinement")
(include-book "polynomial-square-counts")

; The canonical native square check already implies a polynomial boundary checker.

(local (defthm lw-esp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esp-times-negative (a b) (b a)))
                 :in-theory (disable lw-esp-times-negative)))))

(local (defthm lw-esp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esp-left-commutes)))))
(local (defthm lw-esp-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-esp-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(defthm lw-polynomial-square-line-step-exact
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (natp edge) (< edge 4) (natp index))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count (+ 1 index))
    (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count index))
   (lw-polynomial-grid-step side count)))
 :hints (("Goal" :cases ((equal edge 0) (equal edge 1) (equal edge 2))
  :use ((:instance lw-reciprocal-positive (value count))
        (:instance lw-esp-positive-product (a side) (b (/ count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-point lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-polynomial-grid-step lw-complex-segment lw-complex-add lw-complex-scale lw-complex-sub lw-complex-diskp lw-diskp lw-complexp lw-esp-product-rational lw-esp-inverse-rational lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-euler-square-polynomial-budget-data
 (implies (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta)
  (and (lw-positive-squarep anchor side) (lw-complex-coefficientsp (lw-euler-positive-square-model anchor side base-target base-error))
       (lw-complexp anchor) (rationalp side) (< 0 side) (posp coarse)
       (natp base-target) (rationalp base-error) (< 0 base-error) (<= base-error eta)
       (rationalp eta) (< 0 eta) (rationalp (lw-polynomial-grid-step side coarse)) (< 0 (lw-polynomial-grid-step side coarse))
       (rationalp (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side))) (<= 0 (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side)))
       (rationalp (lw-polynomial-edge-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side coarse))) (<= 0 (lw-polynomial-edge-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side coarse))) (<= (lw-polynomial-edge-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side coarse)) (* 1/4 eta))))
 :hints (("Goal"
  :use ((:instance lw-euler-polygon-index-check-data (points (lw-polynomial-square-boundary anchor side coarse)) (step (lw-polynomial-grid-step side coarse)))
        (:instance lw-polynomial-grid-step-data (count coarse))
        (:instance lw-esp-multiply-order (a 0) (b (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side))) (factor (lw-polynomial-grid-step side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-square-index-check lw-euler-polygon-index-check lw-polynomial-edge-cap lw-esp-product-rational lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-esp-contained-type
 (implies (lw-square-containsp anchor side point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-square-containsp lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))
(local (defthm lw-esp-norm-lower
 (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius)
               (rationalp clearance) (< 0 clearance) (< radius clearance) (not (lw-complex-diskp point clearance)))
  (< (* radius radius) (lw-complex-norm-square point)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance lw-complex-disk-norm-square (radius clearance)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-euler-square-base-polynomial-edge-check
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp index) (< index coarse)
               (not (lw-complex-diskp
                (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge)
                 (lw-polynomial-square-edge-right anchor side edge) coarse index) eta)))
  (lw-polynomial-edge-check (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 index)) (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side coarse)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-polynomial-grid-radius-data
        (:instance lw-polynomial-square-line-point-contained (count coarse))
        (:instance lw-polynomial-square-line-point-contained (count coarse) (index (+ 1 index)))
        (:instance lw-square-contained-in-disk (point (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index)))
        (:instance lw-square-contained-in-disk (point (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 index))))
        (:instance lw-polynomial-square-line-step-exact (count coarse))
        (:instance lw-esp-norm-lower (point (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index) 0)) (radius (lw-polynomial-edge-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side coarse))) (clearance eta)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-check lw-polynomial-line-value lw-complex-polynomial-rational lw-esp-contained-type lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-square-base-polynomial-line-check
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp index) (natp remaining)
               (<= (+ index remaining) coarse)
               (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta index (+ 1 remaining)))
  (lw-polynomial-line-check (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index remaining (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side coarse)))
 :hints (("Goal"
  :induct (lw-polynomial-line-check (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index remaining (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side coarse))
  :expand ((lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta index (+ 1 remaining)))
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-check) lw-polynomial-line-check lw-euler-square-base-polynomial-edge-check lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-square-base-polynomial-boundary-check
 (implies (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (lw-polynomial-square-boundary-check (lw-euler-positive-square-model anchor side base-target base-error) anchor side coarse))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data
        (:instance lw-euler-square-line-clearance-generated (edge 0))
        (:instance lw-euler-square-base-polynomial-line-check (edge 0) (index 0) (remaining coarse))
        (:instance lw-euler-square-line-clearance-generated (edge 1))
        (:instance lw-euler-square-base-polynomial-line-check (edge 1) (index 0) (remaining coarse))
        (:instance lw-euler-square-line-clearance-generated (edge 2))
        (:instance lw-euler-square-base-polynomial-line-check (edge 2) (index 0) (remaining coarse))
        (:instance lw-euler-square-line-clearance-generated (edge 3))
        (:instance lw-euler-square-base-polynomial-line-check (edge 3) (index 0) (remaining coarse)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-boundary-check lw-esp-left-commutes lw-esp-left-distributes lw-esp-fold-constants lw-esp-times-negative lw-esp-negative-times lw-esp-zero-times lw-esp-minus-one lw-esp-double-negative lw-esp-add-cancel lw-esp-double lw-esp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
