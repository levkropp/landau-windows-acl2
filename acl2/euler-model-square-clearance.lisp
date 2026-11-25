(in-package "ACL2")

(include-book "euler-square-polynomial-check")
(include-book "polynomial-mesh-cells")

; Uniform clearance for every fine Euler polynomial on a fixed checked square.

(local (defthm lw-emc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emc-times-negative (a b) (b a)))
                 :in-theory (disable lw-emc-times-negative)))))

(local (defthm lw-emc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-emc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-emc-left-commutes)))))

(local (defthm lw-emc-clearance-select
 (implies (and (natp start) (natp remaining) (natp cell) (<= start cell) (< cell (+ start remaining))
               (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta start remaining))
  (not (lw-complex-diskp (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) eta)))
 :hints (("Goal"
  :induct (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta start remaining)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-euler-square-line-clearancep) lw-euler-square-line-clearancep lw-emc-left-commutes lw-emc-left-distributes lw-emc-fold-constants lw-emc-times-negative lw-emc-negative-times lw-emc-zero-times lw-emc-minus-one lw-emc-double-negative lw-emc-add-cancel lw-emc-double lw-emc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-square-base-line-value-clearance
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp cell) (<= cell coarse))
  (not (lw-complex-diskp (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) eta)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-square-line-clearance-generated
        (:instance lw-emc-clearance-select (start 0) (remaining (+ 1 coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-emc-left-commutes lw-emc-left-distributes lw-emc-fold-constants lw-emc-times-negative lw-emc-negative-times lw-emc-zero-times lw-emc-minus-one lw-emc-double-negative lw-emc-add-cancel lw-emc-double lw-emc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-emc-quarter-sum
 (implies (rationalp eta) (equal (+ (* 1/4 eta) (* 3/4 eta)) eta))
 :hints (("Goal" :nonlinearp t))))

(defthm lw-euler-square-model-cell-clearance
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp cell) (< cell coarse)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (not (lw-complex-diskp (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0) (* 1/4 eta))))
 :hints (("Goal"
 :use (lw-euler-square-polynomial-budget-data lw-euler-square-base-line-value-clearance
       (:instance lw-euler-polygon-index-check-data (points (lw-polynomial-square-boundary anchor side coarse)) (step (lw-polynomial-grid-step side coarse)))
       (:instance lw-euler-positive-square-model-valid)
       (:instance lw-polynomial-grid-step-data (count coarse))
       (:instance lw-polynomial-square-line-point-contained (count coarse) (index cell))
       (:instance lw-polynomial-square-line-point-contained (count coarse) (index (+ 1 cell)))
       (:instance lw-polynomial-square-line-step-exact (count coarse) (index cell))
       (:instance lw-square-segment-contained (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))))
       (:instance lw-polynomial-square-segment-variation
        (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))) (step (lw-polynomial-grid-step side coarse)))
       (:instance lw-euler-positive-square-model-cauchy
        (left-target base-target) (left-error base-error) (right-target target) (right-error error) (point (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side target error)) (point (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter)) (offset 0))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0)) (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0)) (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) 0))
        (radius (* 1/4 (+ base-error error))) (other-radius (* (lw-polynomial-grid-step side coarse) (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side)))))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) 0)))
        (radius (+ (* 1/4 (+ base-error error)) (* (lw-polynomial-grid-step side coarse) (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side))))) (cap (* 3/4 eta)))
       (:instance lw-complex-perturbation-excludes-small
        (left (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell))
        (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0))
        (epsilon (* 1/4 eta)) (delta (* 3/4 eta))))
 :in-theory (union-theories
 '(lw-emc-quarter-sum fold-consts-in-+ lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-square-containsp lw-polynomial-line-value lw-polynomial-edge-cap lw-emc-left-commutes lw-emc-left-distributes lw-emc-fold-constants lw-emc-times-negative lw-emc-negative-times lw-emc-zero-times lw-emc-minus-one lw-emc-double-negative lw-emc-add-cancel lw-emc-double lw-emc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-model-side-clearance
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
  (not (lw-complex-diskp (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) parameter) 0) (* 1/4 eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data
        (:instance lw-unit-mesh-cell-data (count coarse))
        (:instance lw-complex-segment-mesh-cover (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge)) (count coarse))
        (:instance lw-euler-square-model-cell-clearance
          (cell (lw-unit-mesh-cell coarse parameter)) (parameter (lw-unit-mesh-local-parameter coarse parameter))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complexp lw-emc-left-commutes lw-emc-left-distributes lw-emc-fold-constants lw-emc-times-negative lw-emc-negative-times lw-emc-zero-times lw-emc-minus-one lw-emc-double-negative lw-emc-add-cancel lw-emc-double lw-emc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-emc-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-emc-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-emc-unit-fraction
 (implies (and (posp count) (natp index) (<= index count))
  (and (rationalp (* index (/ count))) (<= 0 (* index (/ count))) (<= (* index (/ count)) 1)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value count))
        (:instance lw-emc-multiply-order (a 0) (b index) (factor (/ count)))
        (:instance lw-positive-division-bound (numerator index) (divisor count) (bound 1)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-emc-product-rational lw-emc-inverse-rational lw-emc-left-commutes lw-emc-left-distributes lw-emc-fold-constants lw-emc-times-negative lw-emc-negative-times lw-emc-zero-times lw-emc-minus-one lw-emc-double-negative lw-emc-add-cancel lw-emc-double lw-emc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-euler-square-model-line-point-clearance
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (posp count) (natp index) (<= index count)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
  (not (lw-complex-diskp (lw-polynomial-line-value (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) count index) (* 1/4 eta))))
 :hints (("Goal"
  :use (lw-emc-unit-fraction
        (:instance lw-euler-square-model-side-clearance (parameter (* index (/ count)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-value lw-polynomial-line-point lw-emc-left-commutes lw-emc-left-distributes lw-emc-fold-constants lw-emc-times-negative lw-emc-negative-times lw-emc-zero-times lw-emc-minus-one lw-emc-double-negative lw-emc-add-cancel lw-emc-double lw-emc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
