(in-package "ACL2")

(include-book "euler-normalized-square-derivative")

; Retain the full margin of the fixed base polynomial.

(local (defthm lw-ebm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ebm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ebm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ebm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ebm-times-negative (a b) (b a)))
                 :in-theory (disable lw-ebm-times-negative)))))

(local (defthm lw-ebm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ebm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ebm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ebm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ebm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ebm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ebm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ebm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ebm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ebm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ebm-left-commutes)))))

(local (defthm lw-ebm-budget-sum
 (implies (rationalp eta) (equal (+ (* 3/4 eta) (* 1/4 eta)) eta))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ebm-left-commutes lw-ebm-left-distributes lw-ebm-fold-constants lw-ebm-times-negative lw-ebm-negative-times lw-ebm-zero-times lw-ebm-minus-one lw-ebm-double-negative lw-ebm-add-cancel lw-ebm-double lw-ebm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-euler-base-cell-boundary-margin
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp cell) (< cell coarse)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (not (lw-complex-diskp (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0) (* 3/4 eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-square-base-line-value-clearance
        (:instance lw-polynomial-square-line-point-contained (count coarse) (index cell))
        (:instance lw-polynomial-square-line-point-contained (count coarse) (index (+ 1 cell)))
        (:instance lw-polynomial-square-line-step-exact (count coarse) (index cell))
        (:instance lw-square-segment-contained (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))))
        (:instance lw-polynomial-square-segment-variation
         (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))) (step (lw-polynomial-grid-step side coarse)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter)) (offset 0))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) 0)))
         (radius (* (lw-polynomial-grid-step side coarse) (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side)))) (cap (* 1/4 eta)))
        (:instance lw-complex-perturbation-excludes-small (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) 0)) (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0))
         (epsilon (* 3/4 eta)) (delta (* 1/4 eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-square-containsp lw-polynomial-line-value lw-polynomial-edge-cap lw-ebm-budget-sum lw-ebm-left-commutes lw-ebm-left-distributes lw-ebm-fold-constants lw-ebm-times-negative lw-ebm-negative-times lw-ebm-zero-times lw-ebm-minus-one lw-ebm-double-negative lw-ebm-add-cancel lw-ebm-double lw-ebm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-base-side-boundary-margin
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (not (lw-complex-diskp (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-complex-segment (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) parameter) 0) (* 3/4 eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data
        (:instance lw-unit-mesh-cell-data (count coarse))
        (:instance lw-complex-segment-mesh-cover (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge)) (count coarse))
        (:instance lw-euler-base-cell-boundary-margin (cell (lw-unit-mesh-cell coarse parameter))
         (parameter (lw-unit-mesh-local-parameter coarse parameter))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complexp lw-ebm-left-commutes lw-ebm-left-distributes lw-ebm-fold-constants lw-ebm-times-negative lw-ebm-negative-times lw-ebm-zero-times lw-ebm-minus-one lw-ebm-double-negative lw-ebm-add-cancel lw-ebm-double lw-ebm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-base-normalized-boundary-margin
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (lw-unit-square-pointp point))
  (not (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) point 0) (* 3/4 eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-unit-square-edge-data lw-unit-square-point-coordinates
        (:instance lw-polynomial-square-normalize-evaluation (coefficients (lw-euler-positive-square-model anchor side base-target base-error)))
        (:instance lw-polynomial-square-forward-side (edge (lw-unit-square-edge-number point)) (parameter (lw-unit-square-edge-parameter point)))
        (:instance lw-euler-base-side-boundary-margin (edge (lw-unit-square-edge-number point)) (parameter (lw-unit-square-edge-parameter point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ebm-left-commutes lw-ebm-left-distributes lw-ebm-fold-constants lw-ebm-times-negative lw-ebm-negative-times lw-ebm-zero-times lw-ebm-minus-one lw-ebm-double-negative lw-ebm-add-cancel lw-ebm-double lw-ebm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
