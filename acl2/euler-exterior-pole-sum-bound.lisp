(in-package "ACL2")

(include-book "euler-factor-pole-sum")
(include-book "euler-interior-pole-sum-bound")
(include-book "unit-square-pole-split")

; Bound the exterior sum via the bounded full quotient and interior sum.

(local (defthm lw-eps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eps-times-negative (a b) (b a)))
                 :in-theory (disable lw-eps-times-negative)))))

(local (defthm lw-eps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eps-left-commutes)))))

(defun lw-euler-exterior-pole-sum (anchor side coarse target error eta tolerance point)
 (lw-polynomial-factor-log-sum
  (lw-unit-square-outside-roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))
  point))

(defun lw-euler-exterior-pole-sum-cap (anchor side coarse base-target base-error eta)
 (+ (* (+ (lw-euler-normalized-square-derivative-cap anchor side) (* 1/4 eta)) (/ (* 1/8 eta))) (lw-euler-interior-pole-sum-cap anchor side coarse base-target base-error eta)))

(defthm lw-euler-exterior-pole-roots-valid
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-exterior-rootsp (lw-unit-square-outside-roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))))
 :hints (("Goal" :use (lw-euler-model-accurate-roots-data
                        (:instance lw-unit-square-exterior-roots-data (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-factor-pole-sum-split
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point))
  (equal (lw-polynomial-factor-log-sum (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) point) (lw-complex-add (lw-polynomial-factor-log-sum (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance) point) (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point))))
 :hints (("Goal"
  :use (lw-euler-model-accurate-roots-data lw-unit-square-point-coordinates
        (:instance lw-unit-square-factor-log-sum-split (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-inside-roots lw-euler-exterior-pole-sum lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eps-quotient-bound
 (implies (and (lw-complexp value) (rationalp margin) (< 0 margin)
               (not (lw-complex-diskp value margin))
               (lw-complex-diskp numerator bound))
  (lw-complex-diskp (lw-complex-quotient numerator value) (* bound (/ margin))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-norm-square (point value) (radius margin))
        (:instance lw-complex-reciprocal-disk-bound (point value) (lower margin))
        (:instance lw-complex-mul-disk (left numerator) (right (lw-complex-reciprocal value))
         (radius bound) (other-radius (/ margin))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-quotient lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-eps-factor-polynomial-valid
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-complex-coefficientsp (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-normalization-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-normalization-boundary-check (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-factor-polynomial-valid (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-factor-polynomial lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-eps-difference-add-cancel
 (implies (and (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-add (lw-complex-sub left right) right) left))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-full-pole-sum-bound
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta)) (<= error (* 1/2 (car anchor))))
  (lw-complex-diskp (lw-polynomial-factor-log-sum (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) point) (* (+ (lw-euler-normalized-square-derivative-cap anchor side) (* 1/4 eta)) (/ (* 1/8 eta)))))
 :hints (("Goal"
  :use (lw-euler-factor-pole-sum-identity lw-euler-square-polynomial-budget-data
        lw-euler-model-factor-request-data lw-euler-model-factor-contour-derivative-error lw-euler-normalized-square-derivative-bound
        lw-eps-factor-polynomial-valid lw-unit-square-point-coordinates
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance)) (offset 0))
        (:instance lw-complex-disk-data (point (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point)) (radius (lw-euler-normalized-square-derivative-cap anchor side)))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point)) (right (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point)) (radius (* 2 (lw-euler-model-factor-request anchor side coarse target error eta tolerance))))
        (:instance lw-complex-add-disk (left (lw-complex-sub (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point) (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point))) (right (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point))
         (radius (* 2 (lw-euler-model-factor-request anchor side coarse target error eta tolerance))) (other-radius (lw-euler-normalized-square-derivative-cap anchor side)))
        (:instance lw-eps-difference-add-cancel (left (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point)) (right (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point)) (radius (+ (* 2 (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (lw-euler-normalized-square-derivative-cap anchor side)))
         (cap (+ (lw-euler-normalized-square-derivative-cap anchor side) (* 1/4 eta))))
        (:instance lw-eps-quotient-bound (value (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0)) (numerator (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point))
         (margin (* 1/8 eta)) (bound (+ (lw-euler-normalized-square-derivative-cap anchor side) (* 1/4 eta)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-eps-factor-polynomial-valid lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-exterior-pole-sum-bound
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta)) (<= error (* 1/2 (car anchor)))) (lw-complex-diskp (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point) (lw-euler-exterior-pole-sum-cap anchor side coarse base-target base-error eta)))
 :hints (("Goal"
  :use (lw-euler-full-pole-sum-bound lw-euler-interior-pole-sum-bound lw-euler-factor-pole-sum-split
        lw-euler-model-accurate-roots-data lw-unit-square-point-coordinates
        (:instance lw-unit-square-outside-roots-valid (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)))
        (:instance lw-polynomial-factor-log-sum-rational (roots (lw-unit-square-outside-roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))))
        (:instance lw-polynomial-factor-log-sum-rational (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
        (:instance lw-complex-sub-add-cancel (a (lw-polynomial-factor-log-sum (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance) point)) (b (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)))
        (:instance lw-complex-sub-disk (left (lw-polynomial-factor-log-sum (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) point)) (right (lw-polynomial-factor-log-sum (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance) point))
         (radius (* (+ (lw-euler-normalized-square-derivative-cap anchor side) (* 1/4 eta)) (/ (* 1/8 eta)))) (other-radius (lw-euler-interior-pole-sum-cap anchor side coarse base-target base-error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-exterior-pole-sum-cap lw-euler-exterior-pole-sum lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-split-pole-quotient-error
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))) (<= error (* 1/4 eta)) (rationalp derivative-error) (< 0 derivative-error) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/4 eta)) (<= tolerance (* 1/8 eta)))
  (lw-complex-diskp (lw-complex-sub (lw-complex-add (lw-polynomial-factor-log-sum (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance) point) (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)) (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)) (+ (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error)))))))
 :hints (("Goal"
  :use (lw-euler-native-factor-pole-sum-error lw-euler-factor-pole-sum-split)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
