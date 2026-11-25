(in-package "ACL2")

(include-book "euler-model-accurate-factors")
(include-book "polynomial-factor-quotient-comparison")

; The canonical Euler certificate transfers to the normalized contour.

(local (defthm lw-efc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-efc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-efc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-efc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-efc-times-negative (a b) (b a)))
                 :in-theory (disable lw-efc-times-negative)))))

(local (defthm lw-efc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-efc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-efc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-efc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-efc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-efc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-efc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-efc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-efc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-efc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-efc-left-commutes)))))

(defun lw-euler-model-factor-polynomial (anchor side coarse target error eta tolerance)
 (let* ((coefficients (lw-euler-positive-square-model anchor side target error))
        (count (lw-euler-model-square-count anchor side coarse target error eta)))
  (lw-polynomial-square-factor-polynomial
   (lw-polynomial-square-normalize coefficients anchor side)
   (lw-polynomial-normalization-count coefficients anchor side count)
   tolerance)))

(defthm lw-euler-model-normalized-boundary-clearance
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)
               (lw-unit-square-pointp point))
  (not (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0) (* 1/4 eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-positive-square-model-valid
        lw-unit-square-edge-data lw-unit-square-point-coordinates
        (:instance lw-polynomial-square-normalize-evaluation (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-square-forward-side
          (edge (lw-unit-square-edge-number point)) (parameter (lw-unit-square-edge-parameter point)))
        (:instance lw-euler-square-model-side-clearance
          (edge (lw-unit-square-edge-number point)) (parameter (lw-unit-square-edge-parameter point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-efc-left-commutes lw-efc-left-distributes lw-efc-fold-constants lw-efc-times-negative lw-efc-negative-times lw-efc-zero-times lw-efc-minus-one lw-efc-double-negative lw-efc-add-cancel lw-efc-double lw-efc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-factor-contour-derivative-error
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point))
   (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point)) (* 2 (lw-euler-model-factor-request anchor side coarse target error eta tolerance))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data
        lw-euler-model-square-boundary-check lw-unit-square-point-in-derivative-disk
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-normalization-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-normalization-boundary-check (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-factor-derivative-error (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta))) (center point)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-factor-polynomial lw-euler-model-factor-request lw-polynomial-square-normalized-request lw-efc-left-commutes lw-efc-left-distributes lw-efc-fold-constants lw-efc-times-negative lw-efc-negative-times lw-efc-zero-times lw-efc-minus-one lw-efc-double-negative lw-efc-add-cancel lw-efc-double lw-efc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-model-factor-contour-quotient-error
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta))
               (rationalp numerator-cap) (<= 0 numerator-cap)
               (lw-complex-diskp (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) numerator-cap))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point) (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0)) (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)))
   (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) numerator-cap) (lw-euler-model-factor-request anchor side coarse target error eta tolerance))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        lw-unit-square-point-in-derivative-disk lw-euler-model-normalized-boundary-clearance
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-normalization-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-normalization-boundary-check (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-factor-quotient-error (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta)))
                   (center point) (clearance (* 1/8 eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-factor-polynomial lw-euler-model-factor-request lw-polynomial-square-normalized-request lw-efc-left-commutes lw-efc-left-distributes lw-efc-fold-constants lw-efc-times-negative lw-efc-negative-times lw-efc-zero-times lw-efc-minus-one lw-efc-double-negative lw-efc-add-cancel lw-efc-double lw-efc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
