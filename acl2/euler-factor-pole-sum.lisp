(in-package "ACL2")

(include-book "euler-native-factor-quotient")
(include-book "polynomial-factor-log-sum")

; The complete finite root family recovers the native boundary quotient.

(local (defthm lw-epsm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epsm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epsm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epsm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epsm-times-negative (a b) (b a)))
                 :in-theory (disable lw-epsm-times-negative)))))

(local (defthm lw-epsm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epsm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epsm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epsm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epsm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epsm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epsm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epsm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epsm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epsm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epsm-left-commutes)))))

(local (defthm lw-epsm-factor-boundary-value
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point))
  (and (lw-complexp (lw-polynomial-linear-factor-value (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))) point)) (equal (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0) (lw-polynomial-linear-factor-value (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))) point))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        lw-euler-model-accurate-roots-data lw-unit-square-point-coordinates
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-normalization-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-normalization-boundary-check (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-accurate-data (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta))))
        (:instance lw-polynomial-factor-coefficients-evaluation (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)))))
        (:instance lw-polynomial-linear-factor-value-rational (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-factor-polynomial lw-polynomial-square-factor-polynomial lw-euler-model-accurate-roots lw-polynomial-square-accurate-normalized-roots lw-epsm-left-commutes lw-epsm-left-distributes lw-epsm-fold-constants lw-epsm-times-negative lw-epsm-negative-times lw-epsm-zero-times lw-epsm-minus-one lw-epsm-double-negative lw-epsm-add-cancel lw-epsm-double lw-epsm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-factor-pole-sum-identity
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta)))
  (and (not (lw-complex-diskp (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0) (* 1/8 eta))) (equal (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point) (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0)) (lw-polynomial-factor-log-sum (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) point))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        lw-euler-model-accurate-roots-data lw-euler-model-factor-request-data lw-unit-square-point-coordinates
        lw-unit-square-point-in-derivative-disk lw-euler-model-normalized-boundary-clearance lw-epsm-factor-boundary-value
        (:instance lw-complex-disk-enlarge (radius 3/2) (cap 2))
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-normalization-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-normalization-boundary-check (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-accurate-data (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta))))
        lw-euler-model-accurate-disk-approximation
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (offset 0))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)) (right (lw-polynomial-linear-factor-value (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))) point)) (radius (lw-euler-model-factor-request anchor side coarse target error eta tolerance)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-polynomial-linear-factor-value (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))) point) (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0))) (radius (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (cap (* 1/8 eta)))
        (:instance lw-complex-perturbation-excludes-small (left (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)) (right (lw-polynomial-linear-factor-value (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))) point)) (epsilon (* 1/8 eta)) (delta (* 1/8 eta)))
        (:instance lw-complex-zero-disk (radius (* 1/8 eta)))
        (:instance lw-polynomial-factor-log-derivative (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-factor-polynomial lw-polynomial-square-factor-polynomial lw-euler-model-accurate-roots lw-polynomial-square-accurate-normalized-roots lw-epsm-left-commutes lw-epsm-left-distributes lw-epsm-fold-constants lw-epsm-times-negative lw-epsm-negative-times lw-epsm-zero-times lw-epsm-minus-one lw-epsm-double-negative lw-epsm-add-cancel lw-epsm-double lw-epsm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-native-factor-pole-sum-error
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))) (<= error (* 1/4 eta)) (rationalp derivative-error) (< 0 derivative-error) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/4 eta)) (<= tolerance (* 1/8 eta)))
  (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) point) (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)) (+ (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error)))))))
 :hints (("Goal"
  :use (lw-euler-factor-pole-sum-identity lw-euler-square-native-factor-quotient-error)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-epsm-left-commutes lw-epsm-left-distributes lw-epsm-fold-constants lw-epsm-times-negative lw-epsm-negative-times lw-epsm-zero-times lw-epsm-minus-one lw-epsm-double-negative lw-epsm-add-cancel lw-epsm-double lw-epsm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
