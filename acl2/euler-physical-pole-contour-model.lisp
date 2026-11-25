(in-package "ACL2")

(include-book "euler-accurate-pole-candidates")
(include-book "euler-exterior-pole-sum-bound")
(include-book "square-pole-coordinate-transport")

; The selected poles and the exterior model use physical coordinates.

(local (defthm lw-epc2-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epc2-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epc2-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epc2-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epc2-times-negative (a b) (b a)))
                 :in-theory (disable lw-epc2-times-negative)))))

(local (defthm lw-epc2-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epc2-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epc2-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epc2-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epc2-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epc2-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epc2-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epc2-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epc2-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epc2-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epc2-left-commutes)))))

(local (defthm lw-epc2-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-interior-pole-sum-coordinate-identity
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (equal (lw-complex-scale (* 1/2 side) (lw-factor-model-log-sum (lw-polynomial-square-forward anchor side point) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance))) (lw-polynomial-factor-log-sum (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance) point)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-accurate-roots-data lw-unit-square-point-coordinates
        (:instance lw-square-unit-pole-sum-coordinate-identity (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-pole-candidates lw-epc2-left-commutes lw-epc2-left-distributes lw-epc2-fold-constants lw-epc2-times-negative lw-epc2-negative-times lw-epc2-zero-times lw-epc2-minus-one lw-epc2-double-negative lw-epc2-add-cancel lw-epc2-double lw-epc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-physical-exterior-pole-sum-bound
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta)) (<= error (* 1/2 (car anchor)))) (lw-complex-diskp (lw-complex-scale (* 2 (/ side)) (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)) (* (* 2 (/ side)) (lw-euler-exterior-pole-sum-cap anchor side coarse base-target base-error eta))))
 :hints (("Goal"
  :use (lw-euler-exterior-pole-sum-bound lw-euler-square-polynomial-budget-data
        (:instance lw-reciprocal-positive (value side))
        (:instance lw-complex-scale-disk (point (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)) (factor (* 2 (/ side))) (radius (lw-euler-exterior-pole-sum-cap anchor side coarse base-target base-error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ abs lw-epc2-inverse-rational lw-epc2-left-commutes lw-epc2-left-distributes lw-epc2-fold-constants lw-epc2-times-negative lw-epc2-negative-times lw-epc2-zero-times lw-epc2-minus-one lw-epc2-double-negative lw-epc2-add-cancel lw-epc2-double lw-epc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-pole-contour-model
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))) (<= error (* 1/4 eta)) (rationalp derivative-error) (< 0 derivative-error) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/4 eta)) (<= tolerance (* 1/8 eta)))
  (lw-complex-diskp (lw-complex-sub (lw-complex-add (lw-complex-scale (* 1/2 side) (lw-factor-model-log-sum (lw-polynomial-square-forward anchor side point) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance))) (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)) (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)) (+ (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error)))))))
 :hints (("Goal"
  :use (lw-euler-interior-pole-sum-coordinate-identity lw-euler-native-split-pole-quotient-error)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-epc2-left-commutes lw-epc2-left-distributes lw-epc2-fold-constants lw-epc2-times-negative lw-epc2-negative-times lw-epc2-zero-times lw-epc2-minus-one lw-epc2-double-negative lw-epc2-add-cancel lw-epc2-double lw-epc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-epc2-native-quotient-rational
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta) (lw-unit-square-pointp point)) (rationalp derivative-error) (< 0 derivative-error)
               (rationalp value-error) (< 0 value-error))
          (lw-complexp (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-polynomial-square-forward-contained
        (:instance lw-complex-euler-continuation-value-rational
          (rate (car (lw-polynomial-square-forward anchor side point))) (height (cdr (lw-polynomial-square-forward anchor side point))) (error value-error))
        (:instance lw-complex-euler-local-coefficient-rational
          (rate (car (lw-polynomial-square-forward anchor side point))) (height (cdr (lw-polynomial-square-forward anchor side point))) (radius (* 1/4 (car anchor))) (index 1) (error derivative-error))
        (:instance lw-complex-scale-rational (point (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (* 1/4 (car anchor)) 1 derivative-error)) (factor (* 1/2 side)))
        (:instance lw-complex-quotient-rational (numerator (lw-complex-scale (* 1/2 side) (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (* 1/4 (car anchor)) 1 derivative-error))) (denominator (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) value-error))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-square-native-normalized-quotient lw-square-containsp lw-complexp lw-positive-squarep lw-epc2-left-commutes lw-epc2-left-distributes lw-epc2-fold-constants lw-epc2-times-negative lw-epc2-negative-times lw-epc2-zero-times lw-epc2-minus-one lw-epc2-double-negative lw-epc2-add-cancel lw-epc2-double lw-epc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-epc2-physical-difference
 (implies (and (rationalp side) (< 0 side) (lw-complexp poles) (lw-complexp exterior)
               (lw-complexp native))
  (equal (lw-complex-scale (* 2 (/ side))
            (lw-complex-sub (lw-complex-add (lw-complex-scale (* 1/2 side) poles) exterior) native))
         (lw-complex-sub (lw-complex-add poles (lw-complex-scale (* 2 (/ side)) exterior))
                         (lw-complex-scale (* 2 (/ side)) native))))
 :hints (("Goal"
  :use ((:instance lw-epc2-inverse-factor (divisor side) (coefficient (car poles)))
        (:instance lw-epc2-inverse-factor (divisor side) (coefficient (cdr poles))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-scale lw-complex-sub lw-complex-add lw-epc2-inverse-rational lw-epc2-left-commutes lw-epc2-left-distributes lw-epc2-fold-constants lw-epc2-times-negative lw-epc2-negative-times lw-epc2-zero-times lw-epc2-minus-one lw-epc2-double-negative lw-epc2-add-cancel lw-epc2-double lw-epc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-native-physical-pole-contour-model
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))) (<= error (* 1/4 eta)) (rationalp derivative-error) (< 0 derivative-error) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/4 eta)) (<= tolerance (* 1/8 eta)) (<= (+ (car anchor) side) 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-add (lw-factor-model-log-sum (lw-polynomial-square-forward anchor side point) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)) (lw-complex-scale (* 2 (/ side)) (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point))) (lw-complex-scale (* 2 (/ side)) (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)))
                   (* (* 2 (/ side)) (+ (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error))))))))
 :hints (("Goal"
  :use (lw-euler-native-pole-contour-model lw-euler-square-polynomial-budget-data
        lw-euler-model-accurate-pole-candidates-data lw-unit-square-point-coordinates
        lw-euler-exterior-pole-sum-bound lw-epc2-native-quotient-rational
        (:instance lw-complex-disk-data (point (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)) (radius (lw-euler-exterior-pole-sum-cap anchor side coarse base-target base-error eta)))
        (:instance lw-polynomial-square-map-data)
        (:instance lw-factor-model-rational (point (lw-polynomial-square-forward anchor side point)) (entries (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)))
        (:instance lw-epc2-physical-difference (poles (lw-factor-model-log-sum (lw-polynomial-square-forward anchor side point) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance))) (exterior (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)) (native (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)))
        (:instance lw-reciprocal-positive (value side))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-add (lw-complex-scale (* 1/2 side) (lw-factor-model-log-sum (lw-polynomial-square-forward anchor side point) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance))) (lw-euler-exterior-pole-sum anchor side coarse target error eta tolerance point)) (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)))
         (factor (* 2 (/ side))) (radius (+ (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error))))))))
  :in-theory (union-theories
 '(fold-consts-in-+ abs lw-epc2-inverse-rational lw-epc2-left-commutes lw-epc2-left-distributes lw-epc2-fold-constants lw-epc2-times-negative lw-epc2-negative-times lw-epc2-zero-times lw-epc2-minus-one lw-epc2-double-negative lw-epc2-add-cancel lw-epc2-double lw-epc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
