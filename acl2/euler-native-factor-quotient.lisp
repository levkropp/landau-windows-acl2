(in-package "ACL2")

(include-book "euler-normalized-square-derivative")

; The factor quotient and native quotient use the same square coordinate.

(local (defthm lw-enf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enf-times-negative (a b) (b a)))
                 :in-theory (disable lw-enf-times-negative)))))

(local (defthm lw-enf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enf-left-commutes)))))

(defun lw-euler-square-native-normalized-quotient (anchor side point derivative-error value-error)
 (let* ((physical-point (lw-polynomial-square-forward anchor side point))
        (radius (* 1/4 (car anchor))))
  (lw-complex-quotient
   (lw-complex-scale (* 1/2 side)
    (lw-complex-euler-local-coefficient-value (car physical-point) (cdr physical-point) radius 1 derivative-error))
   (lw-complex-euler-continuation-value (car physical-point) (cdr physical-point) value-error))))

(defthm lw-euler-normalized-square-native-value-error
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta) (lw-unit-square-pointp point)) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0) (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) value-error)) (+ (* 1/4 error) (* 1/4 value-error))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-positive-square-model-valid
        lw-unit-square-point-coordinates lw-polynomial-square-forward-contained
        (:instance lw-polynomial-square-normalize-evaluation (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-euler-positive-square-model-comparison (point (lw-polynomial-square-forward anchor side point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-enf-left-commutes lw-enf-left-distributes lw-enf-fold-constants lw-enf-times-negative lw-enf-negative-times lw-enf-zero-times lw-enf-minus-one lw-enf-double-negative lw-enf-add-cancel lw-enf-double lw-enf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-enf-clearance
 (implies (and (lw-complexp original) (lw-complexp value) (rationalp eta) (< 0 eta)
               (rationalp error-cap) (<= error-cap (* 1/8 eta))
               (not (lw-complex-diskp original (* 1/4 eta)))
               (lw-complex-diskp (lw-complex-sub original value) error-cap))
  (and (<= (* 1/64 eta eta) (lw-complex-norm-square original))
       (<= (* 1/64 eta eta) (lw-complex-norm-square value))))
 :hints (("Goal"
  :use ((:instance lw-complex-difference-symmetric (left original) (right value) (radius error-cap))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub value original)) (radius error-cap) (cap (* 1/8 eta)))
        (:instance lw-complex-perturbation-excludes-small (left original) (right value)
                   (epsilon (* 1/8 eta)) (delta (* 1/8 eta)))
        (:instance lw-complex-disk-norm-square (point value) (radius (* 1/8 eta)))
        (:instance lw-complex-disk-norm-square (point original) (radius (* 1/4 eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-enf-left-commutes lw-enf-left-distributes lw-enf-fold-constants lw-enf-times-negative lw-enf-negative-times lw-enf-zero-times lw-enf-minus-one lw-enf-double-negative lw-enf-add-cancel lw-enf-double lw-enf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(defthm lw-euler-square-native-quotient-error
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))) (<= error (* 1/4 eta)) (rationalp derivative-error) (< 0 derivative-error) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/4 eta)))
  (lw-complex-diskp (lw-complex-sub (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error) (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0))) (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-positive-square-model-valid lw-unit-square-point-coordinates
        lw-euler-normalized-square-derivative-bound lw-euler-model-normalized-boundary-clearance
        lw-euler-normalized-square-native-derivative-error lw-euler-normalized-square-native-value-error
        lw-polynomial-square-forward-contained lw-euler-square-inner-radius-data
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (offset 0))
        (:instance lw-complex-polynomial-derivative-rational
          (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)))
        (:instance lw-complex-euler-continuation-value-rational
          (rate (car (lw-polynomial-square-forward anchor side point))) (height (cdr (lw-polynomial-square-forward anchor side point))) (error value-error))
        (:instance lw-complex-euler-local-coefficient-rational
          (rate (car (lw-polynomial-square-forward anchor side point))) (height (cdr (lw-polynomial-square-forward anchor side point))) (radius (* 1/4 (car anchor))) (index 1) (error derivative-error))
        (:instance lw-complex-scale-rational (point (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) 1 derivative-error)) (factor (* 1/2 side)))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point)) (right (lw-complex-scale (* 1/2 side) (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) 1 derivative-error))) (radius (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)) (right (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) value-error)) (radius (+ (* 1/4 error) (* 1/4 value-error))))
        (:instance lw-enf-clearance (original (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)) (value (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) value-error)) (error-cap (+ (* 1/4 error) (* 1/4 value-error))))
        (:instance lw-complex-quotient-difference-bound
          (numerator (lw-complex-scale (* 1/2 side) (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) 1 derivative-error))) (denominator (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) value-error)) (approximate-numerator (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point))
          (approximate-denominator (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)) (left-clearance (* 1/8 eta)) (right-clearance (* 1/8 eta))
          (numerator-cap (lw-euler-normalized-square-derivative-cap anchor side)) (numerator-error (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (denominator-error (+ (* 1/4 error) (* 1/4 value-error)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-square-native-normalized-quotient lw-square-containsp lw-complexp lw-positive-squarep lw-enf-left-commutes lw-enf-left-distributes lw-enf-fold-constants lw-enf-times-negative lw-enf-negative-times lw-enf-zero-times lw-enf-minus-one lw-enf-double-negative lw-enf-add-cancel lw-enf-double lw-enf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



(local (defthm lw-enf-native-quotient-rational
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
 '(fold-consts-in-+ lw-euler-square-native-normalized-quotient lw-square-containsp lw-complexp lw-positive-squarep lw-enf-left-commutes lw-enf-left-distributes lw-enf-fold-constants lw-enf-times-negative lw-enf-negative-times lw-enf-zero-times lw-enf-minus-one lw-enf-double-negative lw-enf-add-cancel lw-enf-double lw-enf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-enf-model-quotient-rational
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta) (lw-unit-square-pointp point)) (lw-complexp (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-positive-square-model-valid lw-unit-square-point-coordinates
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (offset 0))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)))
        (:instance lw-complex-quotient-rational (numerator (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point)) (denominator (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-enf-left-commutes lw-enf-left-distributes lw-enf-fold-constants lw-enf-times-negative lw-enf-negative-times lw-enf-zero-times lw-enf-minus-one lw-enf-double-negative lw-enf-add-cancel lw-enf-double lw-enf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-enf-factor-quotient-rational
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (lw-complexp (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point) (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check lw-unit-square-point-coordinates
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-normalization-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-normalization-boundary-check (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-factor-polynomial-valid (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta))))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance)) (offset 0))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance)))
        (:instance lw-complex-quotient-rational (numerator (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point)) (denominator (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-factor-polynomial lw-enf-left-commutes lw-enf-left-distributes lw-enf-fold-constants lw-enf-times-negative lw-enf-negative-times lw-enf-zero-times lw-enf-minus-one lw-enf-double-negative lw-enf-add-cancel lw-enf-double lw-enf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-euler-square-native-factor-quotient-error
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))) (<= error (* 1/4 eta)) (rationalp derivative-error) (< 0 derivative-error) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/4 eta)) (<= tolerance (* 1/8 eta)))
  (lw-complex-diskp (lw-complex-sub (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point) (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0)) (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)) (+ (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error)))))))
 :hints (("Goal"
  :use (lw-euler-model-factor-contour-fixed-quotient-error lw-euler-square-native-quotient-error lw-enf-factor-quotient-rational
        lw-enf-native-quotient-rational lw-enf-model-quotient-rational
        (:instance lw-complex-difference-symmetric (left (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error)) (right (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0))) (radius (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error))))))
        (:instance lw-complex-difference-triangle (left (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point) (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0))) (middle (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0))) (right (lw-euler-square-native-normalized-quotient anchor side point derivative-error value-error))
                   (radius (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance))) (other-radius (+ (* (/ (* 1/8 eta)) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))) (* (lw-euler-normalized-square-derivative-cap anchor side) (/ (* 1/8 eta)) (/ (* 1/8 eta)) (+ (* 1/4 error) (* 1/4 value-error)))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-enf-left-commutes lw-enf-left-distributes lw-enf-fold-constants lw-enf-times-negative lw-enf-negative-times lw-enf-zero-times lw-enf-minus-one lw-enf-double-negative lw-enf-add-cancel lw-enf-double lw-enf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
