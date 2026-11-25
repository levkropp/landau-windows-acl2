(in-package "ACL2")

(include-book "euler-square-derivative")
(include-book "euler-factor-contour-comparison")

; Compare derivatives in the same normalized coordinate as the factors.

(local (defthm lw-ens-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ens-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ens-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ens-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ens-times-negative (a b) (b a)))
                 :in-theory (disable lw-ens-times-negative)))))

(local (defthm lw-ens-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ens-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ens-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ens-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ens-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ens-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ens-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ens-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ens-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ens-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ens-left-commutes)))))

(local (defthm lw-ens-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ens-mul-real
 (implies (and (rationalp factor) (lw-complexp point))
  (equal (lw-complex-mul (cons factor 0) point) (lw-complex-scale factor point)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-mul lw-complex-scale lw-ens-left-commutes lw-ens-left-distributes lw-ens-fold-constants lw-ens-times-negative lw-ens-negative-times lw-ens-zero-times lw-ens-minus-one lw-ens-double-negative lw-ens-add-cancel lw-ens-double lw-ens-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ens-scale-difference
 (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-scale factor (lw-complex-sub a b))
         (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-scale lw-ens-left-commutes lw-ens-left-distributes lw-ens-fold-constants lw-ens-times-negative lw-ens-negative-times lw-ens-zero-times lw-ens-minus-one lw-ens-double-negative lw-ens-add-cancel lw-ens-double lw-ens-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-square-normalized-derivative
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor)
               (rationalp side) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (lw-polynomial-square-normalize coefficients anchor side) point)
         (lw-complex-scale (* 1/2 side) (lw-complex-polynomial-derivative coefficients (lw-polynomial-square-forward anchor side point)))))
 :hints (("Goal"
  :use (lw-polynomial-trim-valid lw-polynomial-square-map-data
        (:instance lw-polynomial-affine-derivative
         (coefficients (lw-polynomial-trim coefficients))
         (center (lw-polynomial-square-center anchor side)) (slope (lw-polynomial-square-slope side)))
        (:instance lw-polynomial-trim-derivative (point (lw-polynomial-square-forward anchor side point)))
        (:instance lw-complex-polynomial-derivative-rational (point (lw-polynomial-square-forward anchor side point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-normalize lw-polynomial-square-forward lw-polynomial-square-slope lw-ens-mul-real lw-ens-product-rational lw-ens-left-commutes lw-ens-left-distributes lw-ens-fold-constants lw-ens-times-negative lw-ens-negative-times lw-ens-zero-times lw-ens-minus-one lw-ens-double-negative lw-ens-add-cancel lw-ens-double lw-ens-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-square-forward-contained
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (lw-unit-square-pointp point))
  (lw-square-containsp anchor side (lw-polynomial-square-forward anchor side point)))
 :hints (("Goal" :use (lw-unit-square-point-coordinates)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-square-containsp lw-polynomial-square-forward lw-polynomial-square-center lw-polynomial-square-slope lw-complexp lw-complex-add lw-complex-mul lw-ens-product-rational lw-ens-left-commutes lw-ens-left-distributes lw-ens-fold-constants lw-ens-times-negative lw-ens-negative-times lw-ens-zero-times lw-ens-minus-one lw-ens-double-negative lw-ens-add-cancel lw-ens-double lw-ens-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defun lw-euler-normalized-square-derivative-cap (anchor side)
 (* 1/2 side (lw-euler-square-derivative-cap anchor side)))

(defthm lw-euler-normalized-square-derivative-bound
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))))
  (and (rationalp (lw-euler-normalized-square-derivative-cap anchor side)) (< 0 (lw-euler-normalized-square-derivative-cap anchor side))
       (lw-complex-diskp (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-euler-normalized-square-derivative-cap anchor side))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-positive-square-model-valid lw-euler-square-derivative-cap-data lw-unit-square-point-coordinates
        lw-polynomial-square-forward-contained
        (:instance lw-polynomial-square-normalized-derivative (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-euler-square-model-derivative-bound (point (lw-polynomial-square-forward anchor side point)))
        (:instance lw-complex-scale-disk (point (lw-complex-polynomial-derivative (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-forward anchor side point)))
                   (radius (lw-euler-square-derivative-cap anchor side)) (factor (* 1/2 side)))
        (:instance lw-ens-positive-product (a (* 1/2 side)) (b (lw-euler-square-derivative-cap anchor side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-normalized-square-derivative-cap lw-ens-product-rational abs lw-ens-left-commutes lw-ens-left-distributes lw-ens-fold-constants lw-ens-times-negative lw-ens-negative-times lw-ens-zero-times lw-ens-minus-one lw-ens-double-negative lw-ens-add-cancel lw-ens-double lw-ens-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-normalized-square-native-derivative-error
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta) (lw-unit-square-pointp point)) (rationalp derivative-error) (< 0 derivative-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-scale (* 1/2 side) (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) 1 derivative-error))) (* (* 1/2 side) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-positive-square-model-valid lw-unit-square-point-coordinates
        lw-polynomial-square-forward-contained
        (:instance lw-polynomial-square-normalized-derivative (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-euler-square-model-native-derivative-error (point (lw-polynomial-square-forward anchor side point)))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-euler-positive-square-model anchor side target error)) (point (lw-polynomial-square-forward anchor side point)))
        (:instance lw-complex-euler-local-coefficient-rational
          (rate (car (lw-polynomial-square-forward anchor side point))) (height (cdr (lw-polynomial-square-forward anchor side point))) (radius (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side))) (index 1) (error derivative-error))
        (:instance lw-positive-square-point-data (point (lw-polynomial-square-forward anchor side point)))
        (:instance lw-positive-square-disk-data)
        (:instance lw-euler-square-inner-radius-data)
        (:instance lw-ens-scale-difference
         (a (lw-complex-polynomial-derivative (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-forward anchor side point))) (b (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) 1 derivative-error)) (factor (* 1/2 side)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-polynomial-derivative (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-forward anchor side point)) (lw-complex-euler-local-coefficient-value (car (lw-polynomial-square-forward anchor side point)) (cdr (lw-polynomial-square-forward anchor side point)) (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) 1 derivative-error)))
         (radius (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error)) (factor (* 1/2 side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-positive-squarep lw-square-containsp lw-complexp abs lw-ens-left-commutes lw-ens-left-distributes lw-ens-fold-constants lw-ens-times-negative lw-ens-negative-times lw-ens-zero-times lw-ens-minus-one lw-ens-double-negative lw-ens-add-cancel lw-ens-double lw-ens-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-model-factor-contour-fixed-quotient-error
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= error (* 1/2 (car anchor))) (<= tolerance (* 1/8 eta)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point) (lw-complex-polynomial (lw-euler-model-factor-polynomial anchor side coarse target error eta tolerance) point 0)) (lw-complex-quotient (lw-complex-polynomial-derivative (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point) (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)))
   (* (lw-polynomial-factor-quotient-cost (* 1/8 eta) (lw-euler-normalized-square-derivative-cap anchor side)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance))))
 :hints (("Goal"
  :use (lw-euler-normalized-square-derivative-bound
        (:instance lw-euler-model-factor-contour-quotient-error (numerator-cap (lw-euler-normalized-square-derivative-cap anchor side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ens-left-commutes lw-ens-left-distributes lw-ens-fold-constants lw-ens-times-negative lw-ens-negative-times lw-ens-zero-times lw-ens-minus-one lw-ens-double-negative lw-ens-add-cancel lw-ens-double lw-ens-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
