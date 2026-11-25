(in-package "ACL2")

(include-book "euler-model-square-check")
(include-book "euler-square-counts")
(include-book "unit-square-root-selection")

; Arbitrarily accurate polynomial models give a computed interior list of fixed length.

(local (defthm lw-emf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emf-times-negative (a b) (b a)))
                 :in-theory (disable lw-emf-times-negative)))))

(local (defthm lw-emf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-emf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-emf-left-commutes)))))

(defun lw-euler-model-square-roots (anchor side coarse target error eta)
 (let* ((coefficients (lw-euler-positive-square-model anchor side target error))
        (count (lw-euler-model-square-count anchor side coarse target error eta)))
  (lw-polynomial-square-factor-roots
   (lw-polynomial-square-normalize coefficients anchor side)
   (lw-polynomial-normalization-count coefficients anchor side count))))
(defun lw-euler-model-square-inside-roots (anchor side coarse target error eta)
 (lw-unit-square-inside-roots (lw-euler-model-square-roots anchor side coarse target error eta)))

(defthm lw-euler-model-square-grid-index
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta))
  (equal (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta))) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error)))
 :hints (("Goal"
  :use (lw-euler-model-square-count-data
        (:instance lw-euler-native-square-grid-refinement-index (factor (lw-euler-model-square-factor anchor side target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-square-count lw-emf-left-commutes lw-emf-left-distributes lw-emf-fold-constants lw-emf-times-negative lw-emf-negative-times lw-emf-zero-times lw-emf-minus-one lw-emf-double-negative lw-emf-add-cancel lw-emf-double lw-emf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-square-factor-count
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta))
  (equal (lw-unit-square-factor-count (lw-euler-model-square-roots anchor side coarse target error eta)) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data
        lw-euler-model-square-boundary-check lw-euler-model-square-grid-index
        (:instance lw-polynomial-square-index-factor-count (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-square-roots lw-emf-left-commutes lw-emf-left-distributes lw-emf-fold-constants lw-emf-times-negative lw-emf-negative-times lw-emf-zero-times lw-emf-minus-one lw-emf-double-negative lw-emf-add-cancel lw-emf-double lw-emf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-square-roots-data
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta))
  (and (lw-ray-pointsp (lw-euler-model-square-roots anchor side coarse target error eta)) (lw-unit-square-roots-awayp (lw-euler-model-square-roots anchor side coarse target error eta))
       (lw-ray-pointsp (lw-euler-model-square-inside-roots anchor side coarse target error eta)) (lw-unit-square-open-rootsp (lw-euler-model-square-inside-roots anchor side coarse target error eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data
        lw-euler-model-square-boundary-check
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side target error)))
        (:instance lw-polynomial-normalization-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-normalization-boundary-check (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-factor-data (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta))))
        (:instance lw-polynomial-square-factors-away (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side)) (count (lw-polynomial-normalization-count (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta))))
        (:instance lw-unit-square-inside-roots-valid (roots (lw-euler-model-square-roots anchor side coarse target error eta)))
        (:instance lw-unit-square-inside-roots-interior (roots (lw-euler-model-square-roots anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-square-roots lw-euler-model-square-inside-roots lw-emf-left-commutes lw-emf-left-distributes lw-emf-fold-constants lw-emf-times-negative lw-emf-negative-times lw-emf-zero-times lw-emf-minus-one lw-emf-double-negative lw-emf-add-cancel lw-emf-double lw-emf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-square-inside-count
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta))
  (and (equal (len (lw-euler-model-square-inside-roots anchor side coarse target error eta)) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error))
       (<= (len (lw-euler-model-square-inside-roots anchor side coarse target error eta)) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-model-square-factor-count lw-euler-square-polynomial-budget-data
        (:instance lw-euler-native-square-index-nonnegative (value-error base-error))
        (:instance lw-unit-square-inside-roots-length (roots (lw-euler-model-square-roots anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-square-inside-roots lw-emf-left-commutes lw-emf-left-distributes lw-emf-fold-constants lw-emf-times-negative lw-emf-negative-times lw-emf-zero-times lw-emf-minus-one lw-emf-double-negative lw-emf-add-cancel lw-emf-double lw-emf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-square-inside-nonempty
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (not (equal (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error) 0))) (consp (lw-euler-model-square-inside-roots anchor side coarse target error eta)))
 :hints (("Goal"
  :use (lw-euler-model-square-inside-count)
  :cases ((consp (lw-euler-model-square-inside-roots anchor side coarse target error eta))) :expand ((len (lw-euler-model-square-inside-roots anchor side coarse target error eta)))
  :in-theory (union-theories
 '(fold-consts-in-+ endp lw-emf-left-commutes lw-emf-left-distributes lw-emf-fold-constants lw-emf-times-negative lw-emf-negative-times lw-emf-zero-times lw-emf-minus-one lw-emf-double-negative lw-emf-add-cancel lw-emf-double lw-emf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
