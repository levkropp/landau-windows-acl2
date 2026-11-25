(in-package "ACL2")

(include-book "euler-model-square-clearance")
(include-book "polynomial-clearance-mesh")

; Every requested Euler model generates its own accepted polynomial square mesh.

(local (defthm lw-ems-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ems-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ems-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ems-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ems-times-negative (a b) (b a)))
                 :in-theory (disable lw-ems-times-negative)))))

(local (defthm lw-ems-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ems-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ems-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ems-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ems-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ems-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ems-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ems-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ems-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ems-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ems-left-commutes)))))

(defun lw-euler-model-square-factor (anchor side target error eta)
 (lw-polynomial-root-count (lw-euler-positive-square-model anchor side target error) anchor side (* 1/4 eta)))
(defun lw-euler-model-square-count (anchor side coarse target error eta)
 (* coarse (lw-euler-model-square-factor anchor side target error eta)))

(defthm lw-euler-model-square-count-data
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta))
  (and (lw-complex-coefficientsp (lw-euler-positive-square-model anchor side target error)) (posp (lw-euler-model-square-factor anchor side target error eta)) (posp (lw-euler-model-square-count anchor side coarse target error eta))
       (equal (lw-euler-model-square-count anchor side coarse target error eta) (lw-polynomial-clearance-count (lw-euler-positive-square-model anchor side target error) anchor side coarse (* 1/4 eta)))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data
        lw-euler-positive-square-model-valid
        (:instance lw-polynomial-root-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (epsilon (* 1/4 eta)))
        (:instance lw-polynomial-clearance-count-data (coefficients (lw-euler-positive-square-model anchor side target error)) (clearance (* 1/4 eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-square-factor lw-euler-model-square-count lw-polynomial-clearance-count lw-ems-left-commutes lw-ems-left-distributes lw-ems-fold-constants lw-ems-times-negative lw-ems-negative-times lw-ems-zero-times lw-ems-minus-one lw-ems-double-negative lw-ems-add-cancel lw-ems-double lw-ems-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-model-square-edge-check
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (natp edge) (< edge 4) (natp index) (< index (lw-euler-model-square-count anchor side coarse target error eta)))
  (lw-polynomial-edge-check (lw-euler-positive-square-model anchor side target error)
   (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-euler-model-square-count anchor side coarse target error eta) index)
   (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-euler-model-square-count anchor side coarse target error eta) (+ 1 index))
   (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-euler-model-square-count anchor side coarse target error eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data
        (:instance lw-euler-square-model-line-point-clearance (count (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-clearance-edge-check (coefficients (lw-euler-positive-square-model anchor side target error)) (clearance (* 1/4 eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ems-left-commutes lw-ems-left-distributes lw-ems-fold-constants lw-ems-times-negative lw-ems-negative-times lw-ems-zero-times lw-ems-minus-one lw-ems-double-negative lw-ems-add-cancel lw-ems-double lw-ems-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-square-line-check
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (natp edge) (< edge 4) (natp index) (natp remaining) (<= (+ index remaining) (lw-euler-model-square-count anchor side coarse target error eta)))
  (lw-polynomial-line-check (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-euler-model-square-count anchor side coarse target error eta) index remaining
   (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-euler-model-square-count anchor side coarse target error eta))))
 :hints (("Goal"
  :induct (lw-polynomial-line-check (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (lw-euler-model-square-count anchor side coarse target error eta) index remaining
   (lw-polynomial-grid-radius anchor side) (lw-polynomial-grid-step side (lw-euler-model-square-count anchor side coarse target error eta)))
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-check) lw-polynomial-line-check lw-euler-model-square-edge-check lw-ems-left-commutes lw-ems-left-distributes lw-ems-fold-constants lw-ems-times-negative lw-ems-negative-times lw-ems-zero-times lw-ems-minus-one lw-ems-double-negative lw-ems-add-cancel lw-ems-double lw-ems-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-model-square-boundary-check
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta))
  (lw-polynomial-square-boundary-check (lw-euler-positive-square-model anchor side target error) anchor side (lw-euler-model-square-count anchor side coarse target error eta)))
 :hints (("Goal"
  :use (lw-euler-model-square-count-data
        (:instance lw-euler-model-square-line-check (edge 0) (index 0) (remaining (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-euler-model-square-line-check (edge 1) (index 0) (remaining (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-euler-model-square-line-check (edge 2) (index 0) (remaining (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-euler-model-square-line-check (edge 3) (index 0) (remaining (lw-euler-model-square-count anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-boundary-check lw-ems-left-commutes lw-ems-left-distributes lw-ems-fold-constants lw-ems-times-negative lw-ems-negative-times lw-ems-zero-times lw-ems-minus-one lw-ems-double-negative lw-ems-add-cancel lw-ems-double lw-ems-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
