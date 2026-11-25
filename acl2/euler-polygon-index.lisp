; One finite coarse certificate fixes the native Euler polygon index.
(in-package "ACL2")
(include-book "polynomial-square-path-control")
(local (in-theory (disable lw-complexp lw-complex-diskp lw-complex-polynomial
 lw-positive-squarep lw-square-point-listp lw-euler-positive-square-model
 lw-ray-row-near-check lw-ray-row-avoids lw-ray-pointwise-nearp
 lw-polynomial-path-values lw-ray-close-polygon lw-ray-polygon-index lw-polynomial-lipschitz-cap)))
(local (defthm lw-enp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enp-times-negative (a b) (b a)))
                 :in-theory (disable lw-enp-times-negative)))))

(local (defthm lw-enp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enp-left-commutes)))))
(defun lw-euler-polygon-index (anchor side points target error)
 (lw-ray-polygon-index
 (lw-polynomial-path-values (lw-euler-positive-square-model anchor side target error) points)))
(defun lw-euler-polygon-index-check (anchor side points base-target base-error step eta)
 (and (lw-positive-squarep anchor side) (consp points) (lw-square-point-listp anchor side points)
      (natp base-target) (rationalp base-error) (< 0 base-error)
      (rationalp eta) (< 0 eta) (<= base-error eta)
      (rationalp step) (<= 0 step)
      (lw-ray-row-near-check (lw-ray-close-polygon points) (lw-ray-close-polygon points) step)
      (<= (* step (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side))) (/ eta 4))
      (lw-ray-row-avoids (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points) eta)))
(local (in-theory (disable lw-euler-polygon-index lw-euler-polygon-index-check)))

(defthm lw-euler-polygon-index-check-data
 (implies (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
 (and (lw-complex-coefficientsp (lw-euler-positive-square-model anchor side base-target base-error)) (lw-complexp anchor) (rationalp side) (< 0 side)
      (rationalp (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side))) (<= 0 (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side)))
      (consp (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points))
      (lw-ray-pointsp (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points))))
 :hints (("Goal"
 :use ((:instance lw-euler-positive-square-model-valid (target base-target) (error base-error))
       lw-polynomial-grid-radius-data
       (:instance lw-polynomial-lipschitz-cap-data (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (bound (lw-polynomial-grid-radius anchor side)))
       (:instance lw-polynomial-path-values-shape (coefficients (lw-euler-positive-square-model anchor side base-target base-error)))
       lw-square-point-list-data
       (:instance lw-polynomial-path-values-data (coefficients (lw-euler-positive-square-model anchor side base-target base-error))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-positive-squarep lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-polygon-base-step-check
 (implies (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
 (lw-ray-row-near-check (lw-ray-close-polygon (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)) (lw-ray-close-polygon (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)) (/ eta 2)))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data
       (:instance lw-polynomial-square-polygon-step-bound (coefficients (lw-euler-positive-square-model anchor side base-target base-error)))
       (:instance lw-ray-row-near-enlarge
        (bottom (lw-ray-close-polygon (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points))) (top (lw-ray-close-polygon (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)))
        (radius (* step (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side)))) (cap (/ eta 2))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-polygon-models-near
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (lw-ray-pointwise-nearp
 (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)
 (lw-polynomial-path-values (lw-euler-positive-square-model anchor side target error) points)
 (/ eta 2)))
 :hints (("Goal"
 :use ((:instance lw-euler-positive-square-model-path-near
        (left-target base-target) (left-error base-error) (right-target target) (right-error error))
       (:instance lw-ray-pointwise-near-enlarge
        (left (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)) (right (lw-polynomial-path-values (lw-euler-positive-square-model anchor side target error) points))
        (delta (* 1/4 (+ base-error error))) (cap (/ eta 2))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-polygon-index-stable
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (equal (lw-euler-polygon-index anchor side points target error)
        (lw-euler-polygon-index anchor side points base-target base-error)))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data lw-euler-polygon-base-step-check lw-euler-polygon-models-near
       (:instance lw-ray-polygon-pointwise-perturbation
        (bottom (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points))
        (top (lw-polynomial-path-values (lw-euler-positive-square-model anchor side target error) points))
        (beta (/ eta 2)) (delta (/ eta 2))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-euler-polygon-index lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-polygon-index-independent-requests
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (<= left-error eta)
               (rationalp right-error) (< 0 right-error) (<= right-error eta))
 (equal (lw-euler-polygon-index anchor side points left-target left-error)
        (lw-euler-polygon-index anchor side points right-target right-error)))
 :hints (("Goal"
 :use ((:instance lw-euler-polygon-index-stable (target left-target) (error left-error))
       (:instance lw-euler-polygon-index-stable (target right-target) (error right-error)))
 :in-theory (union-theories
 '( lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-polygon-nonzero-index-preserved
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
               (not (equal (lw-euler-polygon-index anchor side points base-target base-error) 0))
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (not (equal (lw-euler-polygon-index anchor side points target error) 0)))
 :hints (("Goal" :use (lw-euler-polygon-index-stable) :in-theory (union-theories
 '( lw-enp-left-commutes lw-enp-left-distributes lw-enp-fold-constants lw-enp-times-negative lw-enp-negative-times lw-enp-zero-times lw-enp-minus-one lw-enp-double-negative lw-enp-add-cancel lw-enp-double lw-enp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

