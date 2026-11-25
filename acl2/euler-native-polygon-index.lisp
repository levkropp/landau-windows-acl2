; Actual native Euler sample indices agree with the fixed coarse polynomial index.
(in-package "ACL2")
(include-book "euler-square-native-index")
(local (in-theory (disable lw-complexp lw-complex-diskp lw-complex-polynomial
 lw-complex-euler-continuation-value lw-euler-positive-square-model lw-square-point-listp
 lw-square-containsp lw-positive-squarep lw-euler-polygon-index-check
 lw-euler-polygon-index lw-polynomial-path-values lw-ray-pointwise-nearp
 lw-ray-polygon-index lw-ray-row-near-check lw-ray-row-avoids lw-ray-close-polygon)))
(local (defthm lw-enx-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enx-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enx-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enx-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enx-times-negative (a b) (b a)))
                 :in-theory (disable lw-enx-times-negative)))))

(local (defthm lw-enx-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enx-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enx-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enx-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enx-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enx-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enx-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enx-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enx-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enx-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enx-left-commutes)))))
(defun lw-euler-native-path-values (points error)
 (if (endp points) nil
 (cons (lw-complex-euler-continuation-value (caar points) (cdar points) error)
       (lw-euler-native-path-values (cdr points) error))))
(defun lw-euler-native-polygon-index (points error)
 (lw-ray-polygon-index (lw-euler-native-path-values points error)))
(local (in-theory (disable lw-euler-native-path-values lw-euler-native-polygon-index)))

(defthm lw-euler-native-path-model-near
 (implies (and (lw-positive-squarep anchor side) (lw-square-point-listp anchor side points)
               (natp base-target) (rationalp base-error) (< 0 base-error)
               (rationalp value-error) (< 0 value-error))
 (lw-ray-pointwise-nearp (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points) (lw-euler-native-path-values points value-error) (* 1/4 (+ base-error value-error))))
 :hints (("Goal" :induct (lw-square-point-listp anchor side points)
 :in-theory (union-theories
 '(lw-square-point-listp lw-polynomial-path-values lw-euler-native-path-values lw-ray-pointwise-nearp endp lw-enx-left-commutes lw-enx-left-distributes lw-enx-fold-constants lw-enx-times-negative lw-enx-negative-times lw-enx-zero-times lw-enx-minus-one lw-enx-double-negative lw-enx-add-cancel lw-enx-double lw-enx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-positive-square-model-comparison (target base-target) (error base-error) (point (car points)))
         (:instance lw-euler-positive-square-model-valid (target base-target) (error base-error))
         (:instance lw-positive-square-point-data (point (car points)))
         (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (car points)) (offset 0))
         (:instance lw-complex-euler-continuation-value-rational
          (rate (caar points)) (height (cdar points)) (error value-error))
         (:instance lw-complex-difference-symmetric
          (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (car points) 0))
          (right (lw-complex-euler-continuation-value (caar points) (cdar points) value-error))
          (radius (* 1/4 (+ base-error value-error)))))
   :in-theory (union-theories
 '(lw-square-containsp lw-complexp lw-enx-left-commutes lw-enx-left-distributes lw-enx-fold-constants lw-enx-times-negative lw-enx-negative-times lw-enx-zero-times lw-enx-minus-one lw-enx-double-negative lw-enx-add-cancel lw-enx-double lw-enx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
   :do-not-induct t))))

(defthm lw-euler-native-polygon-index-stable
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (equal (lw-euler-native-polygon-index points value-error)
        (lw-euler-polygon-index anchor side points base-target base-error)))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data lw-euler-polygon-base-step-check
       lw-euler-native-path-model-near
       (:instance lw-ray-pointwise-near-enlarge
        (left (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)) (right (lw-euler-native-path-values points value-error)) (delta (* 1/4 (+ base-error value-error))) (cap (/ eta 2)))
       (:instance lw-ray-polygon-pointwise-perturbation
        (bottom (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)) (top (lw-euler-native-path-values points value-error)) (beta (/ eta 2)) (delta (/ eta 2))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-euler-polygon-index lw-euler-native-polygon-index lw-enx-left-commutes lw-enx-left-distributes lw-enx-fold-constants lw-enx-times-negative lw-enx-negative-times lw-enx-zero-times lw-enx-minus-one lw-enx-double-negative lw-enx-add-cancel lw-enx-double lw-enx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-polygon-index-independent-requests
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
               (rationalp left-error) (< 0 left-error) (<= left-error eta)
               (rationalp right-error) (< 0 right-error) (<= right-error eta))
 (equal (lw-euler-native-polygon-index points left-error)
        (lw-euler-native-polygon-index points right-error)))
 :hints (("Goal"
 :use ((:instance lw-euler-native-polygon-index-stable (value-error left-error))
       (:instance lw-euler-native-polygon-index-stable (value-error right-error)))
 :in-theory (union-theories
 '( lw-enx-left-commutes lw-enx-left-distributes lw-enx-fold-constants lw-enx-times-negative lw-enx-negative-times lw-enx-zero-times lw-enx-minus-one lw-enx-double-negative lw-enx-add-cancel lw-enx-double lw-enx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-polygon-index-model-agreement
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta)
               (natp target) (rationalp error) (< 0 error) (<= error eta)
               (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (equal (lw-euler-native-polygon-index points value-error)
        (lw-euler-polygon-index anchor side points target error)))
 :hints (("Goal" :use (lw-euler-native-polygon-index-stable lw-euler-polygon-index-stable)
 :in-theory (union-theories
 '( lw-enx-left-commutes lw-enx-left-distributes lw-enx-fold-constants lw-enx-times-negative lw-enx-negative-times lw-enx-zero-times lw-enx-minus-one lw-enx-double-negative lw-enx-add-cancel lw-enx-double lw-enx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-square-index-model-agreement
 (implies (and (lw-euler-square-index-check anchor side count base-target base-error step eta)
               (natp target) (rationalp error) (< 0 error) (<= error eta)
               (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (equal
 (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side count) value-error)
 (lw-ray-grid-boundary-index
  (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side count))))
 :hints (("Goal"
 :use ((:instance lw-euler-native-polygon-index-model-agreement (points (lw-polynomial-square-boundary anchor side count)))
       (:instance lw-euler-polygon-index-check-data (points (lw-polynomial-square-boundary anchor side count)))
       (:instance lw-euler-positive-square-model-valid)
       (:instance lw-polynomial-grid-boundary-as-polygon
        (coefficients (lw-euler-positive-square-model anchor side target error))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-euler-polygon-index lw-positive-squarep lw-enx-left-commutes lw-enx-left-distributes lw-enx-fold-constants lw-enx-times-negative lw-enx-negative-times lw-enx-zero-times lw-enx-minus-one lw-enx-double-negative lw-enx-add-cancel lw-enx-double lw-enx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

