(in-package "ACL2")

(include-book "euler-model-factor-counts")
(include-book "pole-cluster-search")

; Unit-weight rational pole candidates, with generated strip and cluster checks.
; Their equality or approximation to native pole coefficients is not asserted.

(local (defthm lw-emp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emp-times-negative (a b) (b a)))
                 :in-theory (disable lw-emp-times-negative)))))

(local (defthm lw-emp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-emp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-emp-left-commutes)))))

(local (defthm lw-emp-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-emp-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-square-unit-pole-candidates (anchor side roots)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) nil
  (cons (cons (lw-polynomial-square-forward anchor side (car roots)) 1)
        (lw-square-unit-pole-candidates anchor side (cdr roots)))))
(defun lw-square-pole-candidate-center (anchor) (cons 252 (cdr anchor)))
(defun lw-square-pole-candidate-radius (anchor side) (+ 252 (- (car anchor)) side))

(defun lw-euler-model-pole-candidates (anchor side coarse target error eta)
 (lw-square-unit-pole-candidates anchor side
  (lw-euler-model-square-inside-roots anchor side coarse target error eta)))

(local (in-theory (disable lw-square-unit-pole-candidates lw-square-pole-candidate-center lw-square-pole-candidate-radius lw-euler-model-pole-candidates)))

(defthm lw-square-unit-pole-candidates-length
 (equal (len (lw-square-unit-pole-candidates anchor side roots)) (len roots))
 :hints (("Goal" :induct (lw-square-unit-pole-candidates anchor side roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-square-unit-pole-candidates) lw-square-unit-pole-candidates len endp lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-square-forward-root-interior
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side)
               (lw-complexp root) (< -1 (car root)) (< (car root) 1) (< -1 (cdr root)) (< (cdr root) 1))
  (and (lw-complexp (lw-polynomial-square-forward anchor side root))
       (< (car anchor) (car (lw-polynomial-square-forward anchor side root))) (< (car (lw-polynomial-square-forward anchor side root)) (+ (car anchor) side))
       (< (cdr anchor) (cdr (lw-polynomial-square-forward anchor side root))) (< (cdr (lw-polynomial-square-forward anchor side root)) (+ (cdr anchor) side))))
 :hints (("Goal" :nonlinearp t
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-forward lw-polynomial-square-center lw-polynomial-square-slope lw-complex-add lw-complex-mul lw-complexp lw-emp-product-rational lw-emp-sum-rational lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-square-unit-pole-candidates-valid
 (implies (and (lw-positive-squarep anchor side) (<= (+ (car anchor) side) 1) (lw-unit-square-open-rootsp roots))
  (lw-zeta-pole-familyp (lw-square-unit-pole-candidates anchor side roots)))
 :hints (("Goal" :induct (lw-square-unit-pole-candidates anchor side roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-square-unit-pole-candidates) lw-square-unit-pole-candidates lw-unit-square-open-rootsp lw-zeta-pole-familyp lw-zeta-pole-datap lw-positive-squarep endp lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-square-forward-root-interior (root (car roots)))) :do-not-induct t))))

(defthm lw-square-pole-candidate-cluster-data
 (implies (and (lw-positive-squarep anchor side) (<= (+ (car anchor) side) 1))
  (and (lw-complexp (lw-square-pole-candidate-center anchor)) (< 3 (car (lw-square-pole-candidate-center anchor))) (rationalp (lw-square-pole-candidate-radius anchor side)) (< 0 (lw-square-pole-candidate-radius anchor side))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-square-pole-candidate-center lw-square-pole-candidate-radius lw-positive-squarep lw-complexp lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-emp-interior-point-cluster
 (implies (and (lw-positive-squarep anchor side) (<= (+ (car anchor) side) 1)
               (lw-complexp point)
               (< (car anchor) (car point)) (< (car point) (+ (car anchor) side))
               (< (cdr anchor) (cdr point)) (< (cdr point) (+ (cdr anchor) side)))
  (and (< 0 (car (lw-complex-sub (lw-square-pole-candidate-center anchor) point))) (lw-complex-diskp (lw-complex-sub (lw-square-pole-candidate-center anchor) point) (lw-square-pole-candidate-radius anchor side))))
 :hints (("Goal"
  :use ((:instance lw-complex-l1-bound (point (lw-complex-sub (lw-square-pole-candidate-center anchor) point)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-square-pole-candidate-center anchor) point)) (radius (lw-complex-l1 (lw-complex-sub (lw-square-pole-candidate-center anchor) point))) (cap (lw-square-pole-candidate-radius anchor side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-square-pole-candidate-center lw-square-pole-candidate-radius lw-positive-squarep lw-complexp lw-complex-sub lw-complex-l1 abs lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-square-unit-pole-candidates-cluster-check
 (implies (and (lw-positive-squarep anchor side) (<= (+ (car anchor) side) 1) (lw-unit-square-open-rootsp roots))
  (lw-pole-cluster-check (lw-square-pole-candidate-center anchor) (lw-square-unit-pole-candidates anchor side roots) (lw-square-pole-candidate-radius anchor side)))
 :hints (("Goal" :induct (lw-square-unit-pole-candidates anchor side roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-square-unit-pole-candidates) lw-square-unit-pole-candidates lw-unit-square-open-rootsp lw-pole-cluster-check lw-positive-squarep endp lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-square-forward-root-interior (root (car roots)))
          (:instance lw-emp-interior-point-cluster (point (lw-polynomial-square-forward anchor side (car roots)))))
    :do-not-induct t))))

(defthm lw-euler-model-pole-candidates-data
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (<= (+ (car anchor) side) 1))
  (and (lw-zeta-pole-familyp (lw-euler-model-pole-candidates anchor side coarse target error eta))
       (lw-pole-cluster-check (lw-square-pole-candidate-center anchor) (lw-euler-model-pole-candidates anchor side coarse target error eta) (lw-square-pole-candidate-radius anchor side))
       (equal (len (lw-euler-model-pole-candidates anchor side coarse target error eta)) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error))
       (<= (len (lw-euler-model-pole-candidates anchor side coarse target error eta)) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-roots-data lw-euler-model-square-inside-count
        (:instance lw-square-unit-pole-candidates-valid (roots (lw-euler-model-square-inside-roots anchor side coarse target error eta)))
        (:instance lw-square-unit-pole-candidates-cluster-check (roots (lw-euler-model-square-inside-roots anchor side coarse target error eta)))
        (:instance lw-square-unit-pole-candidates-length (roots (lw-euler-model-square-inside-roots anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-pole-candidates lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-pole-candidates-nonempty
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (not (equal (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error) 0))) (consp (lw-euler-model-pole-candidates anchor side coarse target error eta)))
 :hints (("Goal"
  :use (lw-euler-model-square-inside-nonempty)
  :expand ((lw-square-unit-pole-candidates anchor side (lw-euler-model-square-inside-roots anchor side coarse target error eta)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-pole-candidates endp lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-pole-candidates-large-index
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (<= (+ (car anchor) side) 1) (not (equal (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error) 0)) (natp start))
  (let ((index (lw-pole-cluster-large-index (lw-square-pole-candidate-center anchor) (lw-euler-model-pole-candidates anchor side coarse target error eta) (lw-square-pole-candidate-radius anchor side) start)))
   (and (natp index) (< start index) (<= index (+ start (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error)))
        (rationalp (lw-pole-cluster-large-cap (lw-square-pole-candidate-center anchor) (lw-euler-model-pole-candidates anchor side coarse target error eta) (lw-square-pole-candidate-radius anchor side) start)) (< 0 (lw-pole-cluster-large-cap (lw-square-pole-candidate-center anchor) (lw-euler-model-pole-candidates anchor side coarse target error eta) (lw-square-pole-candidate-radius anchor side) start))
        (not (lw-complex-diskp
         (lw-complex-scale (lw-rational-power (lw-square-pole-candidate-radius anchor side) index) (lw-pole-log-coefficient-sum (lw-square-pole-candidate-center anchor) (lw-euler-model-pole-candidates anchor side coarse target error eta) index))
         (lw-pole-cluster-large-cap (lw-square-pole-candidate-center anchor) (lw-euler-model-pole-candidates anchor side coarse target error eta) (lw-square-pole-candidate-radius anchor side) start))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-square-pole-candidate-cluster-data
        lw-euler-model-pole-candidates-data lw-euler-model-pole-candidates-nonempty
        (:instance lw-pole-cluster-large-cap-positive (center (lw-square-pole-candidate-center anchor)) (entries (lw-euler-model-pole-candidates anchor side coarse target error eta)) (radius (lw-square-pole-candidate-radius anchor side)))
        (:instance lw-pole-cluster-large-index-certificate (center (lw-square-pole-candidate-center anchor)) (entries (lw-euler-model-pole-candidates anchor side coarse target error eta)) (radius (lw-square-pole-candidate-radius anchor side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-emp-left-commutes lw-emp-left-distributes lw-emp-fold-constants lw-emp-times-negative lw-emp-negative-times lw-emp-zero-times lw-emp-minus-one lw-emp-double-negative lw-emp-add-cancel lw-emp-double lw-emp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
