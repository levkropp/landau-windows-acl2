(in-package "ACL2")

(include-book "euler-model-accurate-factors")

; Arbitrarily accurate candidate families retain the generated cluster checks.

(local (defthm lw-eap-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eap-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eap-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eap-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eap-times-negative (a b) (b a)))
                 :in-theory (disable lw-eap-times-negative)))))

(local (defthm lw-eap-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eap-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eap-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eap-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eap-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eap-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eap-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eap-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eap-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eap-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eap-left-commutes)))))

(defun lw-euler-model-accurate-pole-candidates (anchor side coarse target error eta tolerance)
 (lw-square-unit-pole-candidates anchor side
  (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))

(defthm lw-euler-model-accurate-pole-candidates-data
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (<= (+ (car anchor) side) 1))
  (and (lw-zeta-pole-familyp (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)) (lw-pole-cluster-check (lw-square-pole-candidate-center anchor) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance) (lw-square-pole-candidate-radius anchor side))
       (equal (len (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error))
       (<= (len (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-accurate-roots-data lw-euler-model-accurate-inside-count
        (:instance lw-square-unit-pole-candidates-valid (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
        (:instance lw-square-unit-pole-candidates-cluster-check (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
        (:instance lw-square-unit-pole-candidates-length (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-pole-candidates lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-accurate-pole-candidates-nonempty
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (not (equal (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error) 0))) (consp (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)))
 :hints (("Goal"
  :use (lw-euler-model-accurate-inside-count)
  :cases ((consp (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
  :expand ((len (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)) (lw-square-unit-pole-candidates anchor side (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-pole-candidates endp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-accurate-pole-candidates-large-index
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (<= (+ (car anchor) side) 1) (not (equal (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error) 0)) (natp start))
  (let ((index (lw-pole-cluster-large-index (lw-square-pole-candidate-center anchor) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance) (lw-square-pole-candidate-radius anchor side) start)))
   (and (natp index) (< start index) (<= index (+ start (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error)))
        (rationalp (lw-pole-cluster-large-cap (lw-square-pole-candidate-center anchor) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance) (lw-square-pole-candidate-radius anchor side) start))
        (< 0 (lw-pole-cluster-large-cap (lw-square-pole-candidate-center anchor) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance) (lw-square-pole-candidate-radius anchor side) start))
        (not (lw-complex-diskp
         (lw-complex-scale (lw-rational-power (lw-square-pole-candidate-radius anchor side) index) (lw-pole-log-coefficient-sum (lw-square-pole-candidate-center anchor) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance) index))
         (lw-pole-cluster-large-cap (lw-square-pole-candidate-center anchor) (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance) (lw-square-pole-candidate-radius anchor side) start))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-square-pole-candidate-cluster-data
        lw-euler-model-accurate-pole-candidates-data lw-euler-model-accurate-pole-candidates-nonempty
        (:instance lw-pole-cluster-large-cap-positive (center (lw-square-pole-candidate-center anchor)) (entries (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)) (radius (lw-square-pole-candidate-radius anchor side)))
        (:instance lw-pole-cluster-large-index-certificate (center (lw-square-pole-candidate-center anchor)) (entries (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance)) (radius (lw-square-pole-candidate-radius anchor side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-pole-family-small-valuesp (entries value-error cap)
 (declare (xargs :measure (acl2-count entries) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp entries) (equal entries nil)
  (and (lw-complex-diskp (lw-complex-euler-continuation-value (car (caar entries)) (cdr (caar entries)) value-error) cap)
       (lw-pole-family-small-valuesp (cdr entries) value-error cap))))

(local (defthm lw-eap-subset-cons
 (implies (subsetp-equal roots whole) (subsetp-equal roots (cons head whole)))
 :hints (("Goal" :induct (subsetp-equal roots whole)
  :in-theory (union-theories
 '(fold-consts-in-+ subsetp-equal member-equal endp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-eap-self-subset
 (subsetp-equal roots roots)
 :hints (("Goal" :induct (len roots)
  :in-theory (union-theories
 '(fold-consts-in-+ len subsetp-equal member-equal endp cons-car-cdr lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-eap-subset-cons (roots (cdr roots)) (whole (cdr roots)) (head (car roots))))
    :do-not-induct t)))))

(local (defthm lw-eap-mapped-small-values
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (rationalp value-error) (< 0 value-error) (subsetp-equal roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
  (lw-pole-family-small-valuesp (lw-square-unit-pole-candidates anchor side roots) value-error (+ tolerance (* 1/4 error) (* 1/4 value-error))))
 :hints (("Goal" :induct (lw-square-unit-pole-candidates anchor side roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-square-unit-pole-candidates) lw-square-unit-pole-candidates lw-pole-family-small-valuesp subsetp-equal endp lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-euler-model-accurate-root-value (root (car roots)))) :do-not-induct t)))))

(defthm lw-euler-model-accurate-pole-candidates-small-values
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (rationalp value-error) (< 0 value-error))
  (lw-pole-family-small-valuesp (lw-euler-model-accurate-pole-candidates anchor side coarse target error eta tolerance) value-error (+ tolerance (* 1/4 error) (* 1/4 value-error))))
 :hints (("Goal"
  :use ((:instance lw-eap-mapped-small-values (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-pole-candidates lw-eap-self-subset lw-eap-left-commutes lw-eap-left-distributes lw-eap-fold-constants lw-eap-times-negative lw-eap-negative-times lw-eap-zero-times lw-eap-minus-one lw-eap-double-negative lw-eap-add-cancel lw-eap-double lw-eap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
