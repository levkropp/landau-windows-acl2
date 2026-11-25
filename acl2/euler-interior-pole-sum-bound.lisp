(in-package "ACL2")

(include-book "euler-interior-root-clearance")
(include-book "polynomial-pole-sum-clearance")

; Bound the selected sum by the fixed native count times the reciprocal margin.

(local (defthm lw-ips-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ips-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ips-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ips-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ips-times-negative (a b) (b a)))
                 :in-theory (disable lw-ips-times-negative)))))

(local (defthm lw-ips-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ips-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ips-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ips-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ips-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ips-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ips-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ips-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ips-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ips-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ips-left-commutes)))))

(local (defthm lw-ips-subset-cons
 (implies (subsetp-equal roots whole) (subsetp-equal roots (cons head whole)))
 :hints (("Goal" :induct (subsetp-equal roots whole)
  :in-theory (union-theories
 '(fold-consts-in-+ subsetp-equal member-equal endp lw-ips-left-commutes lw-ips-left-distributes lw-ips-fold-constants lw-ips-times-negative lw-ips-negative-times lw-ips-zero-times lw-ips-minus-one lw-ips-double-negative lw-ips-add-cancel lw-ips-double lw-ips-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ips-self-subset
 (subsetp-equal roots roots)
 :hints (("Goal" :induct (len roots)
  :in-theory (union-theories
 '(fold-consts-in-+ len subsetp-equal member-equal endp cons-car-cdr lw-ips-left-commutes lw-ips-left-distributes lw-ips-fold-constants lw-ips-times-negative lw-ips-negative-times lw-ips-zero-times lw-ips-minus-one lw-ips-double-negative lw-ips-add-cancel lw-ips-double lw-ips-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-ips-subset-cons (roots (cdr roots)) (whole (cdr roots)) (head (car roots))))
    :do-not-induct t)))))

(local (defthm lw-ips-selected-clearances
 (implies (and (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta))) (subsetp-equal roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)) (lw-ray-pointsp roots))
  (lw-polynomial-root-clearancesp roots point (lw-euler-interior-root-clearance anchor side base-target base-error eta)))
 :hints (("Goal" :induct (lw-polynomial-root-clearancesp roots point (lw-euler-interior-root-clearance anchor side base-target base-error eta))
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-root-clearancesp) lw-polynomial-root-clearancesp lw-ray-pointsp subsetp-equal endp lw-ips-left-commutes lw-ips-left-distributes lw-ips-fold-constants lw-ips-times-negative lw-ips-negative-times lw-ips-zero-times lw-ips-minus-one lw-ips-double-negative lw-ips-add-cancel lw-ips-double lw-ips-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-euler-selected-root-boundary-distance (root (car roots))))
    :do-not-induct t)))))

(defthm lw-euler-interior-root-clearances-generated
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta)))
  (lw-polynomial-root-clearancesp (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance) point (lw-euler-interior-root-clearance anchor side base-target base-error eta)))
 :hints (("Goal"
  :use (lw-euler-model-accurate-roots-data (:instance lw-ips-selected-clearances (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ips-self-subset lw-ips-left-commutes lw-ips-left-distributes lw-ips-fold-constants lw-ips-times-negative lw-ips-negative-times lw-ips-zero-times lw-ips-minus-one lw-ips-double-negative lw-ips-add-cancel lw-ips-double lw-ips-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defun lw-euler-interior-pole-sum-cap (anchor side coarse base-target base-error eta)
 (* (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error) (/ (lw-euler-interior-root-clearance anchor side base-target base-error eta))))

(defthm lw-euler-interior-pole-sum-bound
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-unit-square-pointp point)) (<= tolerance (* 1/8 eta))) (lw-complex-diskp (lw-polynomial-factor-log-sum (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance) point) (lw-euler-interior-pole-sum-cap anchor side coarse base-target base-error eta)))
 :hints (("Goal"
  :use (lw-euler-model-accurate-roots-data lw-unit-square-point-coordinates lw-euler-model-accurate-inside-count
        lw-euler-interior-root-clearance-data lw-euler-interior-root-clearances-generated
        (:instance lw-polynomial-factor-log-sum-clearance-bound (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)) (clearance (lw-euler-interior-root-clearance anchor side base-target base-error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-interior-pole-sum-cap lw-ips-left-commutes lw-ips-left-distributes lw-ips-fold-constants lw-ips-times-negative lw-ips-negative-times lw-ips-zero-times lw-ips-minus-one lw-ips-double-negative lw-ips-add-cancel lw-ips-double lw-ips-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
