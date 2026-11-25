(in-package "ACL2")

(include-book "euler-square-polynomial-check")
(include-book "euler-native-indexed-cover")

; Nonnegative native contour and retained-cover indices, bounded independently
; of the new model degree, mesh refinement and admissible evaluation request.

(local (defthm lw-esc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esc-times-negative (a b) (b a)))
                 :in-theory (disable lw-esc-times-negative)))))

(local (defthm lw-esc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esc-left-commutes)))))
(defthm lw-euler-square-base-index-nonnegative
 (implies (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (and (<= 0 (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side base-target base-error) anchor side coarse))) (<= (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side base-target base-error) anchor side coarse)) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-square-base-polynomial-boundary-check
        (:instance lw-polynomial-square-index-nonnegative (coefficients (lw-euler-positive-square-model anchor side base-target base-error))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-square-index-nonnegative
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (rationalp value-error) (< 0 value-error) (<= value-error eta))
  (and (<= 0 (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) value-error)) (<= (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) value-error) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-square-base-index-nonnegative
        (:instance lw-euler-native-square-index-model-agreement
          (count coarse) (step (lw-polynomial-grid-step side coarse)) (target base-target) (error base-error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-square-model-grid-index-nonnegative
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (posp factor) (natp target) (rationalp error) (< 0 error) (<= error eta))
  (and (<= 0 (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side (* coarse factor)))) (<= (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side (* coarse factor))) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-native-square-grid-refinement-index
        (:instance lw-euler-native-square-index-nonnegative (value-error base-error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-indexed-cover-index-nonnegative
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
  (and (<= 0 (lw-polynomial-cover-index
   (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))
   anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)
   (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon))) (<= (lw-polynomial-cover-index
   (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))
   anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)
   (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon)) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-native-indexed-cover-index
        (:instance lw-euler-native-square-index-nonnegative (value-error base-error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-square-index-positive
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (rationalp value-error) (< 0 value-error) (<= value-error eta)
               (not (equal (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) value-error) 0)))
  (< 0 (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) value-error)))
 :hints (("Goal" :use (lw-euler-native-square-index-nonnegative)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
