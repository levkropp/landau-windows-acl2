; A fixed coarse certificate preserves the native index under every integer subdivision.
(in-package "ACL2")
(include-book "euler-native-edge-sampling")
(include-book "euler-native-path-access")
(local (in-theory (disable lw-euler-polygon-index-check lw-euler-polygon-base-anchor
 lw-euler-native-edge-samples lw-euler-native-edge-value lw-euler-polygon-edge-point
 lw-euler-native-path-values lw-euler-native-polygon-index lw-ray-close-polygon
 lw-ray-refinement-check lw-ray-refine-polygon lw-ray-indexed-slice lw-ray-polygon-index
 lw-complex-euler-continuation-value lw-square-point-listp lw-positive-squarep)))
(local (defthm lw-nrf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nrf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nrf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nrf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nrf-times-negative (a b) (b a)))
                 :in-theory (disable lw-nrf-times-negative)))))

(local (defthm lw-nrf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nrf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nrf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nrf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nrf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nrf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nrf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nrf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nrf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nrf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nrf-left-commutes)))))
(defun lw-euler-native-refinement-blocks (points count value-error index remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (lw-euler-native-edge-samples points index count value-error)
       (lw-euler-native-refinement-blocks points count value-error (+ 1 index) (- remaining 1)))))
(defun lw-euler-polygon-refinement-anchors (anchor side points base-target base-error index remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (lw-euler-polygon-base-anchor anchor side points base-target base-error index)
       (lw-euler-polygon-refinement-anchors anchor side points base-target base-error (+ 1 index) (- remaining 1)))))
(defun lw-euler-native-refined-polygon (points count value-error)
 (lw-ray-refine-polygon (lw-euler-native-path-values (lw-ray-close-polygon points) value-error)
  (lw-euler-native-refinement-blocks points count value-error 0 (len points))))
(local (in-theory (disable lw-euler-native-refinement-blocks lw-euler-polygon-refinement-anchors lw-euler-native-refined-polygon)))

(local (defthm lw-nrf-length-natural
 (natp (len points)) :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-nrf-left-commutes lw-nrf-left-distributes lw-nrf-fold-constants lw-nrf-times-negative lw-nrf-negative-times lw-nrf-zero-times lw-nrf-minus-one lw-nrf-double-negative lw-nrf-add-cancel lw-nrf-double lw-nrf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-nrf-nth-zero
 (equal (nth 0 values) (car values))
 :hints (("Goal" :expand ((nth 0 values)) :in-theory (union-theories
 '(nth lw-nrf-left-commutes lw-nrf-left-distributes lw-nrf-fold-constants lw-nrf-times-negative lw-nrf-negative-times lw-nrf-zero-times lw-nrf-minus-one lw-nrf-double-negative lw-nrf-add-cancel lw-nrf-double lw-nrf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-native-refinement-check
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (posp count)
               (rationalp value-error) (< 0 value-error) (<= value-error eta)
               (natp index) (natp remaining) (<= (+ index remaining) (len points)))
 (lw-ray-refinement-check (lw-complex-euler-continuation-value (car (nth index (lw-ray-close-polygon points))) (cdr (nth index (lw-ray-close-polygon points))) value-error)
  (lw-ray-indexed-slice (lw-euler-native-path-values (lw-ray-close-polygon points) value-error) (+ 1 index) remaining) (lw-euler-native-refinement-blocks points count value-error index remaining) (lw-euler-polygon-refinement-anchors anchor side points base-target base-error index remaining)))
 :hints (("Goal" :induct (lw-euler-native-refinement-blocks points count value-error index remaining)
 :expand ((lw-euler-native-refinement-blocks points count value-error index remaining) (lw-euler-polygon-refinement-anchors anchor side points base-target base-error index remaining) (lw-ray-indexed-slice (lw-euler-native-path-values (lw-ray-close-polygon points) value-error) (+ 1 index) remaining))
 :in-theory (union-theories
 '((:induction lw-euler-native-refinement-blocks) lw-ray-refinement-check lw-euler-native-refinement-blocks lw-euler-polygon-refinement-anchors lw-ray-indexed-slice fold-consts-in-+ lw-nrf-left-commutes lw-nrf-left-distributes lw-nrf-fold-constants lw-nrf-times-negative lw-nrf-negative-times lw-nrf-zero-times lw-nrf-minus-one lw-nrf-double-negative lw-nrf-add-cancel lw-nrf-double lw-nrf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use (lw-square-point-list-data
         lw-euler-polygon-edge-endpoints
         (:instance lw-ray-close-polygon-data)
         (:instance lw-euler-native-path-values-nth (points (lw-ray-close-polygon points)) (error value-error) (index (+ 1 index)))
         (:instance lw-euler-native-edge-halfplane (parameter 0))
         (:instance lw-euler-native-edge-halfplane (parameter 1))
         lw-euler-native-edge-samples-halfplane)
   :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-euler-native-edge-value fold-consts-in-+ lw-nrf-left-commutes lw-nrf-left-distributes lw-nrf-fold-constants lw-nrf-times-negative lw-nrf-negative-times lw-nrf-zero-times lw-nrf-minus-one lw-nrf-double-negative lw-nrf-add-cancel lw-nrf-double lw-nrf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
   :do-not-induct t))))

(defthm lw-euler-native-refined-polygon-index
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (posp count)
               (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (equal (lw-ray-polygon-index (lw-euler-native-refined-polygon points count value-error))
        (lw-euler-native-polygon-index points value-error)))
 :hints (("Goal"
 :use (lw-square-point-list-data
       (:instance lw-ray-close-polygon-data)
       (:instance lw-euler-native-path-values-shape (points (lw-ray-close-polygon points)) (error value-error))
       (:instance lw-euler-native-path-values-nth (points (lw-ray-close-polygon points)) (error value-error) (index 0))
       (:instance lw-ray-indexed-slice-tail (values (lw-euler-native-path-values (lw-ray-close-polygon points) value-error)))
       (:instance lw-euler-native-refinement-check (index 0) (remaining (len points)))
       (:instance lw-ray-refinement-polygon-index
        (points (lw-euler-native-path-values (lw-ray-close-polygon points) value-error))
        (blocks (lw-euler-native-refinement-blocks points count value-error 0 (len points)))
        (anchors (lw-euler-polygon-refinement-anchors anchor side points base-target base-error 0 (len points))))
       (:instance lw-euler-native-polygon-index-close (error value-error)))
 :in-theory (union-theories
 '(lw-euler-native-refined-polygon lw-euler-native-polygon-index lw-euler-polygon-index-check lw-nrf-nth-zero lw-nrf-length-natural fold-consts-in-+ lw-nrf-left-commutes lw-nrf-left-distributes lw-nrf-fold-constants lw-nrf-times-negative lw-nrf-negative-times lw-nrf-zero-times lw-nrf-minus-one lw-nrf-double-negative lw-nrf-add-cancel lw-nrf-double lw-nrf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-refined-polygon-base-index
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (posp count)
               (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (equal (lw-ray-polygon-index (lw-euler-native-refined-polygon points count value-error))
        (lw-euler-polygon-index anchor side points base-target base-error)))
 :hints (("Goal" :use (lw-euler-native-refined-polygon-index lw-euler-native-polygon-index-stable)
 :in-theory (union-theories
 '( lw-nrf-left-commutes lw-nrf-left-distributes lw-nrf-fold-constants lw-nrf-times-negative lw-nrf-negative-times lw-nrf-zero-times lw-nrf-minus-one lw-nrf-double-negative lw-nrf-add-cancel lw-nrf-double lw-nrf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-refined-polygon-independent-requests
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (posp left-count) (posp right-count)
               (rationalp left-error) (< 0 left-error) (<= left-error eta)
               (rationalp right-error) (< 0 right-error) (<= right-error eta))
 (equal (lw-ray-polygon-index (lw-euler-native-refined-polygon points left-count left-error))
        (lw-ray-polygon-index (lw-euler-native-refined-polygon points right-count right-error))))
 :hints (("Goal"
 :use ((:instance lw-euler-native-refined-polygon-base-index (count left-count) (value-error left-error))
       (:instance lw-euler-native-refined-polygon-base-index (count right-count) (value-error right-error)))
 :in-theory (union-theories
 '( lw-nrf-left-commutes lw-nrf-left-distributes lw-nrf-fold-constants lw-nrf-times-negative lw-nrf-negative-times lw-nrf-zero-times lw-nrf-minus-one lw-nrf-double-negative lw-nrf-add-cancel lw-nrf-double lw-nrf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

