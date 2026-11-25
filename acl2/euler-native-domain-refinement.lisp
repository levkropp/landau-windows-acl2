; Identify native value refinement with sampling an actual subdivided domain polygon.
(in-package "ACL2")
(include-book "euler-native-refinement")
(local (in-theory (disable lw-euler-native-path-values lw-euler-native-edge-values lw-euler-native-edge-samples
 lw-euler-native-refinement-blocks lw-euler-native-refined-polygon
 lw-polynomial-path-values lw-polynomial-path-blocks lw-polynomial-path-refinement
 lw-polynomial-edge-values lw-polynomial-edge-samples lw-complex-polynomial
 lw-ray-refine-path lw-ray-refine-polygon lw-ray-indexed-slice lw-ray-close-polygon
 lw-euler-polygon-index-check lw-square-point-listp lw-unit-parametersp lw-unit-mesh)))
(local (defthm lw-ndr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ndr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ndr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ndr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ndr-times-negative (a b) (b a)))
                 :in-theory (disable lw-ndr-times-negative)))))

(local (defthm lw-ndr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ndr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ndr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ndr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ndr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ndr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ndr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ndr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ndr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ndr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ndr-left-commutes)))))
(defun lw-euler-native-block-values (blocks value-error)
 (if (endp blocks) nil
 (cons (lw-euler-native-path-values (car blocks) value-error)
       (lw-euler-native-block-values (cdr blocks) value-error))))
(local (in-theory (disable lw-euler-native-block-values)))

(local (defthm lw-ndr-length-natural
 (natp (len points)) :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-ndr-nth-zero
 (equal (nth 0 values) (car values))
 :hints (("Goal" :expand ((nth 0 values)) :in-theory (union-theories
 '(nth lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ndr-slice-heads
 (and (equal (consp (lw-ray-indexed-slice values index remaining)) (not (zp remaining)))
      (implies (not (zp remaining))
       (and (equal (car (lw-ray-indexed-slice values index remaining)) (nth index values))
            (equal (cdr (lw-ray-indexed-slice values index remaining))
                   (lw-ray-indexed-slice values (+ 1 index) (- remaining 1))))))
 :hints (("Goal" :expand ((lw-ray-indexed-slice values index remaining))
 :in-theory (union-theories
 '(lw-ray-indexed-slice lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-native-refine-path-map
 (equal
 (lw-euler-native-path-values (lw-ray-refine-path current points blocks) value-error)
 (lw-ray-refine-path
  (lw-complex-euler-continuation-value (car current) (cdr current) value-error)
  (lw-euler-native-path-values points value-error) (lw-euler-native-block-values blocks value-error)))
 :hints (("Goal" :induct (lw-ray-refine-path current points blocks)
 :in-theory (union-theories
 '(lw-ray-refine-path lw-euler-native-path-values lw-euler-native-block-values lw-euler-native-path-values-append endp lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-native-refine-polygon-map
 (equal
 (lw-euler-native-path-values (lw-ray-refine-polygon points blocks) value-error)
 (lw-ray-refine-polygon (lw-euler-native-path-values points value-error)
                       (lw-euler-native-block-values blocks value-error)))
 :hints (("Goal" :use (lw-euler-native-path-values-shape
       (:instance lw-euler-native-refine-path-map (current (car points)) (points (cdr points))))
 :in-theory (union-theories
 '(lw-ray-refine-polygon lw-euler-native-path-values endp lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-ndr-identity-value
 (implies (lw-complexp point) (equal (lw-complex-polynomial '((0 . 0) (1 . 0)) point 0) point))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial lw-complex-power lw-complex-add lw-complex-mul lw-complexp endp nfix lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ndr-identity-path
 (implies (lw-ray-pointsp points) (equal (lw-polynomial-path-values '((0 . 0) (1 . 0)) points) points))
 :hints (("Goal" :induct (lw-polynomial-path-values '((0 . 0) (1 . 0)) points)
 :in-theory (union-theories
 '(lw-polynomial-path-values lw-ray-pointsp lw-ndr-identity-value endp lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-native-edge-parameters-domain
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)) (lw-unit-parametersp parameters))
 (equal
 (lw-euler-native-path-values (lw-polynomial-edge-values '((0 . 0) (1 . 0)) (nth index (lw-ray-close-polygon points)) (nth (+ 1 index) (lw-ray-close-polygon points)) parameters) value-error)
 (lw-euler-native-edge-values points index parameters value-error)))
 :hints (("Goal" :induct (lw-euler-native-edge-values points index parameters value-error)
 :in-theory (union-theories
 '(lw-euler-native-edge-values lw-euler-native-path-values lw-polynomial-edge-values lw-unit-parametersp endp lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use (lw-euler-polygon-edge-data
         (:instance lw-complex-segment-rational (left (nth index (lw-ray-close-polygon points))) (right (nth (+ 1 index) (lw-ray-close-polygon points))) (parameter (car parameters))))
   :in-theory (union-theories
 '(lw-euler-native-edge-value lw-euler-polygon-edge-point lw-square-containsp lw-ndr-identity-value lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
   :do-not-induct t))))

(defthm lw-euler-native-edge-samples-domain
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)) (posp count))
 (equal
 (lw-euler-native-path-values (lw-polynomial-edge-samples '((0 . 0) (1 . 0)) (nth index (lw-ray-close-polygon points)) (nth (+ 1 index) (lw-ray-close-polygon points)) count) value-error)
 (lw-euler-native-edge-samples points index count value-error)))
 :hints (("Goal"
 :use ((:instance lw-unit-mesh-data (index 1) (remaining (nfix (- count 1))))
       (:instance lw-euler-native-edge-parameters-domain
        (parameters (lw-unit-mesh count 1 (nfix (- count 1))))))
 :in-theory (union-theories
 '(lw-euler-native-edge-samples lw-polynomial-edge-samples nfix lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-refinement-blocks-domain
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (posp count) (natp index) (natp remaining) (<= (+ index remaining) (len points)))
 (equal
 (lw-euler-native-block-values (lw-polynomial-path-blocks '((0 . 0) (1 . 0)) (nth index (lw-ray-close-polygon points)) (lw-ray-indexed-slice (lw-ray-close-polygon points) (+ 1 index) remaining) count) value-error)
 (lw-euler-native-refinement-blocks points count value-error index remaining)))
 :hints (("Goal"
 :induct (lw-euler-native-refinement-blocks points count value-error index remaining)
 :in-theory (union-theories
 '(lw-euler-native-refinement-blocks lw-euler-native-block-values lw-polynomial-path-blocks lw-ndr-slice-heads lw-ray-indexed-slice endp fold-consts-in-+ lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use (lw-euler-native-edge-samples-domain)
   :do-not-induct t))))

(defthm lw-euler-native-refined-polygon-domain
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (posp count))
 (equal
 (lw-euler-native-refined-polygon points count value-error)
 (lw-euler-native-path-values
  (lw-polynomial-path-refinement '((0 . 0) (1 . 0)) (lw-ray-close-polygon points) count) value-error)))
 :hints (("Goal"
 :use (lw-square-point-list-data lw-square-point-list-close
       (:instance lw-square-point-list-data (points (lw-ray-close-polygon points)))
       (:instance lw-ray-close-polygon-data)
       (:instance lw-ray-indexed-slice-tail (values (lw-ray-close-polygon points)))
       (:instance lw-euler-native-refinement-blocks-domain (index 0) (remaining (len points)))
       (:instance lw-euler-native-refine-polygon-map
        (points (lw-ray-close-polygon points)) (blocks (lw-polynomial-path-blocks '((0 . 0) (1 . 0)) (car (lw-ray-close-polygon points)) (cdr (lw-ray-close-polygon points)) count))))
 :in-theory (union-theories
 '(lw-euler-native-refined-polygon lw-polynomial-path-refinement lw-ndr-identity-path lw-euler-polygon-index-check lw-ndr-nth-zero lw-ndr-length-natural fold-consts-in-+ lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-domain-refinement-index
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (posp count) (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (equal
 (lw-euler-native-polygon-index (lw-polynomial-path-refinement '((0 . 0) (1 . 0)) (lw-ray-close-polygon points) count) value-error)
 (lw-euler-polygon-index anchor side points base-target base-error)))
 :hints (("Goal" :use (lw-euler-native-refined-polygon-domain lw-euler-native-refined-polygon-base-index)
 :in-theory (union-theories
 '(lw-euler-native-polygon-index lw-ndr-left-commutes lw-ndr-left-distributes lw-ndr-fold-constants lw-ndr-times-negative lw-ndr-negative-times lw-ndr-zero-times lw-ndr-minus-one lw-ndr-double-negative lw-ndr-add-cancel lw-ndr-double lw-ndr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

