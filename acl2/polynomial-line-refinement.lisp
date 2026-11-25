; A fixed checked uniform polynomial path retains its index at every multiple mesh.
(in-package "ACL2")
(include-book "polynomial-line-sampling")
(local (in-theory (disable lw-complexp lw-complex-segment lw-complex-add lw-complex-scale
 lw-complex-polynomial lw-ray-row-index lw-ray-row-last lw-ray-path-index lw-ray-path-last
 lw-ray-halfplane-points lw-complex-positive-halfplanep lw-ray-crossing lw-polynomial-edge-check
 lw-unit-mesh lw-polynomial-edge-values lw-polynomial-line-point lw-polynomial-line-value
 lw-polynomial-line-values lw-polynomial-line-crossings lw-polynomial-line-check)))
(local (defthm lw-plr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-plr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-plr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-plr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-plr-times-negative (a b) (b a)))
                 :in-theory (disable lw-plr-times-negative)))))

(local (defthm lw-plr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-plr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-plr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-plr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-plr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-plr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-plr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-plr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-plr-left-commutes)))))

(local (defthm lw-plr-cancel-equality
 (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
 (equal (* factor a) (* factor b))) (equal a b))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-plr-inverse-product
 (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
 (equal (/ (* a b)) (* (/ a) (/ b))))
 :hints (("Goal"
 :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
       (:instance inverse-of-* (x (* a b)))
       (:instance lw-plr-cancel-equality (factor (* a b)) (a (/ (* a b))) (b (* (/ a) (/ b)))))
 :in-theory (disable inverse-of-*) :nonlinearp t))))

(local (defthm lw-plr-natural-product
 (implies (and (natp a) (natp b)) (natp (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes (:rewrite :type-prescription)))

(defthm lw-ray-halfplane-row-index
 (implies (and (consp points) (lw-ray-halfplane-points h points))
 (equal (lw-ray-row-index points) (lw-ray-crossing (car points) (lw-ray-row-last points))))
 :hints (("Goal"
 :use ((:instance lw-ray-path-halfplane-potential (current (car points)) (points (cdr points)))
       (:instance lw-ray-path-last-halfplane (current (car points)) (points (cdr points)))
       (:instance lw-ray-halfplane-potential (a (car points)) (b (lw-ray-row-last points)))
       (:instance lw-ray-crossing-data (a h) (b (car points)))
       (:instance lw-ray-crossing-data (a h) (b (lw-ray-row-last points))))
 :in-theory (union-theories
 '(lw-ray-halfplane-points lw-ray-row-index lw-ray-row-last endp lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-plr-positive-length
 (implies (< 0 (len points)) (consp points))
 :hints (("Goal" :in-theory (union-theories
 '(len endp lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil))

(defthm lw-polynomial-line-edge-index
 (implies (and (posp count) (lw-polynomial-edge-check coefficients left right bound radius))
 (equal (lw-polynomial-line-crossings coefficients left right count 0 count)
        (lw-ray-crossing (lw-complex-polynomial coefficients left 0) (lw-complex-polynomial coefficients right 0))))
 :hints (("Goal"
 :use ((:instance lw-unit-mesh-data (index 0) (remaining (+ 1 count)))
       (:instance lw-polynomial-edge-values-halfplane (parameters (lw-unit-mesh count 0 (+ 1 count))))
       (:instance lw-polynomial-line-values-index (index 0) (remaining count))
       (:instance lw-ray-halfplane-row-index
        (h (lw-complex-polynomial coefficients left 0))
        (points (lw-polynomial-line-values coefficients left right count 0 (+ 1 count))))
       lw-polynomial-line-values-endpoints
       (:instance lw-plr-positive-length (points (lw-polynomial-line-values coefficients left right count 0 (+ 1 count))))
       (:instance lw-polynomial-line-values-data (index 0) (remaining (+ 1 count))))
 :in-theory (union-theories
 '(lw-polynomial-line-values-as-mesh lw-polynomial-edge-check lw-unit-mesh lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-line-refinement-point
 (implies (and (lw-complexp left) (lw-complexp right) (posp coarse) (posp factor) (natp cell) (natp index))
 (equal
 (lw-polynomial-line-point
  (lw-polynomial-line-point left right coarse cell)
  (lw-polynomial-line-point left right coarse (+ 1 cell)) factor index)
 (lw-polynomial-line-point left right (* coarse factor) (+ (* cell factor) index))))
 :hints (("Goal"
 :use ((:instance inverse-of-* (x coarse)) (:instance inverse-of-* (x factor)))
 :in-theory (union-theories
 '(lw-polynomial-line-point lw-complex-segment lw-complex-add lw-complex-scale lw-complexp lw-plr-inverse-product lw-plr-inverse-factor fold-consts-in-+ lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-line-refinement-values
 (implies (and (lw-complexp left) (lw-complexp right) (posp coarse) (posp factor) (natp cell) (natp index) (natp remaining))
 (equal
 (lw-polynomial-line-values coefficients
  (lw-polynomial-line-point left right coarse cell)
  (lw-polynomial-line-point left right coarse (+ 1 cell)) factor index remaining)
 (lw-polynomial-line-values coefficients left right (* coarse factor) (+ (* cell factor) index) remaining)))
 :hints (("Goal" :induct (lw-unit-mesh factor index remaining)
 :in-theory (union-theories
 '(lw-unit-mesh lw-polynomial-line-values lw-polynomial-line-value lw-polynomial-line-refinement-point fold-consts-in-+ lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-line-refined-block-index
 (implies (and (lw-complexp left) (lw-complexp right) (posp coarse) (posp factor) (natp cell)
 (lw-polynomial-edge-check coefficients
  (lw-polynomial-line-point left right coarse cell)
  (lw-polynomial-line-point left right coarse (+ 1 cell)) bound radius))
 (equal (lw-polynomial-line-crossings coefficients left right (* coarse factor) (* cell factor) factor)
 (lw-ray-crossing (lw-polynomial-line-value coefficients left right coarse cell)
                  (lw-polynomial-line-value coefficients left right coarse (+ 1 cell)))))
 :hints (("Goal"
 :use ((:instance lw-polynomial-line-refinement-values (index 0) (remaining (+ 1 factor)))
       (:instance lw-polynomial-line-values-index (count (* coarse factor)) (index (* cell factor)) (remaining factor))
       (:instance lw-polynomial-line-values-index
        (left (lw-polynomial-line-point left right coarse cell))
        (right (lw-polynomial-line-point left right coarse (+ 1 cell)))
        (count factor) (index 0) (remaining factor))
       (:instance lw-polynomial-line-edge-index
        (left (lw-polynomial-line-point left right coarse cell))
        (right (lw-polynomial-line-point left right coarse (+ 1 cell))) (count factor)))
 :in-theory (union-theories
 '(lw-polynomial-line-value lw-plr-natural-product lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-plr-zero-crossings
 (equal (lw-polynomial-line-crossings coefficients left right count index 0) 0)
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-line-crossings lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-plr-crossings-step
 (implies (not (zp remaining))
 (equal (lw-polynomial-line-crossings coefficients left right count index remaining)
 (+ (lw-ray-crossing (lw-polynomial-line-value coefficients left right count index)
                    (lw-polynomial-line-value coefficients left right count (+ 1 index)))
    (lw-polynomial-line-crossings coefficients left right count (+ 1 index) (- remaining 1)))))
 :hints (("Goal" :expand ((lw-polynomial-line-crossings coefficients left right count index remaining))
 :in-theory (union-theories
 '(lw-polynomial-line-crossings lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil))

(defthm lw-polynomial-line-refinement-index
 (implies (and (lw-complexp left) (lw-complexp right) (posp coarse) (posp factor) (natp index) (natp remaining)
 (lw-polynomial-line-check coefficients left right coarse index remaining bound radius))
 (equal (lw-polynomial-line-crossings coefficients left right (* coarse factor) (* index factor) (* remaining factor))
        (lw-polynomial-line-crossings coefficients left right coarse index remaining)))
 :hints (("Goal" :induct (lw-polynomial-line-check coefficients left right coarse index remaining bound radius)
 :in-theory (union-theories
 '(lw-polynomial-line-check lw-plr-natural-product lw-plr-zero-crossings lw-polynomial-line-crossings-integer fold-consts-in-+ lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-plr-natural-product (a (- remaining 1)) (b factor))
         (:instance lw-polynomial-line-crossings-split
     (count (* coarse factor)) (index (* index factor)) (prefix factor) (suffix (* (- remaining 1) factor)))
         (:instance lw-polynomial-line-refined-block-index (cell index))
         (:instance lw-plr-crossings-step (count coarse))) :do-not-induct t))))
