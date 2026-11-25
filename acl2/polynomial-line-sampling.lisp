; Exact uniform polynomial path samples and finite crossing sums.
(in-package "ACL2")
(include-book "polynomial-grid-perimeter")
(local (in-theory (disable lw-complexp lw-complex-polynomial lw-complex-segment
 lw-ray-row-index lw-ray-row-last lw-ray-pointsp lw-ray-path-last lw-ray-crossing
 lw-polynomial-edge-values lw-unit-mesh lw-polynomial-edge-check)))
(local (defthm lw-pls-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pls-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pls-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pls-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pls-times-negative (a b) (b a)))
                 :in-theory (disable lw-pls-times-negative)))))

(local (defthm lw-pls-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pls-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pls-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pls-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pls-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pls-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pls-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pls-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pls-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pls-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pls-left-commutes)))))
(defun lw-polynomial-line-point (left right count index)
 (lw-complex-segment left right (* index (/ count))))
(defun lw-polynomial-line-value (coefficients left right count index)
 (lw-complex-polynomial coefficients (lw-polynomial-line-point left right count index) 0))
(defun lw-polynomial-line-values (coefficients left right count index remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (lw-polynomial-line-value coefficients left right count index)
       (lw-polynomial-line-values coefficients left right count (+ 1 index) (- remaining 1)))))
(defun lw-polynomial-line-crossings (coefficients left right count index remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) 0
 (+ (lw-ray-crossing (lw-polynomial-line-value coefficients left right count index)
                    (lw-polynomial-line-value coefficients left right count (+ 1 index)))
    (lw-polynomial-line-crossings coefficients left right count (+ 1 index) (- remaining 1)))))
(defun lw-polynomial-line-check (coefficients left right count index remaining bound radius)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) t
 (and (lw-polynomial-edge-check coefficients
       (lw-polynomial-line-point left right count index)
       (lw-polynomial-line-point left right count (+ 1 index)) bound radius)
      (lw-polynomial-line-check coefficients left right count (+ 1 index) (- remaining 1) bound radius))))
(local (in-theory (disable lw-polynomial-line-point lw-polynomial-line-value lw-polynomial-line-values lw-polynomial-line-crossings lw-polynomial-line-check)))

(local (defthm lw-pls-heads
 (and (equal (consp (lw-polynomial-line-values coefficients left right count index remaining)) (not (zp remaining)))
      (implies (not (zp remaining))
       (and (equal (car (lw-polynomial-line-values coefficients left right count index remaining))
                   (lw-polynomial-line-value coefficients left right count index))
            (equal (cdr (lw-polynomial-line-values coefficients left right count index remaining))
                   (lw-polynomial-line-values coefficients left right count (+ 1 index) (- remaining 1))))))
 :hints (("Goal" :expand ((lw-polynomial-line-values coefficients left right count index remaining))
 :in-theory (union-theories
 '(lw-polynomial-line-values lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pls-row-last-cons
 (equal (lw-ray-row-last (cons current points))
 (if (endp points) current (lw-ray-row-last points)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-row-last lw-ray-path-last endp lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-line-values-as-mesh
 (equal (lw-polynomial-line-values coefficients left right count index remaining)
 (lw-polynomial-edge-values coefficients left right (lw-unit-mesh count index remaining)))
 :hints (("Goal" :induct (lw-unit-mesh count index remaining)
 :in-theory (union-theories
 '(lw-polynomial-line-values lw-polynomial-line-value lw-polynomial-line-point lw-unit-mesh lw-polynomial-edge-values endp lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-line-values-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp left) (lw-complexp right)
 (posp count) (natp index) (natp remaining))
 (and (lw-ray-pointsp (lw-polynomial-line-values coefficients left right count index remaining))
      (equal (len (lw-polynomial-line-values coefficients left right count index remaining)) remaining)))
 :hints (("Goal" :induct (lw-polynomial-line-values coefficients left right count index remaining)
 :in-theory (union-theories
 '(lw-polynomial-line-values lw-polynomial-line-value lw-polynomial-line-point lw-ray-pointsp lw-complex-polynomial-rational lw-complex-segment-rational len endp lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-line-crossings-integer
 (integerp (lw-polynomial-line-crossings coefficients left right count index remaining))
 :hints (("Goal" :induct (lw-polynomial-line-crossings coefficients left right count index remaining)
 :in-theory (union-theories
 '(lw-polynomial-line-crossings lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-crossing-data
    (a (lw-polynomial-line-value coefficients left right count index))
    (b (lw-polynomial-line-value coefficients left right count (+ 1 index))))) :do-not-induct t)))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-polynomial-line-crossings-split
 (implies (and (natp index) (natp prefix) (natp suffix))
 (equal (lw-polynomial-line-crossings coefficients left right count index (+ prefix suffix))
 (+ (lw-polynomial-line-crossings coefficients left right count index prefix)
    (lw-polynomial-line-crossings coefficients left right count (+ index prefix) suffix))))
 :hints (("Goal" :induct (lw-polynomial-line-crossings coefficients left right count index prefix)
 :in-theory (union-theories
 '(lw-polynomial-line-crossings lw-polynomial-line-crossings-integer lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-crossing-data
    (a (lw-polynomial-line-value coefficients left right count index))
    (b (lw-polynomial-line-value coefficients left right count (+ 1 index))))) :do-not-induct t))))

(local (defthm lw-pls-zero-values
 (equal (lw-polynomial-line-values coefficients left right count index 0) nil)
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-line-values lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pls-single-values
 (equal (lw-polynomial-line-values coefficients left right count index 1)
 (list (lw-polynomial-line-value coefficients left right count index)))
 :hints (("Goal" :expand ((lw-polynomial-line-values coefficients left right count index 1)) :in-theory (union-theories
 '(lw-polynomial-line-values lw-pls-zero-values lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-line-values-index
 (implies (and (natp index) (natp remaining))
 (equal (lw-ray-row-index (lw-polynomial-line-values coefficients left right count index (+ 1 remaining)))
        (lw-polynomial-line-crossings coefficients left right count index remaining)))
 :hints (("Goal" :induct (lw-polynomial-line-crossings coefficients left right count index remaining)
 :expand ((lw-polynomial-line-values coefficients left right count index (+ 1 remaining)))
 :in-theory (union-theories
 '((:induction lw-polynomial-line-values) lw-pls-zero-values lw-pls-single-values lw-polynomial-line-crossings lw-ray-row-index-cons lw-pls-heads lw-polynomial-line-crossings-integer endp lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-crossing-data
    (a (lw-polynomial-line-value coefficients left right count index))
    (b (lw-polynomial-line-value coefficients left right count (+ 1 index))))) :do-not-induct t))))

(defthm lw-polynomial-line-values-last
 (implies (and (natp index) (posp remaining))
 (equal (lw-ray-row-last (lw-polynomial-line-values coefficients left right count index remaining))
        (lw-polynomial-line-value coefficients left right count (+ index remaining -1))))
 :hints (("Goal" :induct (lw-polynomial-line-values coefficients left right count index remaining)
 :expand ((lw-polynomial-line-values coefficients left right count index remaining))
 :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-line-values) lw-pls-zero-values lw-pls-single-values lw-pls-row-last-cons lw-pls-heads endp lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-line-values-endpoints
 (implies (and (lw-complexp left) (lw-complexp right) (posp count))
 (and (equal (car (lw-polynomial-line-values coefficients left right count 0 (+ 1 count)))
             (lw-complex-polynomial coefficients left 0))
      (equal (lw-ray-row-last (lw-polynomial-line-values coefficients left right count 0 (+ 1 count)))
             (lw-complex-polynomial coefficients right 0))))
 :hints (("Goal"
 :use ((:instance inverse-of-* (x count))
       (:instance lw-polynomial-line-values-last (index 0) (remaining (+ 1 count)))
       lw-complex-segment-endpoints)
 :in-theory (union-theories
 '(lw-pls-heads lw-polynomial-line-value lw-polynomial-line-point lw-pls-left-commutes lw-pls-left-distributes lw-pls-fold-constants lw-pls-times-negative lw-pls-negative-times lw-pls-zero-times lw-pls-minus-one lw-pls-double-negative lw-pls-add-cancel lw-pls-double lw-pls-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
