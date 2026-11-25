(in-package "ACL2")

(include-book "polynomial-line-clearance")

; Every rational line parameter has a computed coarse cell and local parameter.

(local (defthm lw-pmc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pmc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pmc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pmc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pmc-times-negative (a b) (b a)))
                 :in-theory (disable lw-pmc-times-negative)))))

(local (defthm lw-pmc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pmc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pmc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pmc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pmc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pmc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pmc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pmc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pmc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pmc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pmc-left-commutes)))))
(defun lw-unit-mesh-cell (count parameter)
 (if (equal parameter 0) 0 (- (lw-ceiling-rational (* count parameter)) 1)))
(defun lw-unit-mesh-local-parameter (count parameter)
 (- (* count parameter) (lw-unit-mesh-cell count parameter)))

(local (defthm lw-pmc-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pmc-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-unit-mesh-cell-data
 (implies (and (posp count) (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (and (natp (lw-unit-mesh-cell count parameter)) (< (lw-unit-mesh-cell count parameter) count)
       (rationalp (lw-unit-mesh-local-parameter count parameter))
       (<= 0 (lw-unit-mesh-local-parameter count parameter))
       (<= (lw-unit-mesh-local-parameter count parameter) 1)))
 :hints (("Goal"
  :use ((:instance lw-pmc-multiply-order (a 0) (b parameter) (factor count))
        (:instance lw-pmc-multiply-order (a parameter) (b 1) (factor count))
        (:instance lw-pmc-positive-product (a count) (b parameter))
        (:instance lw-ceiling-rational-natural (value (* count parameter)))
        (:instance lw-ceiling-rational-bracket (value (* count parameter))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-mesh-cell lw-unit-mesh-local-parameter lw-pmc-product-rational lw-pmc-sum-rational lw-pmc-left-commutes lw-pmc-left-distributes lw-pmc-fold-constants lw-pmc-times-negative lw-pmc-negative-times lw-pmc-zero-times lw-pmc-minus-one lw-pmc-double-negative lw-pmc-add-cancel lw-pmc-double lw-pmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-segment-mesh-cell
 (implies (and (lw-complexp left) (lw-complexp right) (posp count) (rationalp cell) (rationalp parameter))
  (equal
   (lw-complex-segment (lw-polynomial-line-point left right count cell)
                       (lw-polynomial-line-point left right count (+ 1 cell)) (- (* count parameter) cell))
   (lw-complex-segment left right parameter)))
 :hints (("Goal" :use ((:instance inverse-of-* (x count)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-line-point lw-complex-segment lw-complex-add lw-complex-scale lw-complexp lw-pmc-inverse-factor lw-pmc-product-rational lw-pmc-left-commutes lw-pmc-left-distributes lw-pmc-fold-constants lw-pmc-times-negative lw-pmc-negative-times lw-pmc-zero-times lw-pmc-minus-one lw-pmc-double-negative lw-pmc-add-cancel lw-pmc-double lw-pmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-complex-segment-mesh-cover
 (implies (and (lw-complexp left) (lw-complexp right) (posp count)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (equal
   (lw-complex-segment
    (lw-polynomial-line-point left right count (lw-unit-mesh-cell count parameter))
    (lw-polynomial-line-point left right count (+ 1 (lw-unit-mesh-cell count parameter)))
    (lw-unit-mesh-local-parameter count parameter))
   (lw-complex-segment left right parameter)))
 :hints (("Goal" :use (lw-unit-mesh-cell-data
                       (:instance lw-complex-segment-mesh-cell (cell (lw-unit-mesh-cell count parameter))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-mesh-local-parameter lw-pmc-left-commutes lw-pmc-left-distributes lw-pmc-fold-constants lw-pmc-times-negative lw-pmc-negative-times lw-pmc-zero-times lw-pmc-minus-one lw-pmc-double-negative lw-pmc-add-cancel lw-pmc-double lw-pmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-whole-line-excludes-clearance
 (implies (and (lw-polynomial-line-check coefficients left right count 0 count bound radius)
               (lw-complexp left) (lw-complexp right) (posp count)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (not (lw-complex-diskp (lw-complex-polynomial coefficients (lw-complex-segment left right parameter) 0)
    (lw-polynomial-line-clearance coefficients left right count 0 count bound radius))))
 :hints (("Goal"
  :use (lw-unit-mesh-cell-data lw-complex-segment-mesh-cover
        (:instance lw-polynomial-line-segment-excludes-clearance
          (index 0) (remaining count) (position (lw-unit-mesh-cell count parameter))
          (parameter (lw-unit-mesh-local-parameter count parameter))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pmc-left-commutes lw-pmc-left-distributes lw-pmc-fold-constants lw-pmc-times-negative lw-pmc-negative-times lw-pmc-zero-times lw-pmc-minus-one lw-pmc-double-negative lw-pmc-add-cancel lw-pmc-double lw-pmc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
