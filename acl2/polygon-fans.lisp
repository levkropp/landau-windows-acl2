(in-package "ACL2")

(include-book "ray-generic-anchor")
(include-book "polygon-paths")

; Exact fan triangulation of a closed polygon, plus total finite path
; predicates. Safe edges exclude the origin and allow positive collinearity.

(local (defthm lw-pfa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfa-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfa-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfa-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfa-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfa-times-negative)))))

(local (defthm lw-pfa-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfa-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfa-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfa-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfa-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfa-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfa-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfa-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfa-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfa-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfa-left-commutes)))))

(defun lw-ray-safe-pathp (current points)
 (if (endp points) (and (lw-complexp current) (equal points nil))
  (and (lw-ray-safe-edgep current (car points))
       (lw-ray-safe-pathp (car points) (cdr points)))))

(defun lw-ray-safe-polygonp (points)
 (if (endp points) (equal points nil)
  (and (lw-ray-safe-pathp (car points) (cdr points))
       (lw-ray-safe-edgep (lw-ray-path-last (car points) (cdr points)) (car points)))))

(defun lw-ray-fan-path-index (anchor current points)
 (if (endp points) 0
  (+ (lw-ray-triangle-index anchor current (car points))
     (lw-ray-fan-path-index anchor (car points) (cdr points)))))

(local (defthm lw-pfa-cross-integer
 (integerp (lw-ray-crossing a b))
 :hints (("Goal" :use (lw-ray-crossing-data) :in-theory (theory 'minimal-theory)))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-ray-fan-path-index-integer
 (integerp (lw-ray-fan-path-index anchor current points))
 :hints (("Goal" :induct (lw-ray-fan-path-index anchor current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-fan-path-index lw-ray-triangle-index lw-pfa-cross-integer lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-ray-safe-path-data
 (implies (lw-ray-safe-pathp current points)
  (and (lw-complexp current) (lw-ray-pointsp points)
       (lw-ray-nonzero-pointsp points)
       (lw-complexp (lw-ray-path-last current points))))
 :hints (("Goal" :induct (lw-ray-safe-pathp current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-pathp lw-ray-safe-edge-data lw-ray-pointsp lw-ray-nonzero-pointsp lw-ray-path-last lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-safe-polygon-data
 (implies (lw-ray-safe-polygonp points)
  (and (lw-ray-pointsp points) (lw-ray-nonzero-pointsp points)
       (implies (consp points)
        (and (lw-ray-safe-pathp (car points) (cdr points))
             (lw-ray-safe-edgep (lw-ray-path-last (car points) (cdr points)) (car points))))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-polygonp lw-ray-safe-path-data lw-ray-safe-edge-data lw-ray-pointsp lw-ray-nonzero-pointsp lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-safe-path-first
 (implies (and (consp points) (lw-ray-safe-pathp current points))
  (and (lw-ray-safe-edgep current (car points))
       (lw-ray-safe-pathp (car points) (cdr points))))
 :hints (("Goal" :expand ((lw-ray-safe-pathp current points))
          :in-theory (union-theories
 '( lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-fan-path-decomposition
 (implies (and (lw-complexp anchor) (lw-complexp current) (lw-ray-pointsp points))
  (equal (lw-ray-fan-path-index anchor current points)
   (+ (lw-ray-path-index current points)
      (lw-ray-crossing anchor current)
      (- (lw-ray-crossing anchor (lw-ray-path-last current points))))))
 :hints (("Goal" :induct (lw-ray-fan-path-index anchor current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-fan-path-index lw-ray-path-index lw-ray-path-last lw-ray-pointsp lw-ray-triangle-index lw-pfa-cross-integer lw-ray-path-index-integer lw-ray-fan-path-index-integer lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-ray-crossing-reverse (a anchor) (b (car points))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-pfa-cross-integer lw-ray-path-index-integer lw-ray-fan-path-index-integer lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-polygon-fan-decomposition
 (implies (and (lw-complexp anchor) (lw-ray-pointsp points))
  (equal (lw-ray-polygon-index points)
   (if (endp points) 0
    (+ (lw-ray-fan-path-index anchor (car points) (cdr points))
       (lw-ray-triangle-index anchor
        (lw-ray-path-last (car points) (cdr points)) (car points))))))
 :hints (("Goal"
  :use ((:instance lw-ray-fan-path-decomposition
          (current (car points)) (points (cdr points)))
        (:instance lw-ray-crossing-reverse (a anchor) (b (car points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-polygon-index lw-ray-pointsp lw-ray-triangle-index lw-pfa-cross-integer lw-ray-path-index-integer lw-ray-fan-path-index-integer lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((consp points)))))

(defthm lw-ray-noncollinear-edge
 (implies (and (lw-complexp anchor) (lw-complexp point)
               (not (equal (lw-complex-det anchor point) 0)))
  (and (lw-ray-safe-edgep anchor point) (lw-ray-safe-edgep point anchor)))
 :hints (("Goal" :use ((:instance lw-complex-det-reverse (a anchor) (b point)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-edgep lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

