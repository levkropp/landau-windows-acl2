(in-package "ACL2")

(include-book "polygon-fans")

; Every closed polygon whose straight edges avoid zero has the same
; integer winding after multiplication by any nonzero rational complex
; constant. The fan direction is computed from the polygon itself.

(local (defthm lw-pmp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pmp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pmp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pmp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pmp-times-negative (a b) (b a)))
                 :in-theory (disable lw-pmp-times-negative)))))

(local (defthm lw-pmp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pmp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pmp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pmp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pmp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pmp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pmp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pmp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pmp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pmp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pmp-left-commutes)))))

(defun lw-ray-multiply-points (factor points)
 (if (endp points) nil
  (cons (lw-complex-mul factor (car points))
        (lw-ray-multiply-points factor (cdr points)))))

(defthm lw-ray-multiply-points-data
 (implies (and (lw-complexp factor) (lw-ray-pointsp points))
  (and (lw-ray-pointsp (lw-ray-multiply-points factor points))
       (equal (len (lw-ray-multiply-points factor points)) (len points))
       (equal (consp (lw-ray-multiply-points factor points)) (consp points))))
 :hints (("Goal" :induct (lw-ray-multiply-points factor points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-multiply-points lw-ray-pointsp len lw-complex-ring-rational lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-multiply-points-last
 (equal (lw-ray-path-last (lw-complex-mul factor current) (lw-ray-multiply-points factor points))
        (lw-complex-mul factor (lw-ray-path-last current points)))
 :hints (("Goal" :induct (lw-ray-path-last current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-multiply-points lw-ray-path-last lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-safe-path-products
 (implies (and (lw-complexp factor) (not (equal factor (cons 0 0)))
               (lw-ray-safe-pathp current points))
  (lw-ray-safe-pathp (lw-complex-mul factor current) (lw-ray-multiply-points factor points)))
 :hints (("Goal" :induct (lw-ray-safe-pathp current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-pathp lw-ray-multiply-points lw-ray-safe-edge-products lw-complex-ring-rational lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-safe-polygon-products
 (implies (and (lw-complexp factor) (not (equal factor (cons 0 0)))
               (lw-ray-safe-polygonp points))
  (lw-ray-safe-polygonp (lw-ray-multiply-points factor points)))
 :hints (("Goal"
  :use ((:instance lw-ray-safe-path-products (current (car points)) (points (cdr points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-polygonp lw-ray-multiply-points lw-ray-multiply-points-last lw-ray-safe-edge-products lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((consp points)))))

(local (defthm lw-pmp-fan-edge
 (implies (and (lw-complexp anchor) (lw-ray-pointsp points)
               (consp points) (lw-ray-anchor-noncollinearp anchor points))
  (and (lw-ray-safe-edgep anchor (car points))
       (lw-ray-safe-edgep (car points) anchor)))
 :hints (("Goal"
  :use ((:instance lw-ray-noncollinear-edge (point (car points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-pointsp lw-ray-anchor-noncollinearp lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-fan-path-product-invariant
 (implies (and (lw-complexp factor) (not (equal factor (cons 0 0)))
               (lw-complexp anchor) (lw-ray-safe-pathp current points)
               (lw-ray-safe-edgep anchor current)
               (lw-ray-anchor-noncollinearp anchor points))
  (equal
   (lw-ray-fan-path-index (lw-complex-mul factor anchor) (lw-complex-mul factor current)
                          (lw-ray-multiply-points factor points))
   (lw-ray-fan-path-index anchor current points)))
 :hints (("Goal" :induct (lw-ray-fan-path-index anchor current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-fan-path-index lw-ray-multiply-points lw-ray-safe-pathp lw-ray-safe-path-data lw-ray-safe-edge-data lw-ray-anchor-noncollinearp lw-pmp-fan-edge lw-ray-triangle-product-invariant lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-ray-triangle-product-invariant (a anchor) (b current) (c (car points))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-path-data lw-ray-safe-edge-data lw-ray-pointsp lw-ray-anchor-noncollinearp lw-pmp-fan-edge lw-ray-noncollinear-edge lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pmp-last-anchor
 (implies (and (lw-complexp anchor) (lw-ray-safe-pathp current points)
               (not (equal (lw-complex-det anchor current) 0))
               (lw-ray-anchor-noncollinearp anchor points))
  (and (lw-ray-safe-edgep anchor (lw-ray-path-last current points))
       (lw-ray-safe-edgep (lw-ray-path-last current points) anchor)))
 :hints (("Goal"
  :use (lw-ray-anchor-noncollinear-last
        (:instance lw-ray-noncollinear-edge (point (lw-ray-path-last current points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-path-data lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pmp-with-anchor
 (implies (and (lw-complexp factor) (not (equal factor (cons 0 0)))
               (lw-ray-safe-polygonp points) (lw-complexp anchor)
               (lw-ray-anchor-noncollinearp anchor points))
  (equal (lw-ray-polygon-index (lw-ray-multiply-points factor points))
         (lw-ray-polygon-index points)))
 :hints (("Goal"
  :use (lw-ray-safe-polygon-data
        lw-ray-multiply-points-data
        lw-ray-polygon-fan-decomposition
        (:instance lw-ray-polygon-fan-decomposition
          (anchor (lw-complex-mul factor anchor))
          (points (lw-ray-multiply-points factor points)))
        (:instance lw-ray-fan-path-product-invariant
          (current (car points)) (points (cdr points)))
        (:instance lw-pmp-last-anchor (current (car points)) (points (cdr points)))
        (:instance lw-ray-triangle-product-invariant
          (a anchor) (b (lw-ray-path-last (car points) (cdr points))) (c (car points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-multiply-points lw-ray-polygon-index lw-ray-safe-polygonp lw-ray-safe-path-data lw-ray-pointsp lw-ray-multiply-points-last lw-ray-anchor-noncollinearp lw-pmp-fan-edge lw-ray-noncollinear-edge lw-complex-ring-rational lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((consp points)) :do-not-induct t))))

(defthm lw-ray-polygon-product-invariant
 (implies (and (lw-complexp factor) (not (equal factor (cons 0 0)))
               (lw-ray-safe-polygonp points))
  (equal (lw-ray-polygon-index (lw-ray-multiply-points factor points))
         (lw-ray-polygon-index points)))
 :hints (("Goal"
  :use (lw-ray-safe-polygon-data lw-ray-generic-anchor-certificate
        (:instance lw-pmp-with-anchor (anchor (lw-ray-generic-anchor points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pmp-left-commutes lw-pmp-left-distributes lw-pmp-fold-constants lw-pmp-times-negative lw-pmp-negative-times lw-pmp-zero-times lw-pmp-minus-one lw-pmp-double-negative lw-pmp-add-cancel lw-pmp-double lw-pmp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

