(in-package "ACL2")

(include-book "polygon-product-budgets")

; Generate the whole product-grid check and both safe boundary paths
; from positive annuli and one uniform, computed rational step budget.

(local (defthm lw-ppa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppa-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppa-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppa-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppa-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppa-times-negative)))))

(local (defthm lw-ppa-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppa-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppa-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppa-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppa-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppa-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppa-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppa-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppa-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppa-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppa-left-commutes)))))

(local (defthm lw-ppa-length-natural
 (natp (len points)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ppa-same-consp
 (implies (equal (len left) (len right)) (equal (consp left) (consp right)))
 :rule-classes nil
 :hints (("Goal" :expand ((len left) (len right))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ppa-length-natural lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :cases ((consp left))))))

(local (defthm lw-ppa-same-tail-consp
 (implies (and (consp left) (consp right) (equal (len left) (len right)))
          (equal (consp (cdr left)) (consp (cdr right))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-ppa-same-consp (left (cdr left)) (right (cdr right))))
  :expand ((len left) (len right))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppa-length-natural lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-product-path-from-budgets
 (implies (and (lw-ray-annulus-pointsp left lower-left upper-left)
               (lw-ray-annulus-pointsp right lower-right upper-right)
               (equal (len left) (len right))
               (rationalp lower-left) (< 0 lower-left) (rationalp lower-right) (< 0 lower-right)
               (rationalp upper-left) (<= 0 upper-left) (rationalp upper-right) (<= 0 upper-right)
               (rationalp delta) (<= 0 delta)
               (lw-ray-path-step-check left delta) (lw-ray-path-step-check right delta)
               (< (+ (* delta upper-left) (* delta upper-right)) (* lower-left lower-right)))
  (lw-ray-product-path-check left right))
 :hints (("Goal" :induct (lw-ray-product-path-check left right)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-product-path-check lw-ray-path-step-check lw-ray-annulus-first len lw-ppa-length-natural lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use (lw-ppa-same-consp lw-ppa-same-tail-consp
                  (:instance lw-ray-annulus-first (points left) (lower lower-left) (upper upper-left))
                  (:instance lw-ray-annulus-first (points right) (lower lower-right) (upper upper-right))
                  (:instance lw-ray-annulus-first (points (cdr left)) (lower lower-left) (upper upper-left))
                  (:instance lw-ray-annulus-first (points (cdr right)) (lower lower-right) (upper upper-right))
                  (:instance lw-ray-product-strip-from-budgets
                    (points left) (bottom (car right)) (top (cadr right))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-product-path-check lw-ray-path-step-check lw-ray-annulus-first len lw-ppa-length-natural lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppa-square-gap
 (implies (and (rationalp x) (<= 0 x) (rationalp y) (< x y))
          (< (* x x) (* y y)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-ray-annulus-lower-upper
 (implies (and (consp points) (lw-ray-annulus-pointsp points lower upper)
               (rationalp lower) (< 0 lower) (rationalp upper) (<= 0 upper))
  (<= lower upper))
 :hints (("Goal"
  :use (lw-ray-annulus-first
        (:instance lw-complex-disk-norm-square (point (car points)) (radius upper))
        (:instance lw-ppa-square-gap (x upper) (y lower)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ppa-budget-small-steps
 (implies (and (rationalp lower-left) (< 0 lower-left) (rationalp lower-right) (< 0 lower-right)
               (rationalp upper-left) (<= lower-left upper-left)
               (rationalp upper-right) (<= lower-right upper-right)
               (rationalp delta) (<= 0 delta)
               (< (+ (* delta upper-left) (* delta upper-right)) (* lower-left lower-right)))
  (and (< delta lower-left) (< delta lower-right)))
 :hints (("Goal"
  :use ((:instance lw-ppa-multiply-order (a 0) (b upper-left) (factor delta))
        (:instance lw-ppa-multiply-order (a 0) (b upper-right) (factor delta))
        (:instance lw-ppa-multiply-order (a lower-left) (b upper-left) (factor delta))
        (:instance lw-ppa-multiply-order (a lower-right) (b upper-right) (factor delta)))
  :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppa-self-difference
 (implies (and (lw-complexp point) (rationalp delta) (<= 0 delta))
  (lw-complex-diskp (lw-complex-sub point point) delta))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppa-annulus-edge
 (implies (and (lw-complexp point) (lw-complexp next)
               (rationalp lower) (< 0 lower) (rationalp delta) (<= 0 delta) (< delta lower)
               (<= (* lower lower) (lw-complex-norm-square point))
               (lw-complex-diskp (lw-complex-sub next point) delta))
  (lw-ray-safe-edgep point next))
 :hints (("Goal"
  :use ((:instance lw-ppa-square-gap (x delta) (y lower))
        (:instance lw-complex-disk-positive-halfplane (anchor point) (point point) (radius delta))
        (:instance lw-complex-disk-positive-halfplane (anchor point) (point next) (radius delta))
        (:instance lw-ray-halfplane-safe-edge (h point) (a point) (b next)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppa-self-difference lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-annulus-path-safe
 (implies (and (consp points) (lw-ray-annulus-pointsp points lower upper)
               (rationalp lower) (< 0 lower) (rationalp delta) (<= 0 delta) (< delta lower)
               (lw-ray-path-step-check points delta))
  (lw-ray-safe-pathp (car points) (cdr points)))
 :hints (("Goal" :induct (lw-ray-path-step-check points delta)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-pointsp lw-ray-annulus-first lw-ray-path-step-check lw-ray-safe-pathp lw-complex-disk-data lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-ppa-annulus-edge (point (car points)) (next (cadr points))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-first lw-complex-disk-data lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-annulus-closed-polygon-safe
 (implies (and (consp points) (lw-ray-annulus-pointsp points lower upper)
               (rationalp lower) (< 0 lower) (rationalp delta) (<= 0 delta) (< delta lower)
               (lw-ray-path-step-check points delta)
               (equal (lw-ray-row-last points) (car points)))
  (lw-ray-safe-polygonp points))
 :hints (("Goal"
  :use (lw-ray-annulus-path-safe
        (:instance lw-ppa-annulus-edge (point (car points)) (next (car points))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-polygonp lw-ray-row-last lw-ray-annulus-first lw-ppa-self-difference lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-product-index-from-budgets
 (implies (and (consp left) (equal (len left) (len right))
               (lw-ray-annulus-pointsp left lower-left upper-left)
               (lw-ray-annulus-pointsp right lower-right upper-right)
               (equal (lw-ray-row-last left) (car left))
               (equal (lw-ray-row-last right) (car right))
               (rationalp lower-left) (< 0 lower-left) (rationalp lower-right) (< 0 lower-right)
               (rationalp upper-left) (<= 0 upper-left) (rationalp upper-right) (<= 0 upper-right)
               (rationalp delta) (<= 0 delta)
               (lw-ray-path-step-check left delta) (lw-ray-path-step-check right delta)
               (< (+ (* delta upper-left) (* delta upper-right)) (* lower-left lower-right)))
  (equal (lw-ray-polygon-index (lw-ray-pointwise-products left right))
         (+ (lw-ray-polygon-index left) (lw-ray-polygon-index right))))
 :hints (("Goal"
  :use (lw-ppa-same-consp lw-ray-product-path-from-budgets
        (:instance lw-ray-annulus-lower-upper (points left) (lower lower-left) (upper upper-left))
        (:instance lw-ray-annulus-lower-upper (points right) (lower lower-right) (upper upper-right))
        lw-ppa-budget-small-steps
        (:instance lw-ray-annulus-closed-polygon-safe (points left) (lower lower-left) (upper upper-left))
        (:instance lw-ray-annulus-closed-polygon-safe (points right) (lower lower-right) (upper upper-right))
        lw-ray-pointwise-product-index-additive)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-ray-product-index-at-computed-step
 (implies (and (consp left) (equal (len left) (len right))
               (lw-ray-annulus-pointsp left lower-left upper-left)
               (lw-ray-annulus-pointsp right lower-right upper-right)
               (equal (lw-ray-row-last left) (car left))
               (equal (lw-ray-row-last right) (car right))
               (rationalp lower-left) (< 0 lower-left) (rationalp lower-right) (< 0 lower-right)
               (rationalp upper-left) (<= 0 upper-left) (rationalp upper-right) (<= 0 upper-right)
               (lw-ray-path-step-check left
                 (lw-ray-product-step-budget lower-left upper-left lower-right upper-right))
               (lw-ray-path-step-check right
                 (lw-ray-product-step-budget lower-left upper-left lower-right upper-right)))
  (equal (lw-ray-polygon-index (lw-ray-pointwise-products left right))
         (+ (lw-ray-polygon-index left) (lw-ray-polygon-index right))))
 :hints (("Goal"
  :use (lw-ray-product-step-budget-valid
        (:instance lw-ray-product-index-from-budgets
          (delta (lw-ray-product-step-budget lower-left upper-left lower-right upper-right))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppa-left-commutes lw-ppa-left-distributes lw-ppa-fold-constants lw-ppa-times-negative lw-ppa-negative-times lw-ppa-zero-times lw-ppa-minus-one lw-ppa-double-negative lw-ppa-add-cancel lw-ppa-double lw-ppa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

