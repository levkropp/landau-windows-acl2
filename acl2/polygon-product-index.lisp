(in-package "ACL2")

(include-book "polygon-product-checks")

; A checked diagonal through a product grid has the same crossing sum as
; the lower row followed by the right column. Closed paths therefore
; have additive winding under pointwise multiplication.

(local (defthm lw-ppi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppi-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppi-times-negative)))))

(local (defthm lw-ppi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppi-left-commutes)))))

(defun lw-ray-pointwise-products (left right)
 (if (endp left) nil
  (cons (lw-complex-mul (car right) (car left))
        (lw-ray-pointwise-products (cdr left) (cdr right)))))

(local (defthm lw-ppi-length-natural
 (natp (len points)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ppi-cross-integer
 (integerp (lw-ray-crossing a b))
 :hints (("Goal" :use (lw-ray-crossing-data) :in-theory (theory 'minimal-theory)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ppi-map-head
 (implies (consp points)
  (and (consp (lw-ray-multiply-points factor points))
       (equal (car (lw-ray-multiply-points factor points)) (lw-complex-mul factor (car points)))
       (equal (cdr (lw-ray-multiply-points factor points)) (lw-ray-multiply-points factor (cdr points)))))
 :hints (("Goal" :expand ((lw-ray-multiply-points factor points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-map-length
 (equal (len (lw-ray-multiply-points factor points)) (len points))
 :hints (("Goal" :induct (lw-ray-multiply-points factor points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-multiply-points len lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-points-head
 (implies (and (consp points) (lw-ray-pointsp points))
  (and (lw-complexp (car points)) (lw-ray-pointsp (cdr points))))
 :hints (("Goal" :expand ((lw-ray-pointsp points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-products-head
 (implies (consp left)
  (and (consp (lw-ray-pointwise-products left right))
       (equal (car (lw-ray-pointwise-products left right)) (lw-complex-mul (car right) (car left)))
       (equal (cdr (lw-ray-pointwise-products left right))
              (lw-ray-pointwise-products (cdr left) (cdr right)))))
 :hints (("Goal" :expand ((lw-ray-pointwise-products left right))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-pointwise-products-data
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right) (equal (len left) (len right)))
  (and (lw-ray-pointsp (lw-ray-pointwise-products left right))
       (equal (len (lw-ray-pointwise-products left right)) (len left))
       (equal (consp (lw-ray-pointwise-products left right)) (consp left))))
 :hints (("Goal" :induct (lw-ray-pointwise-products left right)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-pointwise-products lw-ray-pointsp len lw-ppi-length-natural lw-complex-ring-rational lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ppi-row-last-tail
 (implies (and (consp points) (consp (cdr points)))
  (equal (lw-ray-row-last points) (lw-ray-row-last (cdr points))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :expand ((lw-ray-path-last (car points) (cdr points)))))))

(local (defthm lw-ppi-row-single
 (implies (and (consp points) (equal (cdr points) nil))
  (and (equal (lw-ray-row-index points) 0)
       (equal (lw-ray-row-last points) (car points))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-index lw-ray-row-last lw-ray-path-index lw-ray-path-last lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-map-row-last
 (implies (consp points)
  (equal (lw-ray-row-last (lw-ray-multiply-points factor points))
         (lw-complex-mul factor (lw-ray-row-last points))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-ppi-map-head lw-ray-multiply-points-last lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-row-step
 (implies (and (consp points) (consp (cdr points)))
  (equal (lw-ray-row-index points)
   (+ (lw-ray-crossing (car points) (cadr points)) (lw-ray-row-index (cdr points)))))
 :hints (("Goal" :expand ((lw-ray-row-index points) (lw-ray-path-index (car points) (cdr points)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-index lw-ray-path-index-integer lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-pointwise-products-last
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
               (consp left) (equal (len left) (len right)))
  (equal (lw-ray-row-last (lw-ray-pointwise-products left right))
         (lw-complex-mul (lw-ray-row-last right) (lw-ray-row-last left))))
 :hints (("Goal" :induct (lw-ray-pointwise-products left right)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-pointsp len lw-ppi-length-natural lw-ray-pointwise-products lw-ppi-row-last-tail lw-ppi-row-single lw-ppi-products-head lw-ray-row-last lw-ray-path-last lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ppi-diagonal-step
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
               (consp left) (consp (cdr left)) (consp right) (consp (cdr right))
               (equal (len left) (len right)) (lw-ray-product-path-check left right)
               (equal (lw-ray-row-index (lw-ray-pointwise-products (cdr left) (cdr right)))
                (+ (lw-ray-row-index (lw-ray-multiply-points (cadr right) (cdr left)))
                   (lw-ray-row-index (lw-ray-multiply-points (lw-ray-row-last left) (cdr right))))))
  (equal (lw-ray-row-index (lw-ray-pointwise-products left right))
   (+ (lw-ray-row-index (lw-ray-multiply-points (car right) left))
      (lw-ray-row-index (lw-ray-multiply-points (lw-ray-row-last left) right)))))
 :hints (("Goal"
  :use ((:instance lw-ray-product-check-first-triangle
          (points left) (lower (car right)) (upper (cadr right)))
        (:instance lw-ray-product-check-strip-zero
          (points (cdr left)) (lower (car right)) (upper (cadr right)))
        (:instance lw-ray-row-strip-boundary
          (bottom (lw-ray-multiply-points (car right) (cdr left)))
          (top (lw-ray-multiply-points (cadr right) (cdr left))))
        (:instance lw-ray-crossing-reverse
          (a (lw-complex-mul (car right) (car left)))
          (b (lw-complex-mul (cadr right) (cadr left)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-product-path-check lw-ray-product-strip-check-tail lw-ray-multiply-points-data lw-ray-pointwise-products-data lw-ray-pointsp lw-ray-row-last-complex lw-ppi-row-last-tail lw-ppi-map-row-last lw-ppi-row-step lw-ppi-map-head lw-ppi-map-length lw-ppi-points-head lw-ppi-products-head lw-ray-triangle-index lw-ppi-cross-integer lw-ray-row-index-integer lw-complex-ring-rational lw-complex-mul-commutative lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ppi-zero-length
 (implies (and (lw-ray-pointsp points) (equal (len points) 0)) (equal points nil))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-pointsp len lw-ppi-length-natural lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-diagonal-single
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
               (consp left) (endp (cdr left)) (equal (len left) (len right)))
  (equal (lw-ray-row-index (lw-ray-pointwise-products left right))
   (+ (lw-ray-row-index (lw-ray-multiply-points (car right) left))
      (lw-ray-row-index (lw-ray-multiply-points (lw-ray-row-last left) right)))))
 :hints (("Goal" :use ((:instance lw-ppi-zero-length (points (cdr right))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-pointsp len lw-ppi-length-natural lw-ray-pointwise-products lw-ray-multiply-points lw-ray-row-index lw-ray-path-index lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-same-consp
 (implies (equal (len left) (len right)) (equal (consp left) (consp right)))
 :rule-classes nil
 :hints (("Goal" :expand ((len left) (len right))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ppi-length-natural lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :cases ((consp left))))))

(local (defthm lw-ppi-same-tail-consp
 (implies (and (consp left) (consp right) (equal (len left) (len right)))
          (equal (consp (cdr left)) (consp (cdr right))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-ppi-same-consp (left (cdr left)) (right (cdr right))))
  :expand ((len left) (len right))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppi-length-natural lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-equal-length-shape
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right) (equal (len left) (len right)))
  (and (equal (consp left) (consp right))
       (implies (consp left) (equal (consp (cdr left)) (consp (cdr right))))))
 :rule-classes nil
 :hints (("Goal" :use (lw-ppi-same-consp lw-ppi-same-tail-consp)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :cases ((consp left))))))

(local (defun lw-ppi-boundary-induct (left right)
 (if (or (endp left) (endp (cdr left))) right
  (lw-ppi-boundary-induct (cdr left) (cdr right)))))

(defthm lw-ray-product-diagonal-boundary
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
               (consp left) (equal (len left) (len right)) (lw-ray-product-path-check left right))
  (equal (lw-ray-row-index (lw-ray-pointwise-products left right))
   (+ (lw-ray-row-index (lw-ray-multiply-points (car right) left))
      (lw-ray-row-index (lw-ray-multiply-points (lw-ray-row-last left) right)))))
 :hints (("Goal" :induct (lw-ppi-boundary-induct left right)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ppi-boundary-induct) lw-ray-pointsp len lw-ppi-length-natural lw-ppi-diagonal-single lw-ppi-diagonal-step lw-ray-product-path-check lw-ppi-row-last-tail lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-ppi-equal-length-shape)
            :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-pointsp len lw-ppi-length-natural lw-ppi-diagonal-single lw-ppi-diagonal-step lw-ray-product-path-check lw-ppi-row-last-tail lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppi-closed-row-index
 (implies (and (lw-ray-pointsp points) (consp points)
               (equal (lw-ray-row-last points) (car points)))
  (equal (lw-ray-polygon-index points) (lw-ray-row-index points)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-polygon-index lw-ray-row-index lw-ray-row-last lw-ray-crossing-self lw-ray-pointsp lw-ray-path-index-integer lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-pointwise-product-index-additive
 (implies (and (lw-ray-safe-polygonp left) (lw-ray-safe-polygonp right)
               (consp left) (equal (len left) (len right))
               (equal (lw-ray-row-last left) (car left))
               (equal (lw-ray-row-last right) (car right))
               (lw-ray-product-path-check left right))
  (equal (lw-ray-polygon-index (lw-ray-pointwise-products left right))
         (+ (lw-ray-polygon-index left) (lw-ray-polygon-index right))))
 :hints (("Goal"
  :use ((:instance lw-ray-safe-polygon-data (points left))
        (:instance lw-ray-safe-polygon-data (points right))
        lw-ray-product-diagonal-boundary
        (:instance lw-ray-polygon-product-invariant (factor (car right)) (points left))
        (:instance lw-ray-polygon-product-invariant (factor (car left)) (points right))
        (:instance lw-ppi-closed-row-index (points (lw-ray-pointwise-products left right)))
        (:instance lw-ppi-closed-row-index (points (lw-ray-multiply-points (car right) left)))
        (:instance lw-ppi-closed-row-index (points (lw-ray-multiply-points (car left) right))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-pointwise-products-data lw-ray-pointwise-products-last lw-ray-multiply-points-data lw-ppi-map-row-last lw-ppi-map-head lw-ppi-map-length lw-ppi-points-head lw-ppi-products-head lw-ray-nonzero-pointsp lw-ray-pointsp len lw-ppi-length-natural lw-ppi-left-commutes lw-ppi-left-distributes lw-ppi-fold-constants lw-ppi-times-negative lw-ppi-negative-times lw-ppi-zero-times lw-ppi-minus-one lw-ppi-double-negative lw-ppi-add-cancel lw-ppi-double lw-ppi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

