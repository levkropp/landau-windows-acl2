(in-package "ACL2")

(include-book "polynomial-normalization-check")
(include-book "polynomial-nonnegative-index")

; Nonnegative counts for every checked rational square, by exact affine transport.

(local (defthm lw-psx-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psx-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psx-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psx-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psx-times-negative (a b) (b a)))
                 :in-theory (disable lw-psx-times-negative)))))

(local (defthm lw-psx-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psx-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psx-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psx-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psx-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psx-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psx-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psx-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psx-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psx-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psx-left-commutes)))))
(defthm lw-polynomial-square-index-normalize
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse))
  (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse)) (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-polynomial-square-normalize coefficients anchor side) (cons -1 -1) 2 (lw-polynomial-normalization-count coefficients anchor side coarse)))))
 :hints (("Goal"
  :use (lw-polynomial-normalization-count-data lw-polynomial-normalization-factor-data
        (:instance lw-polynomial-square-normalize-grid (count (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-polynomial-square-refinement-index (factor (lw-polynomial-normalization-factor coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-normalization-count lw-psx-left-commutes lw-psx-left-distributes lw-psx-fold-constants lw-psx-times-negative lw-psx-negative-times lw-psx-zero-times lw-psx-minus-one lw-psx-double-negative lw-psx-add-cancel lw-psx-double lw-psx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-index-factor-count
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse))
  (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse))
   (lw-unit-square-factor-count (lw-polynomial-square-factor-roots (lw-polynomial-square-normalize coefficients anchor side) (lw-polynomial-normalization-count coefficients anchor side coarse)))))
 :hints (("Goal"
  :use (lw-polynomial-square-index-normalize lw-polynomial-normalization-count-data
        lw-polynomial-square-normalize-valid lw-polynomial-normalization-boundary-check
        (:instance lw-polynomial-checked-square-factor-count (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (coarse (lw-polynomial-normalization-count coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-psx-left-commutes lw-psx-left-distributes lw-psx-fold-constants lw-psx-times-negative lw-psx-negative-times lw-psx-zero-times lw-psx-minus-one lw-psx-double-negative lw-psx-add-cancel lw-psx-double lw-psx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-psx-length-natural
 (natp (len points)) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-psx-length-consp
 (equal (consp points) (< 0 (len points)))
 :hints (("Goal" :expand ((len points)) :in-theory (union-theories
 '(fold-consts-in-+ len lw-psx-length-natural endp lw-psx-left-commutes lw-psx-left-distributes lw-psx-fold-constants lw-psx-times-negative lw-psx-negative-times lw-psx-zero-times lw-psx-minus-one lw-psx-double-negative lw-psx-add-cancel lw-psx-double lw-psx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-psx-degree-order
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (<= (len left) (len right)))
  (<= (len (lw-polynomial-without-leading left)) (len (lw-polynomial-without-leading right))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-polynomial-leading-valid (coefficients left))
        (:instance lw-polynomial-leading-valid (coefficients right)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-psx-length-consp lw-psx-length-natural lw-psx-left-commutes lw-psx-left-distributes lw-psx-fold-constants lw-psx-times-negative lw-psx-negative-times lw-psx-zero-times lw-psx-minus-one lw-psx-double-negative lw-psx-add-cancel lw-psx-double lw-psx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-square-index-nonnegative
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse))
  (and (<= 0 (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse)))
       (<= (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse)) (len (lw-polynomial-without-leading (lw-polynomial-trim coefficients))))))
 :hints (("Goal"
  :use (lw-polynomial-square-index-normalize lw-polynomial-normalization-count-data
        lw-polynomial-square-normalize-valid lw-polynomial-normalization-boundary-check lw-polynomial-trim-valid
        (:instance lw-polynomial-checked-square-index-nonnegative (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (coarse (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-polynomial-trim-valid (coefficients (lw-polynomial-square-normalize coefficients anchor side)))
        (:instance lw-psx-degree-order (left (lw-polynomial-trim (lw-polynomial-square-normalize coefficients anchor side))) (right (lw-polynomial-trim coefficients))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-psx-left-commutes lw-psx-left-distributes lw-psx-fold-constants lw-psx-times-negative lw-psx-negative-times lw-psx-zero-times lw-psx-minus-one lw-psx-double-negative lw-psx-add-cancel lw-psx-double lw-psx-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
