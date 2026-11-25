; Read bounded coefficients and compare padded polynomial differences.
(in-package "ACL2")
(include-book "polynomial-quadratic-bounds")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub
 lw-complex-diskp lw-polynomial-coefficient-caps lw-complex-coefficient-at
 lw-polynomial-disk-difference lw-polynomial-rescale lw-rational-power)))
(local (defthm lw-pcc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcc-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcc-times-negative)))))

(local (defthm lw-pcc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcc-left-commutes)))))
(defthm lw-polynomial-capped-coefficient-at
 (implies (and (lw-complex-coefficientsp coefficients)
 (lw-polynomial-coefficient-caps coefficients cap) (rationalp cap) (<= 0 cap)
 (natp target) (natp offset))
 (lw-complex-diskp (lw-complex-coefficient-at coefficients target offset) cap))
 :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
 :in-theory (union-theories
 '(lw-complex-coefficient-at lw-complex-coefficientsp lw-polynomial-coefficient-caps lw-complex-coefficient-at-below-offset lw-complex-coefficient-at-rational lw-complex-add-zero lw-complex-zero-disk endp lw-pcc-left-commutes lw-pcc-left-distributes lw-pcc-fold-constants lw-pcc-times-negative lw-pcc-negative-times lw-pcc-zero-times lw-pcc-minus-one lw-pcc-double-negative lw-pcc-add-cancel lw-pcc-double lw-pcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-polynomial-capped-nth
 (implies (and (lw-complex-coefficientsp coefficients)
 (lw-polynomial-coefficient-caps coefficients cap) (rationalp cap) (<= 0 cap)
 (natp index) (< index (len coefficients)))
 (lw-complex-diskp (nth index coefficients) cap))
 :hints (("Goal"
 :use ((:instance lw-polynomial-capped-coefficient-at (target index) (offset 0))
       (:instance lw-complex-coefficient-at-nth (target index) (offset 0)))
 :in-theory (union-theories
 '( lw-pcc-left-commutes lw-pcc-left-distributes lw-pcc-fold-constants lw-pcc-times-negative lw-pcc-negative-times lw-pcc-zero-times lw-pcc-minus-one lw-pcc-double-negative lw-pcc-add-cancel lw-pcc-double lw-pcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-polynomial-disk-difference-capped-coefficient
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right)
 (rationalp radius) (natp count) (<= (len left) count) (<= (len right) count)
 (lw-polynomial-coefficient-caps (lw-polynomial-disk-difference left right radius count) cap)
 (rationalp cap) (<= 0 cap) (natp index))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-coefficient-at (lw-polynomial-rescale left radius 0) index 0)
                  (lw-complex-coefficient-at (lw-polynomial-rescale right radius 0) index 0)) cap))
 :hints (("Goal" :cases ((< index count))
 :use (lw-polynomial-disk-difference-valid
       (:instance lw-polynomial-rescale-valid (coefficients left) (factor radius) (offset 0))
       (:instance lw-polynomial-rescale-valid (coefficients right) (factor radius) (offset 0))
       lw-polynomial-disk-difference-coefficient
       (:instance lw-polynomial-capped-nth (coefficients (lw-polynomial-disk-difference left right radius count)))
       (:instance lw-complex-coefficient-at-outside (coefficients (lw-polynomial-rescale left radius 0)) (target index) (offset 0))
       (:instance lw-complex-coefficient-at-outside (coefficients (lw-polynomial-rescale right radius 0)) (target index) (offset 0))
       (:instance lw-complex-zero-disk (radius cap)))
 :in-theory (union-theories
 '(lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-pcc-left-commutes lw-pcc-left-distributes lw-pcc-fold-constants lw-pcc-times-negative lw-pcc-negative-times lw-pcc-zero-times lw-pcc-minus-one lw-pcc-double-negative lw-pcc-add-cancel lw-pcc-double lw-pcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
