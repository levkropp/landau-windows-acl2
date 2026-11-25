(in-package "ACL2")

(include-book "ray-power-index")

; Safety of a power path at any mesh satisfying the common power budget.

(local (defthm lw-rpsf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rpsf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rpsf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rpsf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rpsf-times-negative (a b) (b a)))
                 :in-theory (disable lw-rpsf-times-negative)))))

(local (defthm lw-rpsf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rpsf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rpsf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rpsf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rpsf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rpsf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rpsf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rpsf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpsf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpsf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rpsf-left-commutes)))))
(local (defthm lw-rpsf-delta-small
 (implies (and (rationalp upper) (<= 1 upper) (rationalp delta) (< 0 delta)
               (< (+ (* delta upper) (* delta upper)) 1))
          (< delta 1))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-rpsf-multiply-order (a 1) (b upper) (factor delta)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rpsf-left-commutes lw-rpsf-left-distributes lw-rpsf-fold-constants lw-rpsf-times-negative lw-rpsf-negative-times lw-rpsf-zero-times lw-rpsf-minus-one lw-rpsf-double-negative lw-rpsf-add-cancel lw-rpsf-double lw-rpsf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(local (defthm lw-rpsf-power-head
 (implies (consp points)
  (equal (car (lw-ray-power-points points index)) (lw-complex-power (car points) index)))
 :hints (("Goal" :expand ((lw-ray-power-points points index)) :in-theory (union-theories
 '(fold-consts-in-+ lw-rpsf-left-commutes lw-rpsf-left-distributes lw-rpsf-fold-constants lw-rpsf-times-negative lw-rpsf-negative-times lw-rpsf-zero-times lw-rpsf-minus-one lw-rpsf-double-negative lw-rpsf-add-cancel lw-rpsf-double lw-rpsf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-power-boundary-safe
 (implies (and (consp points) (lw-ray-annulus-pointsp points 1 2)
               (equal (lw-ray-row-last points) (car points)) (natp degree)
               (lw-ray-path-step-check points (lw-ray-power-step-budget degree)))
  (lw-ray-safe-polygonp (lw-ray-power-points points degree)))
 :hints (("Goal"
  :use (lw-ray-power-step-budget-valid
        (:instance lw-rational-power-at-least-one (base 2) (exponent degree))
        (:instance lw-ray-power-points-annulus
          (points points) (index degree))
        (:instance lw-ray-power-points-uniform-step
          (points points)
          (index degree) (error (lw-ray-power-step-budget degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree))))
        (:instance lw-rpsf-delta-small (upper (lw-rational-power 2 degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree))))
        (:instance lw-ray-annulus-closed-polygon-safe
          (points (lw-ray-power-points points degree))
          (lower 1) (upper (lw-rational-power 2 degree))
          (delta (lw-ray-product-step-budget 1 (lw-rational-power 2 degree) 1 (lw-rational-power 2 degree)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-data lw-ray-power-points-data lw-ray-power-points-last lw-rational-power-rational lw-rpsf-power-head lw-rpsf-left-commutes lw-rpsf-left-distributes lw-rpsf-fold-constants lw-rpsf-times-negative lw-rpsf-negative-times lw-rpsf-zero-times lw-rpsf-minus-one lw-rpsf-double-negative lw-rpsf-add-cancel lw-rpsf-double lw-rpsf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
