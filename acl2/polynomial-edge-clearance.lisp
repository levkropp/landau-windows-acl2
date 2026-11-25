(in-package "ACL2")

(include-book "complex-disk-gap")
(include-book "polynomial-square-path-control")

; A checked polynomial edge supplies its own positive value clearance.

(local (defthm lw-pec-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pec-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pec-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pec-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pec-times-negative (a b) (b a)))
                 :in-theory (disable lw-pec-times-negative)))))

(local (defthm lw-pec-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pec-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pec-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pec-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pec-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pec-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pec-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pec-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pec-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pec-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pec-left-commutes)))))
(defun lw-polynomial-edge-clearance (coefficients left right bound radius)
 (if (lw-polynomial-edge-check coefficients left right bound radius)
  (lw-disk-gap-error (lw-complex-norm-square (lw-complex-polynomial coefficients left 0))
                     (lw-polynomial-edge-cap coefficients bound radius)) 0))

(local (defthm lw-pec-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pec-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-polynomial-checked-edge-cap-data
 (implies (lw-polynomial-edge-check coefficients left right bound radius)
  (and (rationalp (lw-polynomial-edge-cap coefficients bound radius))
       (<= 0 (lw-polynomial-edge-cap coefficients bound radius))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-lipschitz-cap-data)
        (:instance lw-pec-multiply-order (a 0) (b (lw-polynomial-lipschitz-cap coefficients bound)) (factor radius)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-check lw-polynomial-edge-cap lw-pec-product-rational lw-pec-left-commutes lw-pec-left-distributes lw-pec-fold-constants lw-pec-times-negative lw-pec-negative-times lw-pec-zero-times lw-pec-minus-one lw-pec-double-negative lw-pec-add-cancel lw-pec-double lw-pec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-edge-clearance-data
 (implies (lw-polynomial-edge-check coefficients left right bound radius)
  (let ((clearance (lw-polynomial-edge-clearance coefficients left right bound radius)))
   (and (rationalp clearance) (< 0 clearance)
        (not (lw-complex-diskp
          (lw-complex-polynomial coefficients left 0)
          (+ (lw-polynomial-edge-cap coefficients bound radius) clearance))))))
 :hints (("Goal"
  :use (lw-polynomial-checked-edge-cap-data
        (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial coefficients left 0))
          (radius (lw-polynomial-edge-cap coefficients bound radius)))
        (:instance lw-complex-disk-gap-excludes (point (lw-complex-polynomial coefficients left 0))
          (radius (lw-polynomial-edge-cap coefficients bound radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-clearance lw-polynomial-edge-check lw-complex-polynomial-rational lw-pec-left-commutes lw-pec-left-distributes lw-pec-fold-constants lw-pec-times-negative lw-pec-negative-times lw-pec-zero-times lw-pec-minus-one lw-pec-double-negative lw-pec-add-cancel lw-pec-double lw-pec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-edge-excludes-clearance
 (implies (and (lw-polynomial-edge-check coefficients left right bound radius)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
  (not (lw-complex-diskp
   (lw-complex-polynomial coefficients (lw-complex-segment left right parameter) 0)
   (lw-polynomial-edge-clearance coefficients left right bound radius))))
 :hints (("Goal"
  :use (lw-polynomial-checked-edge-cap-data lw-polynomial-edge-clearance-data
        lw-polynomial-edge-sample-variation
        (:instance lw-complex-perturbation-excludes-small
          (left (lw-complex-polynomial coefficients left 0))
          (right (lw-complex-polynomial coefficients (lw-complex-segment left right parameter) 0))
          (epsilon (lw-polynomial-edge-clearance coefficients left right bound radius))
          (delta (lw-polynomial-edge-cap coefficients bound radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-check lw-complex-segment-rational lw-complex-polynomial-rational lw-pec-left-commutes lw-pec-left-distributes lw-pec-fold-constants lw-pec-times-negative lw-pec-negative-times lw-pec-zero-times lw-pec-minus-one lw-pec-double-negative lw-pec-add-cancel lw-pec-double lw-pec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
