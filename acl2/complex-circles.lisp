; Rational circular arcs with exact coordinates and a computed inverse chart.
(in-package "ACL2")
(include-book "unit-circle-charts")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub
 lw-complex-scale lw-complex-diskp lw-diskp lw-complex-norm-square
 lw-phase-rotation lw-phase-denominator)))
(local (defthm lw-ccr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ccr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ccr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ccr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ccr-times-negative (a b) (b a)))
                 :in-theory (disable lw-ccr-times-negative)))))

(local (defthm lw-ccr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ccr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ccr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ccr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ccr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ccr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ccr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ccr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ccr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ccr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ccr-left-commutes)))))
(local (defthm lw-ccr-scale-compose
 (implies (and (rationalp left) (rationalp right) (lw-complexp point))
 (equal (lw-complex-scale left (lw-complex-scale right point))
 (lw-complex-scale (* left right) point)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-scale lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(defun lw-complex-circle-point (center radius sign parameter)
 (lw-complex-add center (lw-complex-scale (* radius sign) (lw-phase-rotation parameter))))
(local (in-theory (disable lw-complex-circle-point)))
(defthm lw-complex-circle-point-rational
 (implies (and (lw-complexp center) (rationalp radius) (rationalp sign) (rationalp parameter))
 (lw-complexp (lw-complex-circle-point center radius sign parameter)))
 :hints (("Goal" :use ((:instance lw-phase-rotation-rational (value parameter)))
 :in-theory (union-theories
 '(lw-complex-circle-point lw-complexp lw-complex-add lw-complex-scale lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(local (defthm lw-ccr-norm-scale
 (implies (and (rationalp factor) (lw-complexp point))
 (equal (lw-complex-norm-square (lw-complex-scale factor point))
 (* factor factor (lw-complex-norm-square point))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-norm-square lw-complex-scale lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-ccr-centered
 (implies (and (lw-complexp center) (rationalp radius) (rationalp sign) (rationalp parameter))
 (equal (lw-complex-sub (lw-complex-circle-point center radius sign parameter) center)
 (lw-complex-scale (* radius sign) (lw-phase-rotation parameter))))
 :hints (("Goal" :use ((:instance lw-phase-rotation-rational (value parameter)))
 :in-theory (union-theories
 '(lw-complex-circle-point lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(defthm lw-complex-circle-point-distance
 (implies (and (lw-complexp center) (rationalp radius) (or (equal sign 1) (equal sign -1)) (rationalp parameter))
 (equal (lw-complex-norm-square (lw-complex-sub (lw-complex-circle-point center radius sign parameter) center)) (* radius radius)))
 :hints (("Goal"
 :use ((:instance lw-phase-rotation-rational (value parameter))
       (:instance lw-cayley-norm-square-one (value parameter)))
 :in-theory (union-theories
 '(lw-ccr-centered lw-ccr-norm-scale lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)))
(defthm lw-complex-circle-point-disk
 (implies (and (lw-complexp center) (rationalp radius) (<= 0 radius) (or (equal sign 1) (equal sign -1)) (rationalp parameter))
 (lw-complex-diskp (lw-complex-sub (lw-complex-circle-point center radius sign parameter) center) radius))
 :hints (("Goal" :use (lw-complex-circle-point-rational lw-complex-circle-point-distance
       (:instance lw-complex-disk-norm-square (point (lw-complex-sub (lw-complex-circle-point center radius sign parameter) center))))
 :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(local (defthm lw-ccr-circle-difference
 (implies (and (lw-complexp center) (rationalp radius) (rationalp sign) (rationalp left) (rationalp right))
 (equal (lw-complex-sub (lw-complex-circle-point center radius sign left) (lw-complex-circle-point center radius sign right))
 (lw-complex-scale (* radius sign) (lw-complex-sub (lw-phase-rotation left) (lw-phase-rotation right)))))
 :hints (("Goal" :use ((:instance lw-phase-rotation-rational (value left)) (:instance lw-phase-rotation-rational (value right)))
 :in-theory (union-theories
 '(lw-complex-circle-point lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(defthm lw-complex-circle-point-lipschitz
 (implies (and (lw-complexp center) (rationalp radius) (<= 0 radius) (or (equal sign 1) (equal sign -1)) (rationalp left) (rationalp right))
 (lw-complex-diskp (lw-complex-sub (lw-complex-circle-point center radius sign left) (lw-complex-circle-point center radius sign right)) (* radius (abs (- left right)))))
 :hints (("Goal"
 :use (lw-phase-rotation-lipschitz
       (:instance lw-complex-scale-disk (factor (* radius sign)) (point (lw-complex-sub (lw-phase-rotation left) (lw-phase-rotation right))) (radius (abs (- left right)))))
 :in-theory (union-theories
 '(lw-ccr-circle-difference abs lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
(defthm lw-complex-circle-chart-reconstruction
 (implies (and (lw-complexp center) (rationalp radius) (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (equal (lw-complex-circle-point center radius (lw-unit-circle-sign point) (lw-unit-circle-parameter point))
 (lw-complex-add center (lw-complex-scale radius point))))
 :hints (("Goal"
 :use (lw-unit-circle-chart-data lw-unit-circle-chart-reconstruction
       (:instance lw-phase-rotation-rational (value (lw-unit-circle-parameter point)))
       (:instance lw-ccr-scale-compose (left radius) (right (lw-unit-circle-sign point)) (point (lw-phase-rotation (lw-unit-circle-parameter point)))))
 :in-theory (union-theories
 '(lw-complex-circle-point lw-ccr-left-commutes lw-ccr-left-distributes lw-ccr-fold-constants lw-ccr-times-negative lw-ccr-negative-times lw-ccr-zero-times lw-ccr-minus-one lw-ccr-double-negative lw-ccr-add-cancel lw-ccr-double lw-ccr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

