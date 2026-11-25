; Circle containment and exact rational chart/orbit geometry.
(in-package "ACL2")
(include-book "square-cells")
(include-book "box-circles")
(include-book "complex-circles")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-add lw-complex-scale
 lw-complex-diskp lw-complex-norm-square lw-distance-squared lw-square-containsp
 lw-complex-circle-point lw-complex-power lw-cauchy-orbit-rotation)))
(local (defthm lw-scg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-scg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-scg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-scg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-scg-times-negative (a b) (b a)))
                 :in-theory (disable lw-scg-times-negative)))))

(local (defthm lw-scg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-scg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-scg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-scg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-scg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-scg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-scg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-scg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-scg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-scg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-scg-left-commutes)))))
(defun lw-circle-pointp (center radius point)
 (and (lw-complexp center) (lw-complexp point) (rationalp radius) (< 0 radius)
      (equal (lw-distance-squared (car center) (cdr center) point) (* radius radius))))
(defun lw-circle-contained-in-squarep (anchor side center radius)
 (and (lw-complexp anchor) (rationalp side) (< 0 side)
      (lw-complexp center) (rationalp radius) (< 0 radius)
      (<= (car anchor) (- (car center) radius))
      (<= (+ (car center) radius) (+ (car anchor) side))
      (<= (cdr anchor) (- (cdr center) radius))
      (<= (+ (cdr center) radius) (+ (cdr anchor) side))))
(defun lw-cauchy-circle-point (center radius degree sample)
 (lw-complex-add center
 (lw-complex-scale radius (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))
(local (in-theory (disable lw-circle-pointp lw-circle-contained-in-squarep lw-cauchy-circle-point)))

(defthm lw-distance-squared-as-complex-norm
 (implies (and (lw-complexp center) (lw-complexp point))
 (equal (lw-distance-squared (car center) (cdr center) point)
        (lw-complex-norm-square (lw-complex-sub point center))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-distance-squared lw-complex-norm-square lw-complex-sub lw-complexp lw-scg-left-commutes lw-scg-left-distributes lw-scg-fold-constants lw-scg-times-negative lw-scg-negative-times lw-scg-zero-times lw-scg-minus-one lw-scg-double-negative lw-scg-add-cancel lw-scg-double lw-scg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-circle-point-in-disk
 (implies (lw-circle-pointp center radius point)
 (lw-complex-diskp (lw-complex-sub point center) radius))
 :hints (("Goal"
 :use (lw-distance-squared-as-complex-norm
       (:instance lw-complex-disk-norm-square (point (lw-complex-sub point center))))
 :in-theory (union-theories
 '(lw-circle-pointp lw-complex-sub lw-complexp lw-scg-left-commutes lw-scg-left-distributes lw-scg-fold-constants lw-scg-times-negative lw-scg-negative-times lw-scg-zero-times lw-scg-minus-one lw-scg-double-negative lw-scg-add-cancel lw-scg-double lw-scg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-circle-disk-in-square
 (implies (and (lw-circle-contained-in-squarep anchor side center radius)
               (lw-complexp point)
               (lw-complex-diskp (lw-complex-sub point center) radius))
 (lw-square-containsp anchor side point))
 :hints (("Goal" :use ((:instance lw-complex-disk-coordinates (point (lw-complex-sub point center))))
 :in-theory (union-theories
 '(lw-circle-contained-in-squarep lw-square-containsp lw-complex-sub lw-complexp abs lw-scg-left-commutes lw-scg-left-distributes lw-scg-fold-constants lw-scg-times-negative lw-scg-negative-times lw-scg-zero-times lw-scg-minus-one lw-scg-double-negative lw-scg-add-cancel lw-scg-double lw-scg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-circle-point-in-square
 (implies (and (lw-circle-contained-in-squarep anchor side center radius)
               (lw-circle-pointp center radius point))
 (lw-square-containsp anchor side point))
 :hints (("Goal" :use (lw-circle-point-in-disk lw-circle-disk-in-square)
 :in-theory (union-theories
 '(lw-circle-pointp lw-scg-left-commutes lw-scg-left-distributes lw-scg-fold-constants lw-scg-times-negative lw-scg-negative-times lw-scg-zero-times lw-scg-minus-one lw-scg-double-negative lw-scg-add-cancel lw-scg-double lw-scg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-circle-chart-point
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius)
               (or (equal sign 1) (equal sign -1)) (rationalp parameter))
 (lw-circle-pointp center radius (lw-complex-circle-point center radius sign parameter)))
 :hints (("Goal"
 :use (lw-complex-circle-point-rational lw-complex-circle-point-distance
       (:instance lw-distance-squared-as-complex-norm
        (point (lw-complex-circle-point center radius sign parameter))))
 :in-theory (union-theories
 '(lw-circle-pointp lw-scg-left-commutes lw-scg-left-distributes lw-scg-fold-constants lw-scg-times-negative lw-scg-negative-times lw-scg-zero-times lw-scg-minus-one lw-scg-double-negative lw-scg-add-cancel lw-scg-double lw-scg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-scg-scaled-unit-circle
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius)
               (lw-complexp unit) (equal (lw-complex-norm-square unit) 1))
 (lw-circle-pointp center radius (lw-complex-add center (lw-complex-scale radius unit))))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-circle-pointp lw-distance-squared lw-complex-add lw-complex-scale lw-complexp lw-complex-norm-square lw-scg-left-commutes lw-scg-left-distributes lw-scg-fold-constants lw-scg-times-negative lw-scg-negative-times lw-scg-zero-times lw-scg-minus-one lw-scg-double-negative lw-scg-add-cancel lw-scg-double lw-scg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)) :rule-classes nil))

(defthm lw-cauchy-circle-point-on-circle
 (implies (and (lw-complexp center) (rationalp radius) (< 0 radius)
               (natp degree) (natp sample))
 (lw-circle-pointp center radius (lw-cauchy-circle-point center radius degree sample)))
 :hints (("Goal"
 :use (lw-cauchy-orbit-data
       (:instance lw-cauchy-orbit-power-norm-one (index sample))
       (:instance lw-complex-power-rational (point (lw-cauchy-orbit-rotation degree)) (index sample))
       (:instance lw-scg-scaled-unit-circle (unit (lw-complex-power (lw-cauchy-orbit-rotation degree) sample))))
 :in-theory (union-theories
 '(lw-cauchy-circle-point lw-scg-left-commutes lw-scg-left-distributes lw-scg-fold-constants lw-scg-times-negative lw-scg-negative-times lw-scg-zero-times lw-scg-minus-one lw-scg-double-negative lw-scg-add-cancel lw-scg-double lw-scg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

