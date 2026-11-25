(in-package "ACL2")

(include-book "complex-square-radius")

; Exact rational unit-square membership and distance bounds for z-root.

(local (defthm lw-usc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-usc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-usc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-usc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-usc-times-negative (a b) (b a)))
                 :in-theory (disable lw-usc-times-negative)))))

(local (defthm lw-usc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-usc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-usc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-usc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-usc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-usc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-usc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-usc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-usc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-usc-left-commutes)))))
(defun lw-unit-square-pointp (point)
 (and (lw-complexp point) (equal (lw-complex-square-radius point) 1)))
(defun lw-unit-square-root-gap (root)
 (abs (- 1 (lw-complex-square-radius root))))
(defun lw-unit-square-root-cap (root) (+ 2 (lw-complex-l1 root)))
(defun lw-ray-unit-square-pointsp (points)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) (equal points nil)
  (and (lw-unit-square-pointp (car points)) (lw-ray-unit-square-pointsp (cdr points)))))

(defthm lw-unit-square-point-coordinates
 (equal (lw-unit-square-pointp point)
  (and (lw-complexp point)
       (<= -1 (car point)) (<= (car point) 1) (<= -1 (cdr point)) (<= (cdr point) 1)
       (or (equal (car point) -1) (equal (car point) 1)
           (equal (cdr point) -1) (equal (cdr point) 1))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-complex-square-radius lw-complexp abs max lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-unit-square-point-annulus
 (implies (lw-unit-square-pointp point)
  (and (lw-complex-diskp point 2) (<= 1 (lw-complex-norm-square point))))
 :hints (("Goal"
  :use (lw-complex-square-radius-norm lw-complex-l1-bound
        (:instance lw-complex-disk-enlarge (radius (lw-complex-l1 point)) (cap 2)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-complex-square-radius lw-complex-l1 lw-complexp abs max lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-unit-square-root-gap-data
 (implies (lw-complexp root)
  (and (rationalp (lw-unit-square-root-gap root)) (<= 0 (lw-unit-square-root-gap root))
       (equal (equal (lw-unit-square-root-gap root) 0) (lw-unit-square-pointp root))
       (implies (not (lw-unit-square-pointp root)) (< 0 (lw-unit-square-root-gap root)))))
 :hints (("Goal" :use ((:instance lw-complex-square-radius-data (point root)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-gap lw-unit-square-pointp abs lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-distance-lower
 (implies (and (lw-complexp root) (lw-unit-square-pointp point))
  (<= (* (lw-unit-square-root-gap root) (lw-unit-square-root-gap root))
      (lw-complex-norm-square (lw-complex-sub point root))))
 :hints (("Goal" :use ((:instance lw-complex-square-distance-lower (a point) (b root)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-unit-square-root-gap lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-unit-square-root-cap-bound
 (implies (and (lw-complexp root) (lw-unit-square-pointp point))
  (lw-complex-diskp (lw-complex-sub point root) (lw-unit-square-root-cap root)))
 :hints (("Goal" :use (lw-unit-square-point-annulus
                       (:instance lw-complex-l1-bound (point root))
                       (:instance lw-complex-sub-disk (left point) (radius 2)
                         (right root) (other-radius (lw-complex-l1 root))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-cap lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-usc-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-ray-unit-square-points-data
 (implies (lw-ray-unit-square-pointsp points)
  (and (lw-ray-pointsp points) (lw-ray-annulus-pointsp points 1 2)))
 :hints (("Goal" :induct (lw-ray-unit-square-pointsp points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-unit-square-pointsp) lw-ray-unit-square-pointsp lw-ray-pointsp lw-ray-annulus-pointsp lw-unit-square-point-annulus lw-usc-point-type lw-complex-disk-data endp lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-unit-square-translate-annulus
 (implies (and (lw-complexp root) (lw-ray-unit-square-pointsp points))
  (lw-ray-annulus-pointsp (lw-ray-translate-points root points)
   (lw-unit-square-root-gap root) (lw-unit-square-root-cap root)))
 :hints (("Goal" :induct (lw-ray-unit-square-pointsp points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-unit-square-pointsp) lw-ray-unit-square-pointsp lw-ray-translate-points lw-ray-annulus-pointsp lw-unit-square-distance-lower lw-unit-square-root-cap-bound endp lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-usc-translated-difference
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp root))
  (equal (lw-complex-sub (lw-complex-sub a root) (lw-complex-sub b root))
         (lw-complex-sub a b)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-usc-point-head
 (implies (and (consp points) (lw-ray-pointsp points)) (lw-complexp (car points)))
 :hints (("Goal" :expand ((lw-ray-pointsp points)) :in-theory (union-theories
 '(fold-consts-in-+ endp lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-usc-translated-consp
 (equal (consp (lw-ray-translate-points root points)) (consp points))
 :hints (("Goal" :expand ((lw-ray-translate-points root points)) :in-theory (union-theories
 '(fold-consts-in-+ endp lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-translate-path-step
 (implies (and (lw-complexp root) (lw-ray-pointsp points) (lw-ray-path-step-check points error))
  (lw-ray-path-step-check (lw-ray-translate-points root points) error))
 :hints (("Goal" :induct (lw-ray-translate-points root points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-translate-points) lw-ray-translate-points lw-ray-path-step-check lw-ray-pointsp lw-ray-translate-points-head lw-usc-point-head lw-usc-translated-consp lw-usc-translated-difference endp lw-usc-left-commutes lw-usc-left-distributes lw-usc-fold-constants lw-usc-times-negative lw-usc-negative-times lw-usc-zero-times lw-usc-minus-one lw-usc-double-negative lw-usc-add-cancel lw-usc-double lw-usc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
