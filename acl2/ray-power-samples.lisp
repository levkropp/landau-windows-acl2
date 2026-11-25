(in-package "ACL2")

(include-book "complex-outer-powers")

; Exact power sampling on a common rational path, with uniform annulus
; and step bounds for every exponent through a requested degree.

(local (defthm lw-rpw-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rpw-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rpw-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rpw-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rpw-times-negative (a b) (b a)))
                 :in-theory (disable lw-rpw-times-negative)))))

(local (defthm lw-rpw-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rpw-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rpw-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rpw-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rpw-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rpw-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rpw-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rpw-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpw-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rpw-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rpw-left-commutes)))))

(defun lw-ray-power-points (points index)
 (if (endp points) nil
  (cons (lw-complex-power (car points) index)
        (lw-ray-power-points (cdr points) index))))

(defthm lw-ray-power-points-data
 (implies (lw-ray-pointsp points)
  (and (lw-ray-pointsp (lw-ray-power-points points index))
       (equal (len (lw-ray-power-points points index)) (len points))
       (equal (consp (lw-ray-power-points points index)) (consp points))))
 :hints (("Goal" :induct (lw-ray-power-points points index)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-points lw-ray-pointsp len lw-complex-power-rational lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rpw-head
 (implies (consp points)
  (and (consp (lw-ray-power-points points index))
       (equal (car (lw-ray-power-points points index)) (lw-complex-power (car points) index))
       (equal (cdr (lw-ray-power-points points index)) (lw-ray-power-points (cdr points) index))))
 :hints (("Goal" :expand ((lw-ray-power-points points index))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rpw-path-last
 (equal (lw-ray-path-last (lw-complex-power current index) (lw-ray-power-points points index))
        (lw-complex-power (lw-ray-path-last current points) index))
 :hints (("Goal" :induct (lw-ray-path-last current points)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-points lw-ray-path-last lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-power-points-last
 (implies (consp points)
  (equal (lw-ray-row-last (lw-ray-power-points points index))
         (lw-complex-power (lw-ray-row-last points) index)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-rpw-head lw-rpw-path-last lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rpw-point-bound
 (implies (and (lw-complex-diskp point 2) (<= 1 (lw-complex-norm-square point))
               (natp index) (natp degree) (<= index degree))
  (and (lw-complex-diskp (lw-complex-power point index) (lw-rational-power 2 degree))
       (<= 1 (lw-complex-norm-square (lw-complex-power point index)))))
 :hints (("Goal"
  :use ((:instance lw-complex-power-disk (radius 2))
        (:instance lw-rational-power-monotone-exponent (base 2) (small index) (large degree))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-power point index))
          (radius (lw-rational-power 2 index)) (cap (lw-rational-power 2 degree))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-disk-data lw-rational-power-rational lw-complex-outer-power-norm lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-power-points-annulus
 (implies (and (lw-ray-annulus-pointsp points 1 2)
               (natp index) (natp degree) (<= index degree))
  (lw-ray-annulus-pointsp (lw-ray-power-points points index) 1 (lw-rational-power 2 degree)))
 :hints (("Goal" :induct (lw-ray-power-points points index)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-points lw-ray-annulus-pointsp lw-rpw-point-bound lw-complex-disk-data lw-complex-outer-power-norm lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-path-step-enlarge
 (implies (and (rationalp delta) (rationalp larger) (<= delta larger)
               (lw-ray-path-step-check points delta))
  (lw-ray-path-step-check points larger))
 :hints (("Goal" :induct (lw-ray-path-step-check points delta)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-path-step-check lw-complex-disk-enlarge lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-power-points-step
 (implies (and (lw-ray-annulus-pointsp points 1 2) (natp index)
               (rationalp error) (<= 0 error) (lw-ray-path-step-check points error))
  (lw-ray-path-step-check (lw-ray-power-points points index)
                          (* (lw-rational-power 4 index) error)))
 :hints (("Goal" :induct (lw-ray-path-step-check points error)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-points lw-rpw-head lw-ray-annulus-pointsp lw-ray-annulus-first lw-ray-path-step-check lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-radius-two-power-difference
                    (a (cadr points)) (b (car points))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-first lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-power-points-uniform-step
 (implies (and (lw-ray-annulus-pointsp points 1 2) (natp index) (natp degree) (<= index degree)
               (rationalp error) (<= 0 error) (rationalp delta)
               (lw-ray-path-step-check points error)
               (<= (* (lw-rational-power 4 degree) error) delta))
  (lw-ray-path-step-check (lw-ray-power-points points index) delta))
 :hints (("Goal"
  :use (lw-ray-power-points-step
        (:instance lw-rational-power-monotone-exponent (base 4) (small index) (large degree))
        (:instance lw-rpw-multiply-order
          (a (lw-rational-power 4 index)) (b (lw-rational-power 4 degree)) (factor error))
        (:instance lw-ray-path-step-enlarge
          (points (lw-ray-power-points points index))
          (delta (* (lw-rational-power 4 index) error)) (larger delta)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rational-power-rational lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rpw-power-zero
 (equal (lw-complex-power point 0) (cons 1 0))
 :hints (("Goal" :in-theory (enable lw-complex-power)))))

(local (defthm lw-rpw-zero-halfplane
 (lw-ray-halfplane-points (cons 1 0) (lw-ray-power-points points 0))
 :hints (("Goal" :induct (lw-ray-power-points points 0)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-points lw-rpw-power-zero lw-ray-halfplane-points lw-complex-positive-halfplanep lw-complexp lw-complex-dot lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-power-zero-index
 (equal (lw-ray-polygon-index (lw-ray-power-points points 0)) 0)
 :hints (("Goal"
  :use ((:instance lw-ray-polygon-halfplane-zero
          (h (cons 1 0)) (points (lw-ray-power-points points 0))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rpw-zero-halfplane lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rpw-power-one
 (implies (lw-complexp point) (equal (lw-complex-power point 1) point))
 :hints (("Goal" :expand ((lw-complex-power point 1) (lw-complex-power point 0))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-power lw-complex-mul-one lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-power-one-points
 (implies (lw-ray-pointsp points) (equal (lw-ray-power-points points 1) points))
 :hints (("Goal" :induct (lw-ray-power-points points 1)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-points lw-ray-pointsp lw-rpw-power-one lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-power-points-product
 (implies (and (lw-ray-pointsp points) (natp index))
  (equal (lw-ray-power-points points (+ 1 index))
         (lw-ray-pointwise-products points (lw-ray-power-points points index))))
 :hints (("Goal" :induct (lw-ray-power-points points index)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-power-points lw-ray-pointwise-products lw-ray-pointsp lw-complex-power-rational lw-complex-power-step lw-complex-mul-commutative lw-rpw-left-commutes lw-rpw-left-distributes lw-rpw-fold-constants lw-rpw-times-negative lw-rpw-negative-times lw-rpw-zero-times lw-rpw-minus-one lw-rpw-double-negative lw-rpw-add-cancel lw-rpw-double lw-rpw-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

