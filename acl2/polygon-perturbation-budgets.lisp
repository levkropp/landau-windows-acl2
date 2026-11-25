(in-package "ACL2")

(include-book "polygon-perturbation")
(include-book "ray-path-assembly")

; Annulus and adjacent-step estimates generate the homotopy checks.
; The bottom path is closed by repeating its first vertex.

(local (defthm lw-pqb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pqb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pqb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pqb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pqb-times-negative (a b) (b a)))
                 :in-theory (disable lw-pqb-times-negative)))))

(local (defthm lw-pqb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pqb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pqb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pqb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pqb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pqb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pqb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pqb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pqb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pqb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pqb-left-commutes)))))

(local (defthm lw-pqb-zero-difference-disk
 (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius))
  (lw-complex-diskp (lw-complex-sub point point) radius))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(local (defthm lw-pqb-outside
 (implies (and (lw-complexp point) (rationalp lower) (rationalp radius)
               (<= 0 radius) (< radius lower)
               (<= (* lower lower) (lw-complex-norm-square point)))
  (not (lw-complex-diskp point radius)))
 :rule-classes nil
 :hints (("Goal" :use (lw-complex-disk-norm-square)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-ray-annulus-avoids
 (implies (and (lw-ray-annulus-pointsp points lower upper)
               (rationalp lower) (rationalp radius) (<= 0 radius) (< radius lower))
  (lw-ray-row-avoids points radius))
 :hints (("Goal" :induct (lw-ray-annulus-pointsp points lower upper)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-pointsp lw-ray-row-avoids lw-complex-disk-data endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-pqb-outside (point (car points)))) :do-not-induct t))))

(defthm lw-ray-closed-path-step
 (implies (and (consp points) (lw-ray-pointsp points)
               (equal (lw-ray-row-last points) (car points))
               (rationalp delta) (<= 0 delta)
               (lw-ray-path-step-check points delta))
  (lw-ray-path-step-check (lw-ray-close-polygon points) delta))
 :hints (("Goal"
  :use ((:instance lw-ray-path-step-append (left points) (right (list (car points)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-close-polygon lw-ray-step-join-check lw-ray-path-step-check lw-ray-pointsp lw-pqb-zero-difference-disk append endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
   :do-not-induct t)))

(defthm lw-ray-step-self-near
 (implies (and (lw-ray-pointsp points) (rationalp delta) (<= 0 delta)
               (lw-ray-path-step-check points delta))
  (lw-ray-row-near-check points points delta))
 :hints (("Goal" :induct (lw-ray-path-step-check points delta)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-path-step-check) lw-ray-path-step-check lw-ray-row-near-check lw-ray-pointsp lw-pqb-zero-difference-disk endp lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-annulus-pointwise-perturbation
 (implies (and (consp bottom) (lw-ray-annulus-pointsp bottom lower upper)
               (equal (lw-ray-row-last bottom) (car bottom))
               (lw-ray-path-step-check bottom beta)
               (lw-ray-pointwise-nearp bottom top delta)
               (rationalp lower) (rationalp beta) (<= 0 beta)
               (rationalp delta) (<= 0 delta) (< 0 (+ beta delta)) (< (+ beta delta) lower))
  (equal (lw-ray-polygon-index bottom) (lw-ray-polygon-index top)))
 :hints (("Goal"
  :use ((:instance lw-ray-annulus-data (points bottom))
        (:instance lw-ray-annulus-avoids (points bottom) (radius (+ beta delta)))
        (:instance lw-ray-closed-path-step (points bottom) (delta beta))
        (:instance lw-ray-step-self-near (points (lw-ray-close-polygon bottom)) (delta beta))
        (:instance lw-ray-close-polygon-data (points bottom))
        (:instance lw-ray-polygon-pointwise-perturbation))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pqb-left-commutes lw-pqb-left-distributes lw-pqb-fold-constants lw-pqb-times-negative lw-pqb-negative-times lw-pqb-zero-times lw-pqb-minus-one lw-pqb-double-negative lw-pqb-add-cancel lw-pqb-double lw-pqb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
