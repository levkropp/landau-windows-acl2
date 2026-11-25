(in-package "ACL2")

(include-book "ray-power-safety")

; Bounds and closure for multiplication of a path by one fixed complex number.

(local (defthm lw-rmb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rmb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rmb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rmb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rmb-times-negative (a b) (b a)))
                 :in-theory (disable lw-rmb-times-negative)))))

(local (defthm lw-rmb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rmb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rmb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rmb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rmb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rmb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rmb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rmb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rmb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rmb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rmb-left-commutes)))))
(local (defthm lw-rmb-product-norm-lower
 (implies (and (lw-complexp a) (lw-complexp b)
               (rationalp lower-left) (< 0 lower-left)
               (rationalp lower-right) (< 0 lower-right)
               (<= (* lower-left lower-left) (lw-complex-norm-square a))
               (<= (* lower-right lower-right) (lw-complex-norm-square b)))
  (<= (* lower-left lower-right lower-left lower-right)
      (lw-complex-norm-square (lw-complex-mul a b))))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-valid (point a))
        (:instance lw-complex-norm-square-valid (point b))
        (:instance lw-rmb-multiply-order
          (a (* lower-left lower-left)) (b (lw-complex-norm-square a))
          (factor (lw-complex-norm-square b)))
        (:instance lw-rmb-multiply-order
          (a (* lower-right lower-right)) (b (lw-complex-norm-square b))
          (factor (* lower-left lower-left))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-norm-square-product lw-rmb-left-commutes lw-rmb-left-distributes lw-rmb-fold-constants lw-rmb-times-negative lw-rmb-negative-times lw-rmb-zero-times lw-rmb-minus-one lw-rmb-double-negative lw-rmb-add-cancel lw-rmb-double lw-rmb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t)) :rule-classes nil))


(defthm lw-ray-multiplier-annulus
 (implies (and (lw-complex-diskp factor cap)
               (rationalp lower) (< 0 lower)
               (<= (* lower lower) (lw-complex-norm-square factor))
               (lw-ray-annulus-pointsp points 1 upper))
  (lw-ray-annulus-pointsp (lw-ray-multiply-points factor points) lower (* cap upper)))
 :hints (("Goal" :induct (lw-ray-multiply-points factor points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-multiply-points) lw-ray-multiply-points lw-ray-annulus-pointsp lw-complex-disk-data endp lw-rmb-left-commutes lw-rmb-left-distributes lw-rmb-fold-constants lw-rmb-times-negative lw-rmb-negative-times lw-rmb-zero-times lw-rmb-minus-one lw-rmb-double-negative lw-rmb-add-cancel lw-rmb-double lw-rmb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-rmb-product-norm-lower
                     (a factor) (b (car points)) (lower-left lower) (lower-right 1))
                  (:instance lw-complex-mul-disk
                     (left factor) (radius cap) (right (car points)) (other-radius upper)))
            :do-not-induct t))))

(local (defthm lw-rmb-head
 (implies (consp points)
  (equal (car (lw-ray-multiply-points factor points)) (lw-complex-mul factor (car points))))
 :hints (("Goal" :expand ((lw-ray-multiply-points factor points)) :in-theory (union-theories
 '(fold-consts-in-+ lw-rmb-left-commutes lw-rmb-left-distributes lw-rmb-fold-constants lw-rmb-times-negative lw-rmb-negative-times lw-rmb-zero-times lw-rmb-minus-one lw-rmb-double-negative lw-rmb-add-cancel lw-rmb-double lw-rmb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rmb-consp
 (equal (consp (lw-ray-multiply-points factor points)) (consp points))
 :hints (("Goal" :expand ((lw-ray-multiply-points factor points)) :in-theory (union-theories
 '(fold-consts-in-+ endp lw-rmb-left-commutes lw-rmb-left-distributes lw-rmb-fold-constants lw-rmb-times-negative lw-rmb-negative-times lw-rmb-zero-times lw-rmb-minus-one lw-rmb-double-negative lw-rmb-add-cancel lw-rmb-double lw-rmb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rmb-point-head
 (implies (and (consp points) (lw-ray-pointsp points)) (lw-complexp (car points)))
 :hints (("Goal" :expand ((lw-ray-pointsp points)) :in-theory (union-theories
 '(endp lw-rmb-left-commutes lw-rmb-left-distributes lw-rmb-fold-constants lw-rmb-times-negative lw-rmb-negative-times lw-rmb-zero-times lw-rmb-minus-one lw-rmb-double-negative lw-rmb-add-cancel lw-rmb-double lw-rmb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-multiplier-step
 (implies (and (lw-complex-diskp factor cap) (lw-ray-pointsp points)
               (lw-ray-path-step-check points error))
  (lw-ray-path-step-check (lw-ray-multiply-points factor points) (* cap error)))
 :hints (("Goal" :induct (lw-ray-multiply-points factor points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-multiply-points) lw-ray-multiply-points lw-ray-path-step-check lw-ray-pointsp lw-complex-disk-data lw-complex-mul-subtract lw-rmb-head lw-rmb-consp lw-rmb-point-head endp lw-rmb-left-commutes lw-rmb-left-distributes lw-rmb-fold-constants lw-rmb-times-negative lw-rmb-negative-times lw-rmb-zero-times lw-rmb-minus-one lw-rmb-double-negative lw-rmb-add-cancel lw-rmb-double lw-rmb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-mul-disk
                   (left factor) (radius cap)
                   (right (lw-complex-sub (cadr points) (car points))) (other-radius error)))
            :do-not-induct t))))

(defthm lw-ray-multiplier-closed
 (implies (and (consp points) (equal (lw-ray-row-last points) (car points)))
  (equal (lw-ray-row-last (lw-ray-multiply-points factor points))
         (car (lw-ray-multiply-points factor points))))
 :hints (("Goal" :expand ((lw-ray-multiply-points factor points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-ray-multiply-points-last lw-rmb-left-commutes lw-rmb-left-distributes lw-rmb-fold-constants lw-rmb-times-negative lw-rmb-negative-times lw-rmb-zero-times lw-rmb-minus-one lw-rmb-double-negative lw-rmb-add-cancel lw-rmb-double lw-rmb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
