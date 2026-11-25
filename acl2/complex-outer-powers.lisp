(in-package "ACL2")

(include-book "polygon-product-additivity")
(include-book "cauchy-resolvents")

; Explicit rational power bounds on the radius-two disk. The loose
; difference cap 4^k*error is monotone in k and suits one common mesh.

(local (defthm lw-cop-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cop-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cop-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cop-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cop-times-negative (a b) (b a)))
                 :in-theory (disable lw-cop-times-negative)))))

(local (defthm lw-cop-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cop-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cop-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cop-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cop-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cop-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cop-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cop-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cop-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cop-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cop-left-commutes)))))

(local (defthm lw-cop-norm-one
 (equal (lw-complex-norm-square (cons 1 0)) 1)
 :hints (("Goal" :in-theory (enable lw-complex-norm-square)))))

(local (defthm lw-cop-power-zero
 (implies (zp index) (equal (lw-rational-power base index) 1))
 :hints (("Goal" :expand ((lw-rational-power base index))))))

(local (defthm lw-cop-complex-zero-power
 (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))
 :hints (("Goal" :expand ((lw-complex-power point index))))))

(defthm lw-complex-power-norm-square
 (implies (and (lw-complexp point) (natp index))
  (equal (lw-complex-norm-square (lw-complex-power point index))
         (lw-rational-power (lw-complex-norm-square point) index)))
 :hints (("Goal" :induct (lw-complex-power point index)
          :expand ((lw-complex-power point index)
                   (lw-rational-power (lw-complex-norm-square point) index))
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-complex-power) lw-complex-power-rational lw-complex-norm-square-product lw-cop-norm-one lw-cop-power-zero lw-cop-complex-zero-power lw-cop-left-commutes lw-cop-left-distributes lw-cop-fold-constants lw-cop-times-negative lw-cop-negative-times lw-cop-zero-times lw-cop-minus-one lw-cop-double-negative lw-cop-add-cancel lw-cop-double lw-cop-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-complex-outer-power-norm
 (implies (and (lw-complexp point) (<= 1 (lw-complex-norm-square point)) (natp index))
          (<= 1 (lw-complex-norm-square (lw-complex-power point index))))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-valid)
        (:instance lw-rational-power-at-least-one (base (lw-complex-norm-square point)) (exponent index)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-power-norm-square lw-cop-left-commutes lw-cop-left-distributes lw-cop-fold-constants lw-cop-times-negative lw-cop-negative-times lw-cop-zero-times lw-cop-minus-one lw-cop-double-negative lw-cop-add-cancel lw-cop-double lw-cop-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-cop-difference-algebra
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp p) (lw-complexp q))
  (equal (lw-complex-sub (lw-complex-mul a p) (lw-complex-mul b q))
   (lw-complex-add (lw-complex-mul a (lw-complex-sub p q))
                   (lw-complex-mul (lw-complex-sub a b) q))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-cop-left-commutes lw-cop-left-distributes lw-cop-fold-constants lw-cop-times-negative lw-cop-negative-times lw-cop-zero-times lw-cop-minus-one lw-cop-double-negative lw-cop-add-cancel lw-cop-double lw-cop-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cop-difference-step
 (implies (and (lw-complexp a) (lw-complexp b) (posp index))
  (equal (lw-complex-sub (lw-complex-power a index) (lw-complex-power b index))
   (lw-complex-add
    (lw-complex-mul a (lw-complex-sub (lw-complex-power a (- index 1)) (lw-complex-power b (- index 1))))
    (lw-complex-mul (lw-complex-sub a b) (lw-complex-power b (- index 1))))))
 :hints (("Goal" :expand ((lw-complex-power a index) (lw-complex-power b index))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-cop-difference-algebra lw-complex-power-rational lw-cop-left-commutes lw-cop-left-distributes lw-cop-fold-constants lw-cop-times-negative lw-cop-negative-times lw-cop-zero-times lw-cop-minus-one lw-cop-double-negative lw-cop-add-cancel lw-cop-double lw-cop-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cop-power-step
 (implies (posp index)
  (equal (lw-rational-power base index) (* base (lw-rational-power base (- index 1)))))
 :hints (("Goal" :expand ((lw-rational-power base index))))))





(local (defthm lw-cop-zero-disk
 (implies (and (rationalp error) (<= 0 error))
  (lw-complex-diskp (lw-complex-sub (cons 1 0) (cons 1 0)) error))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-sub lw-complex-diskp lw-complexp lw-diskp lw-cop-left-commutes lw-cop-left-distributes lw-cop-fold-constants lw-cop-times-negative lw-cop-negative-times lw-cop-zero-times lw-cop-minus-one lw-cop-double-negative lw-cop-add-cancel lw-cop-double lw-cop-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cop-error-budget
 (implies (and (rationalp error) (<= 0 error)
               (rationalp small) (<= 0 small) (rationalp large) (<= small large))
  (<= (+ (* 2 large error) (* small error)) (* 4 large error)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-radius-two-power-difference
 (implies (and (lw-complex-diskp a 2) (lw-complex-diskp b 2)
               (lw-complex-diskp (lw-complex-sub a b) error) (natp index))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-power a index) (lw-complex-power b index))
   (* (lw-rational-power 4 index) error)))
 :hints (("Goal" :induct (lw-complex-power a index)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-complex-power) lw-complex-disk-data lw-cop-power-zero lw-cop-complex-zero-power lw-cop-zero-disk lw-cop-left-commutes lw-cop-left-distributes lw-cop-fold-constants lw-cop-times-negative lw-cop-negative-times lw-cop-zero-times lw-cop-minus-one lw-cop-double-negative lw-cop-add-cancel lw-cop-double lw-cop-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-power-disk (point b) (radius 2) (index (- index 1)))
                  (:instance lw-complex-mul-disk
                    (left a) (radius 2)
                    (right (lw-complex-sub (lw-complex-power a (- index 1)) (lw-complex-power b (- index 1))))
                    (other-radius (* (lw-rational-power 4 (- index 1)) error)))
                  (:instance lw-complex-mul-disk
                    (left (lw-complex-sub a b)) (radius error)
                    (right (lw-complex-power b (- index 1))) (other-radius (lw-rational-power 2 (- index 1))))
                  (:instance lw-complex-add-disk
                    (left (lw-complex-mul a
                      (lw-complex-sub (lw-complex-power a (- index 1)) (lw-complex-power b (- index 1)))))
                    (right (lw-complex-mul (lw-complex-sub a b) (lw-complex-power b (- index 1))))
                    (radius (* 2 (lw-rational-power 4 (- index 1)) error))
                    (other-radius (* error (lw-rational-power 2 (- index 1)))))
                  (:instance lw-rational-power-monotone-base
                    (left 2) (right 4) (exponent (- index 1)))
                  (:instance lw-cop-error-budget
                    (small (lw-rational-power 2 (- index 1))) (large (lw-rational-power 4 (- index 1))))
                  (:instance lw-complex-disk-enlarge
                    (point (lw-complex-sub (lw-complex-power a index) (lw-complex-power b index)))
                    (radius (+ (* 2 (lw-rational-power 4 (- index 1)) error)
                               (* error (lw-rational-power 2 (- index 1)))))
                    (cap (* (lw-rational-power 4 index) error))))
             :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-disk-data lw-rational-power-rational lw-rational-power-nonnegative lw-cop-power-step lw-cop-difference-step lw-cop-left-commutes lw-cop-left-distributes lw-cop-fold-constants lw-cop-times-negative lw-cop-negative-times lw-cop-zero-times lw-cop-minus-one lw-cop-double-negative lw-cop-add-cancel lw-cop-double lw-cop-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
             :do-not-induct t))))

