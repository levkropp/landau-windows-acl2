(in-package "ACL2")

(include-book "polynomial-prefix-bounds")

; Geometric coefficient tails on every strict inner disk.
; The finite cap is amplified by the computed gain 1/(1-radius).

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-horner lw-complex-coefficient-at
          lw-polynomial-pad lw-polynomial-drop lw-polynomial-coefficient-caps
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes
          lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-pgb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pgb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pgb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pgb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pgb-times-negative (a b) (b a)))
                 :in-theory (disable lw-pgb-times-negative)))))

(local (defthm lw-pgb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pgb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pgb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pgb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pgb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pgb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pgb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pgb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pgb-left-commutes)))))

(local (defthm lw-pgb-reciprocal-positive
 (implies (and (rationalp x) (< 0 x)) (and (rationalp (/ x)) (< 0 (/ x))))
 :hints (("Goal" :use ((:instance inverse-of-* (x x))) :nonlinearp t))
 :rule-classes nil))

(defun lw-geometric-disk-gain (radius) (/ (- 1 radius)))

(local (in-theory (disable lw-geometric-disk-gain)))

(defthm lw-geometric-disk-gain-data
 (implies (and (rationalp radius) (<= 0 radius) (< radius 1))
  (and (rationalp (lw-geometric-disk-gain radius)) (< 0 (lw-geometric-disk-gain radius)) (<= 1 (lw-geometric-disk-gain radius))
       (equal (* (- 1 radius) (lw-geometric-disk-gain radius)) 1)))
 :hints (("Goal"
  :use ((:instance lw-pgb-reciprocal-positive (x (- 1 radius)))
        (:instance inverse-of-* (x (- 1 radius))))
  :in-theory (union-theories
   '(lw-geometric-disk-gain lw-pgb-left-commutes lw-pgb-left-distributes lw-pgb-fold-constants lw-pgb-times-negative lw-pgb-negative-times lw-pgb-zero-times lw-pgb-minus-one lw-pgb-double-negative lw-pgb-add-cancel lw-pgb-double lw-pgb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-pgb-power-step
 (implies (and (rationalp radius) (natp offset))
  (equal (lw-rational-power radius (+ 1 offset)) (* radius (lw-rational-power radius offset))))
 :hints (("Goal" :expand ((lw-rational-power radius (+ 1 offset))) :in-theory (union-theories
   '( lw-pgb-left-commutes lw-pgb-left-distributes lw-pgb-fold-constants lw-pgb-times-negative lw-pgb-negative-times lw-pgb-zero-times lw-pgb-minus-one lw-pgb-double-negative lw-pgb-add-cancel lw-pgb-double lw-pgb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-pgb-geometric-budget
 (implies (and (rationalp radius) (<= 0 radius) (< radius 1)
               (rationalp cap) (<= 0 cap) (rationalp weight) (<= 0 weight))
  (and (<= 0 (* cap (lw-geometric-disk-gain radius) weight))
       (equal (+ (* cap weight) (* cap (lw-geometric-disk-gain radius) radius weight)) (* cap (lw-geometric-disk-gain radius) weight))))
 :hints (("Goal"
  :use (lw-geometric-disk-gain-data
        (:instance lw-pgb-inverse-factor (divisor (- 1 radius)) (coefficient (* cap weight))))
  :in-theory (union-theories
   '(lw-geometric-disk-gain lw-pgb-left-commutes lw-pgb-left-distributes lw-pgb-fold-constants lw-pgb-times-negative lw-pgb-negative-times lw-pgb-zero-times lw-pgb-minus-one lw-pgb-double-negative lw-pgb-add-cancel lw-pgb-double lw-pgb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-polynomial-geometric-tail-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-polynomial-coefficient-caps coefficients cap)
               (rationalp cap) (<= 0 cap) (lw-complex-diskp point radius) (< radius 1) (natp offset))
  (lw-complex-diskp (lw-complex-polynomial coefficients point offset) (* cap (lw-geometric-disk-gain radius) (lw-rational-power radius offset))))
 :hints (("Goal" :induct (lw-complex-polynomial coefficients point offset)
  :in-theory (union-theories
   '(lw-complex-polynomial lw-polynomial-coefficient-caps lw-complex-coefficientsp lw-pgb-power-step endp lw-pgb-left-commutes lw-pgb-left-distributes lw-pgb-fold-constants lw-pgb-times-negative lw-pgb-negative-times lw-pgb-zero-times lw-pgb-minus-one lw-pgb-double-negative lw-pgb-add-cancel lw-pgb-double lw-pgb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)) )
 (and stable-under-simplificationp
  '(:use ((:instance lw-complex-disk-data)
          (:instance lw-geometric-disk-gain-data)
          (:instance lw-rational-power-rational (base radius) (exponent offset))
          (:instance lw-rational-power-nonnegative (base radius) (exponent offset))
          (:instance lw-complex-power-disk (index offset))
          (:instance lw-complex-mul-disk (left (car coefficients)) (right (lw-complex-power point offset))
           (radius cap) (other-radius (lw-rational-power radius offset)))
          (:instance lw-complex-add-disk
           (left (lw-complex-mul (car coefficients) (lw-complex-power point offset)))
           (right (lw-complex-polynomial (cdr coefficients) point (+ 1 offset)))
           (radius (* cap (lw-rational-power radius offset))) (other-radius (* cap (lw-geometric-disk-gain radius) (lw-rational-power radius (+ 1 offset)))))
          (:instance lw-pgb-geometric-budget (weight (lw-rational-power radius offset)))
          (:instance lw-complex-zero-disk (radius (* cap (lw-geometric-disk-gain radius) (lw-rational-power radius offset)))))
    :in-theory (union-theories
   '(lw-complex-polynomial lw-polynomial-coefficient-caps lw-complex-coefficientsp lw-pgb-power-step endp lw-pgb-left-commutes lw-pgb-left-distributes lw-pgb-fold-constants lw-pgb-times-negative lw-pgb-negative-times lw-pgb-zero-times lw-pgb-minus-one lw-pgb-double-negative lw-pgb-add-cancel lw-pgb-double lw-pgb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
    :nonlinearp nil :do-not-induct t))))

(defthm lw-complex-polynomial-geometric-prefix-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-polynomial-coefficient-caps coefficients cap)
               (rationalp cap) (<= 0 cap) (natp count) (lw-complex-diskp point radius) (< radius 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                   (lw-complex-polynomial (lw-polynomial-pad coefficients count) point 0))
   (* cap (lw-geometric-disk-gain radius) (lw-rational-power radius count))))
 :hints (("Goal"
  :use (lw-polynomial-drop-valid lw-complex-disk-data
        (:instance lw-polynomial-prefix-tail-identity (offset 0))
        (:instance lw-complex-polynomial-geometric-tail-bound
         (coefficients (lw-polynomial-drop coefficients count)) (offset count)))
  :in-theory (union-theories
   '( lw-pgb-left-commutes lw-pgb-left-distributes lw-pgb-fold-constants lw-pgb-times-negative lw-pgb-negative-times lw-pgb-zero-times lw-pgb-minus-one lw-pgb-double-negative lw-pgb-add-cancel lw-pgb-double lw-pgb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

