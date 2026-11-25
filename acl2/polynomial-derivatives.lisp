(in-package "ACL2")

(include-book "polynomial-affine")
(include-book "polynomial-quadratic-bounds")

; Formal finite polynomial derivatives and first affine coefficients.
; These identities will connect the actual Euler polynomial to weighted sums.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
          lw-complex-polynomial lw-complex-polynomial-horner lw-complex-coefficient-at
          lw-polynomial-affine lw-polynomial-add-constant lw-polynomial-multiply-linear
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes)))

(local (defthm lw-pdv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pdv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pdv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pdv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pdv-times-negative (a b) (b a)))
                 :in-theory (disable lw-pdv-times-negative)))))

(local (defthm lw-pdv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pdv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pdv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pdv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pdv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pdv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pdv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pdv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pdv-left-commutes)))))

(local (defthm lw-pdv-nil-coefficient
 (equal (lw-complex-coefficient-at nil target offset) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-coefficient-at)))))

(local (defthm lw-pdv-first-coefficient
 (implies (and (lw-complex-coefficientsp coefficients) (natp offset))
  (equal (lw-complex-coefficient-at coefficients offset offset)
         (if (consp coefficients) (car coefficients) (cons 0 0))))
 :hints (("Goal"
  :use ((:instance lw-complex-coefficient-at-below-offset
         (coefficients (cdr coefficients)) (target offset) (offset (+ 1 offset))))
  :expand ((lw-complex-coefficient-at coefficients offset offset))
  :in-theory (union-theories
   '(lw-pdv-nil-coefficient lw-complex-coefficientsp lw-complex-add-zero lw-complexp endp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-pdv-second-coefficient
 (implies (lw-complex-coefficientsp coefficients)
  (equal (lw-complex-coefficient-at coefficients 1 0)
         (if (consp (cdr coefficients)) (cadr coefficients) (cons 0 0))))
 :hints (("Goal"
  :use ((:instance lw-pdv-first-coefficient (coefficients (cdr coefficients)) (offset 1))
        (:instance lw-complex-coefficient-at-rational (coefficients (cdr coefficients)) (target 1) (offset 1)))
  :expand ((lw-complex-coefficient-at coefficients 1 0))
  :in-theory (union-theories
   '(lw-pdv-nil-coefficient lw-complex-coefficientsp lw-complex-add-zero lw-complexp endp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-pdv-one-step
 (implies (lw-complex-coefficientsp coefficients)
  (equal (lw-complex-coefficient-at coefficients 1 0)
         (lw-complex-coefficient-at (cdr coefficients) 0 0)))
 :hints (("Goal"
  :use (lw-pdv-second-coefficient
        (:instance lw-pdv-first-coefficient (coefficients (cdr coefficients)) (offset 0)))
  :in-theory (union-theories
   '(lw-complex-coefficientsp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-pdv-add-constant-zero
 (implies (and (lw-complexp constant) (lw-complex-coefficientsp coefficients))
  (equal (lw-complex-coefficient-at (lw-polynomial-add-constant constant coefficients) 0 0)
         (lw-complex-add constant (lw-complex-coefficient-at coefficients 0 0))))
 :hints (("Goal"
  :use (lw-polynomial-add-constant-valid
        (:instance lw-polynomial-add-constant-evaluation (point (cons 0 0)))
        lw-complex-polynomial-at-zero
        (:instance lw-complex-polynomial-at-zero (coefficients (lw-polynomial-add-constant constant coefficients))))
  :in-theory (union-theories
   '(lw-complexp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-polynomial-add-constant-linear-coefficient
 (implies (and (lw-complexp constant) (lw-complex-coefficientsp coefficients))
  (equal (lw-complex-coefficient-at (lw-polynomial-add-constant constant coefficients) 1 0)
         (lw-complex-coefficient-at coefficients 1 0)))
 :hints (("Goal"
  :use (lw-polynomial-add-constant-valid)
  :in-theory (union-theories
   '(lw-polynomial-add-constant lw-pdv-second-coefficient lw-complex-coefficientsp lw-complexp endp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-pdv-multiply-linear-zero
 (implies (and (lw-complexp constant) (lw-complexp slope) (lw-complex-coefficientsp coefficients))
  (equal (lw-complex-coefficient-at (lw-polynomial-multiply-linear constant slope coefficients) 0 0)
         (lw-complex-mul constant (lw-complex-coefficient-at coefficients 0 0))))
 :hints (("Goal"
  :use (lw-polynomial-multiply-linear-valid
        (:instance lw-polynomial-multiply-linear-evaluation (point (cons 0 0)))
        lw-complex-polynomial-at-zero
        (:instance lw-complex-polynomial-at-zero (coefficients (lw-polynomial-multiply-linear constant slope coefficients))))
  :in-theory (union-theories
   '(lw-complexp lw-complex-mul-zero lw-complex-add-zero lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-polynomial-multiply-linear-first-coefficient
 (implies (and (lw-complexp constant) (lw-complexp slope) (lw-complex-coefficientsp coefficients))
  (equal (lw-complex-coefficient-at (lw-polynomial-multiply-linear constant slope coefficients) 1 0)
         (lw-complex-add
          (lw-complex-mul constant (lw-complex-coefficient-at coefficients 1 0))
          (lw-complex-mul slope (lw-complex-coefficient-at coefficients 0 0)))))
 :hints (("Goal"
  :cases ((consp coefficients))
  :use (lw-polynomial-multiply-linear-valid
        (:instance lw-complex-coefficient-at-rational (target 1) (offset 0))
        (:instance lw-complex-ring-rational (left constant) (right (lw-complex-coefficient-at coefficients 1 0)))
        (:instance lw-polynomial-multiply-linear-valid (coefficients (cdr coefficients)))
        (:instance lw-polynomial-add-constant-valid
         (constant (lw-complex-mul slope (car coefficients)))
         (coefficients (lw-polynomial-multiply-linear constant slope (cdr coefficients))))
        (:instance lw-complex-operations-rational (left slope) (right (car coefficients)) (factor 1)))
  :expand ((lw-polynomial-multiply-linear constant slope coefficients)
           (lw-polynomial-multiply-linear constant slope nil))
  :in-theory (union-theories
   '(lw-pdv-one-step lw-pdv-first-coefficient lw-pdv-nil-coefficient lw-pdv-add-constant-zero lw-pdv-multiply-linear-zero lw-complex-coefficientsp lw-complexp lw-complex-mul-zero lw-complex-add-zero lw-complex-add-commutative lw-complex-ring-rational lw-complex-coefficient-at-rational endp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-polynomial-derivative (coefficients point)
 (if (endp coefficients) (cons 0 0)
  (lw-complex-add
   (lw-complex-polynomial (cdr coefficients) point 0)
   (lw-complex-mul point (lw-complex-polynomial-derivative (cdr coefficients) point)))))

(defthm lw-complex-polynomial-derivative-rational
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point))
  (lw-complexp (lw-complex-polynomial-derivative coefficients point)))
 :hints (("Goal" :induct (lw-complex-polynomial-derivative coefficients point)
  :in-theory (union-theories
   '(lw-complex-polynomial-derivative lw-complex-coefficientsp lw-complex-polynomial-rational lw-complex-ring-rational lw-complexp endp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (in-theory (disable lw-complex-polynomial-derivative)))

(defthm lw-polynomial-affine-constant-coefficient
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp center) (lw-complexp slope))
  (equal (lw-complex-coefficient-at (lw-polynomial-affine coefficients center slope) 0 0)
         (lw-complex-polynomial coefficients center 0)))
 :hints (("Goal"
  :use (lw-polynomial-affine-valid
        (:instance lw-polynomial-affine-evaluation (point (cons 0 0)))
        (:instance lw-complex-polynomial-at-zero (coefficients (lw-polynomial-affine coefficients center slope))))
  :in-theory (union-theories
   '(lw-complexp lw-complex-mul-zero lw-complex-add-zero lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-pdv-affine-chain
 (implies (and (lw-complexp center) (lw-complexp slope) (lw-complexp derivative) (lw-complexp value))
  (equal
   (lw-complex-add (lw-complex-mul center (lw-complex-mul slope derivative)) (lw-complex-mul slope value))
   (lw-complex-mul slope (lw-complex-add value (lw-complex-mul center derivative)))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-add lw-complex-mul lw-complex-scale lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defthm lw-polynomial-affine-linear-coefficient
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp center) (lw-complexp slope))
  (equal (lw-complex-coefficient-at (lw-polynomial-affine coefficients center slope) 1 0)
         (lw-complex-mul slope (lw-complex-polynomial-derivative coefficients center))))
 :hints (("Goal" :induct (lw-polynomial-affine coefficients center slope)
  :in-theory (union-theories
   '((:induction lw-polynomial-affine) lw-polynomial-affine lw-complex-polynomial-derivative lw-complex-coefficientsp lw-polynomial-add-constant-linear-coefficient lw-polynomial-multiply-linear-first-coefficient lw-polynomial-affine-constant-coefficient lw-polynomial-affine-valid lw-polynomial-multiply-linear-valid lw-complex-polynomial-rational lw-complex-polynomial-derivative-rational lw-pdv-affine-chain lw-pdv-nil-coefficient lw-complex-mul-zero lw-complexp endp lw-pdv-left-commutes lw-pdv-left-distributes lw-pdv-fold-constants lw-pdv-times-negative lw-pdv-negative-times lw-pdv-zero-times lw-pdv-minus-one lw-pdv-double-negative lw-pdv-add-cancel lw-pdv-double lw-pdv-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

