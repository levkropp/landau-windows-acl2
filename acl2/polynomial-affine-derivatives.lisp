(in-package "ACL2")

(include-book "polynomial-derivatives")
(include-book "polynomial-trim")

; Derivative rules for the coefficient constructors used by square models.

(local (defthm lw-pat-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pat-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pat-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pat-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pat-times-negative (a b) (b a)))
                 :in-theory (disable lw-pat-times-negative)))))

(local (defthm lw-pat-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pat-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pat-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pat-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pat-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pat-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pat-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pat-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pat-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pat-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pat-left-commutes)))))

(local (defthm lw-pat-nil-value
 (equal (lw-complex-polynomial nil point 0) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial endp lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pat-cons-derivative
 (implies (and (lw-complex-coefficientsp tail) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (cons head tail) point)
         (lw-complex-add (lw-complex-polynomial tail point 0)
                         (lw-complex-mul point (lw-complex-polynomial-derivative tail point)))))
 :hints (("Goal" :expand ((lw-complex-polynomial-derivative (cons head tail) point))
  :in-theory (union-theories
 '(fold-consts-in-+ endp lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-add-constant-derivative
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (lw-polynomial-add-constant constant coefficients) point)
         (lw-complex-polynomial-derivative coefficients point)))
 :hints (("Goal" :cases ((consp coefficients))
  :expand ((lw-complex-polynomial-derivative coefficients point)
           (lw-complex-polynomial-derivative nil point))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-add-constant lw-pat-cons-derivative lw-pat-nil-value lw-complex-coefficientsp lw-complex-mul-zero lw-complex-add-zero lw-complexp endp lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-pat-multiply-linear-ring
 (implies (and (lw-complexp constant) (lw-complexp slope) (lw-complexp point)
               (lw-complexp head) (lw-complexp value) (lw-complexp derivative))
  (let ((linear (lw-complex-add constant (lw-complex-mul slope point))))
   (equal
    (lw-complex-add
     (lw-complex-add (lw-complex-mul slope head) (lw-complex-mul linear value))
     (lw-complex-mul point
      (lw-complex-add (lw-complex-mul slope value) (lw-complex-mul linear derivative))))
    (lw-complex-add
     (lw-complex-mul slope (lw-complex-add head (lw-complex-mul point value)))
     (lw-complex-mul linear (lw-complex-add value (lw-complex-mul point derivative)))))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-mul lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-polynomial-multiply-linear-derivative
 (implies (and (lw-complexp constant) (lw-complexp slope)
               (lw-complex-coefficientsp coefficients) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (lw-polynomial-multiply-linear constant slope coefficients) point)
   (lw-complex-add
    (lw-complex-mul slope (lw-complex-polynomial coefficients point 0))
    (lw-complex-mul (lw-complex-add constant (lw-complex-mul slope point))
                    (lw-complex-polynomial-derivative coefficients point)))))
 :hints (("Goal" :induct (lw-polynomial-multiply-linear constant slope coefficients)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-multiply-linear) lw-polynomial-multiply-linear lw-polynomial-multiply-linear-valid lw-polynomial-add-constant-valid lw-polynomial-add-constant-evaluation lw-polynomial-add-constant-derivative lw-pat-cons-derivative lw-pat-nil-value lw-complex-polynomial-horner lw-complex-coefficientsp lw-complex-polynomial-rational lw-complex-polynomial-derivative-rational lw-complex-ring-rational lw-complex-mul-zero lw-complex-add-zero (:executable-counterpart lw-complexp) endp lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-polynomial-multiply-linear-evaluation (coefficients (cdr coefficients)))
          (:instance lw-pat-multiply-linear-ring (head (car coefficients))
           (value (lw-complex-polynomial (cdr coefficients) point 0))
           (derivative (lw-complex-polynomial-derivative (cdr coefficients) point))))
    :expand ((lw-complex-polynomial-derivative nil point)
             (lw-complex-polynomial-derivative coefficients point))
    :do-not-induct t))))

(defthm lw-polynomial-trim-derivative
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (lw-polynomial-trim coefficients) point)
         (lw-complex-polynomial-derivative coefficients point)))
 :hints (("Goal" :induct (lw-polynomial-trim coefficients)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-trim lw-polynomial-trim-valid lw-pat-nil-value lw-pat-cons-derivative lw-complex-coefficientsp lw-complex-mul-zero lw-complex-add-zero lw-complexp endp lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-polynomial-trim-evaluation (coefficients (cdr coefficients)) (offset 0)))
    :expand ((lw-complex-polynomial-derivative nil point)
             (lw-complex-polynomial-derivative (lw-polynomial-trim (cdr coefficients)) point)
             (lw-complex-polynomial (lw-polynomial-trim (cdr coefficients)) point 0)
             (lw-complex-polynomial-derivative coefficients point))
    :do-not-induct t))))

(local (defthm lw-pat-affine-ring
 (implies (and (lw-complexp slope) (lw-complexp shifted)
               (lw-complexp value) (lw-complexp derivative))
  (equal (lw-complex-add (lw-complex-mul slope value)
                        (lw-complex-mul shifted (lw-complex-mul slope derivative)))
         (lw-complex-mul slope
          (lw-complex-add value (lw-complex-mul shifted derivative)))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-mul lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-polynomial-affine-derivative
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp center)
               (lw-complexp slope) (lw-complexp point))
  (equal (lw-complex-polynomial-derivative (lw-polynomial-affine coefficients center slope) point)
         (lw-complex-mul slope
          (lw-complex-polynomial-derivative coefficients (lw-complex-add center (lw-complex-mul slope point))))))
 :hints (("Goal" :induct (lw-polynomial-affine coefficients center slope)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-affine) lw-polynomial-affine lw-polynomial-affine-valid lw-polynomial-affine-evaluation lw-polynomial-multiply-linear-valid lw-polynomial-add-constant-derivative lw-polynomial-multiply-linear-derivative lw-pat-cons-derivative lw-pat-affine-ring lw-complex-coefficientsp lw-complex-polynomial-rational lw-complex-polynomial-derivative-rational lw-complex-ring-rational lw-complex-mul-zero lw-complexp endp lw-pat-left-commutes lw-pat-left-distributes lw-pat-fold-constants lw-pat-times-negative lw-pat-negative-times lw-pat-zero-times lw-pat-minus-one lw-pat-double-negative lw-pat-add-cancel lw-pat-double lw-pat-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-pat-affine-ring
             (shifted (lw-complex-add center (lw-complex-mul slope point)))
             (value (lw-complex-polynomial (cdr coefficients) (lw-complex-add center (lw-complex-mul slope point)) 0))
             (derivative (lw-complex-polynomial-derivative (cdr coefficients) (lw-complex-add center (lw-complex-mul slope point))))))
    :expand ((lw-complex-polynomial-derivative nil point)
             (lw-complex-polynomial-derivative nil (lw-complex-add center (lw-complex-mul slope point)))
             (lw-complex-polynomial-derivative coefficients (lw-complex-add center (lw-complex-mul slope point))))
    :do-not-induct t))))
