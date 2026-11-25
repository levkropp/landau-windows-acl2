(in-package "ACL2")

(include-book "polynomial-degree-bounds")

; Compute a radius on which the whole lower-degree part is at most
; one sixteenth of a rational lower scale for the leading monomial.

(local (defthm lw-plr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-plr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-plr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-plr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-plr-times-negative (a b) (b a)))
                 :in-theory (disable lw-plr-times-negative)))))

(local (defthm lw-plr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-plr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-plr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-plr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-plr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-plr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-plr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-plr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-plr-left-commutes)))))

(defun lw-complex-nonzero-lower (point)
 (let ((norm (lw-complex-norm-square point))) (* norm (/ (+ 1 norm)))))

(local (defthm lw-plr-inverse-rational
 (implies (rationalp x) (rationalp (/ x))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-plr-product-rational
 (implies (and (rationalp x) (rationalp y)) (rationalp (* x y)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-plr-inverse-positive
 (implies (and (rationalp x) (< 0 x)) (< 0 (/ x)))
 :hints (("Goal" :use ((:instance inverse-of-*))
          :in-theory (disable inverse-of-*) :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plr-small-lower
 (implies (and (rationalp norm) (< 0 norm))
  (let ((lower (* norm (/ (+ 1 norm)))))
   (and (rationalp lower) (< 0 lower) (<= lower 1)
        (<= (* lower lower) norm))))
 :hints (("Goal"
  :use ((:instance lw-plr-inverse-positive (x (+ 1 norm)))
        (:instance lw-plr-positive-product (a norm) (b (/ (+ 1 norm))))
        (:instance lw-plr-inverse-factor (divisor (+ 1 norm)) (coefficient norm))
        (:instance lw-plr-multiply-order
          (a (* norm (/ (+ 1 norm)))) (b 1) (factor (* norm (/ (+ 1 norm))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-plr-inverse-rational lw-plr-product-rational lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-complex-nonzero-lower-valid
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
  (and (rationalp (lw-complex-nonzero-lower point))
       (< 0 (lw-complex-nonzero-lower point))
       (<= (lw-complex-nonzero-lower point) 1)
       (<= (* (lw-complex-nonzero-lower point) (lw-complex-nonzero-lower point))
           (lw-complex-norm-square point))))
 :hints (("Goal"
  :use (lw-complex-norm-square-positive lw-complex-norm-square-valid
        (:instance lw-plr-small-lower (norm (lw-complex-norm-square point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-nonzero-lower lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defun lw-polynomial-leading-radius (coefficients)
 (let* ((lower (lw-complex-nonzero-lower (lw-polynomial-leading coefficients)))
        (tail (lw-polynomial-without-leading coefficients)))
  (if (equal lower 0) 1
   (+ 1 (* 16 (lw-complex-coefficient-mass tail) (lw-rational-power 2 (len tail)) (/ lower))))))

(local (defthm lw-plr-radius-algebra
 (implies (and (rationalp mass) (<= 0 mass) (rationalp lower) (< 0 lower)
               (rationalp power) (<= 1 power))
  (let ((radius (+ 1 (* 16 mass power (/ lower)))))
   (and (rationalp radius) (<= 1 radius) (<= (* 16 mass power) (* lower radius)))))
 :hints (("Goal"
  :use ((:instance lw-plr-inverse-positive (x lower))
        (:instance lw-plr-positive-product (a power) (b (/ lower)))
        (:instance lw-plr-multiply-order (a 0) (b mass) (factor (* 16 power (/ lower))))
        (:instance lw-plr-inverse-factor (divisor lower) (coefficient (* 16 mass power))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-plr-inverse-rational lw-plr-product-rational lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-leading-radius-data
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0))))
  (let* ((lower (lw-complex-nonzero-lower (lw-polynomial-leading coefficients)))
         (tail (lw-polynomial-without-leading coefficients))
         (radius (lw-polynomial-leading-radius coefficients)))
   (and (rationalp lower) (< 0 lower) (rationalp radius) (<= 1 radius)
        (<= (* 16 (lw-complex-coefficient-mass tail) (lw-rational-power 2 (len tail)))
            (* lower radius)))))
 :hints (("Goal"
  :use (lw-polynomial-leading-valid
        (:instance lw-complex-nonzero-lower-valid (point (lw-polynomial-leading coefficients)))
        (:instance lw-complex-coefficient-mass-valid (coefficients (lw-polynomial-without-leading coefficients)))
        (:instance lw-rational-power-at-least-one (base 2) (exponent (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-plr-radius-algebra
          (mass (lw-complex-coefficient-mass (lw-polynomial-without-leading coefficients)))
          (lower (lw-complex-nonzero-lower (lw-polynomial-leading coefficients)))
          (power (lw-rational-power 2 (len (lw-polynomial-without-leading coefficients))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-leading-radius lw-rational-power-rational lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-plr-power-step
 (implies (posp degree)
  (equal (lw-rational-power radius degree) (* radius (lw-rational-power radius (- degree 1)))))
 :hints (("Goal" :expand ((lw-rational-power radius degree)) :in-theory (union-theories
 '(fold-consts-in-+ lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-plr-radius-power-budget
 (implies (and (rationalp mass) (<= 0 mass) (rationalp lower) (< 0 lower)
               (rationalp radius) (<= 1 radius) (posp degree)
               (<= (* 16 mass (lw-rational-power 2 degree)) (* lower radius)))
  (<= (* mass (lw-rational-power (* 2 radius) (- degree 1)))
      (* 1/16 lower (lw-rational-power radius degree))))
 :hints (("Goal"
  :use ((:instance lw-rational-power-monotone-exponent (base 2) (small (- degree 1)) (large degree))
        (:instance lw-rational-power-at-least-one (base radius) (exponent (- degree 1)))
        (:instance lw-plr-multiply-order
          (a (lw-rational-power 2 (- degree 1))) (b (lw-rational-power 2 degree)) (factor (* 16 mass)))
        (:instance lw-plr-multiply-order
          (a (* 16 mass (lw-rational-power 2 (- degree 1)))) (b (* lower radius))
          (factor (* 1/16 (lw-rational-power radius (- degree 1))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rational-power-product lw-rational-power-rational lw-plr-power-step lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)) :rule-classes nil))

(local (defthm lw-plr-length-natural
 (natp (len coefficients)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-plr-positive-lower-degree
 (implies (and (consp coefficients) (consp (cdr coefficients)))
          (posp (len (lw-polynomial-without-leading coefficients))))
 :hints (("Goal" :expand ((lw-polynomial-without-leading coefficients))
          :in-theory (union-theories
 '(fold-consts-in-+ len lw-plr-length-natural lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-computed-leading-remainder-bound
 (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (lw-complex-diskp point (* 2 (lw-polynomial-leading-radius coefficients))))
  (let* ((tail (lw-polynomial-without-leading coefficients))
         (degree (len tail)) (radius (lw-polynomial-leading-radius coefficients))
         (lower (lw-complex-nonzero-lower (lw-polynomial-leading coefficients))))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-polynomial coefficients point 0)
     (lw-complex-mul (lw-polynomial-leading coefficients) (lw-complex-power point degree)))
    (* 1/16 lower (lw-rational-power radius degree)))))
 :hints (("Goal"
  :use (lw-polynomial-leading-valid lw-polynomial-leading-radius-data
        (:instance lw-polynomial-leading-remainder-bound (radius (* 2 (lw-polynomial-leading-radius coefficients))))
        (:instance lw-complex-coefficient-mass-valid (coefficients (lw-polynomial-without-leading coefficients)))
        (:instance lw-plr-radius-power-budget
          (mass (lw-complex-coefficient-mass (lw-polynomial-without-leading coefficients)))
          (lower (lw-complex-nonzero-lower (lw-polynomial-leading coefficients)))
          (degree (len (lw-polynomial-without-leading coefficients)))
          (radius (lw-polynomial-leading-radius coefficients)))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                   (lw-complex-mul (lw-polynomial-leading coefficients)
                    (lw-complex-power point (len (lw-polynomial-without-leading coefficients))))))
          (radius (* (lw-complex-coefficient-mass (lw-polynomial-without-leading coefficients))
                     (lw-rational-power (* 2 (lw-polynomial-leading-radius coefficients))
                       (- (len (lw-polynomial-without-leading coefficients)) 1))))
          (cap (* 1/16 (lw-complex-nonzero-lower (lw-polynomial-leading coefficients))
                      (lw-rational-power (lw-polynomial-leading-radius coefficients)
                        (len (lw-polynomial-without-leading coefficients)))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-plr-positive-lower-degree lw-plr-length-natural lw-rational-power-rational lw-plr-left-commutes lw-plr-left-distributes lw-plr-fold-constants lw-plr-times-negative lw-plr-negative-times lw-plr-zero-times lw-plr-minus-one lw-plr-double-negative lw-plr-add-cancel lw-plr-double lw-plr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

