(in-package "ACL2")

(include-book "polynomial-outer-index")
(include-book "unit-square-mesh")

; A computed step target makes the leading-term comparison unconditional.

(local (defthm lw-pom-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pom-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pom-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pom-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pom-times-negative (a b) (b a)))
                 :in-theory (disable lw-pom-times-negative)))))

(local (defthm lw-pom-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pom-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pom-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pom-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pom-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pom-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pom-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pom-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pom-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pom-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pom-left-commutes)))))
(defun lw-polynomial-outer-step (coefficients)
 (let* ((degree (len (lw-polynomial-without-leading coefficients)))
        (budget (lw-ray-power-step-budget degree))
        (denominator (* 16 (+ 1 (lw-polynomial-leading-cap coefficients)) (lw-rational-power 4 degree)))
        (candidate (if (equal denominator 0) 0
                    (* (lw-polynomial-leading-floor coefficients) (/ denominator)))))
  (if (< candidate budget) candidate budget)))

(local (defthm lw-pom-length-natural
 (natp (len points)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pom-inverse-rational
 (implies (rationalp x) (rationalp (/ x))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pom-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pom-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pom-budget
 (implies (and (rationalp lower) (< 0 lower) (rationalp cap) (<= 0 cap)
               (rationalp power) (<= 1 power) (rationalp budget) (< 0 budget))
  (let* ((denominator (* 16 (+ 1 cap) power))
         (candidate (* lower (/ denominator)))
         (step (if (< candidate budget) candidate budget)))
   (and (not (equal denominator 0))
        (rationalp step) (< 0 step) (<= step budget)
        (<= (* cap power step) (* 1/16 lower)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pom-positive-product (a (+ 1 cap)) (b power))
        (:instance lw-reciprocal-positive (value (* 16 (+ 1 cap) power)))
        (:instance lw-pom-positive-product (a lower) (b (/ (* 16 (+ 1 cap) power))))
        (:instance lw-pom-inverse-factor (divisor (* 16 (+ 1 cap) power)) (coefficient lower)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pom-product-rational lw-pom-inverse-rational lw-pom-sum-rational lw-pom-left-commutes lw-pom-left-distributes lw-pom-fold-constants lw-pom-times-negative lw-pom-negative-times lw-pom-zero-times lw-pom-minus-one lw-pom-double-negative lw-pom-add-cancel lw-pom-double lw-pom-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t))))

(defthm lw-polynomial-outer-step-data
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0))))
  (let ((step (lw-polynomial-outer-step coefficients))
        (degree (len (lw-polynomial-without-leading coefficients))))
   (and (rationalp step) (< 0 step)
        (<= step (lw-ray-power-step-budget degree))
        (<= (* (lw-polynomial-leading-cap coefficients) (lw-rational-power 4 degree) step)
            (* 1/16 (lw-polynomial-leading-floor coefficients))))))
 :hints (("Goal"
  :use (lw-polynomial-leading-factor-data
        (:instance lw-ray-power-step-budget-valid (degree (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-rational-power-at-least-one (base 4)
          (exponent (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-pom-budget
          (lower (lw-polynomial-leading-floor coefficients))
          (cap (lw-polynomial-leading-cap coefficients))
          (power (lw-rational-power 4 (len (lw-polynomial-without-leading coefficients))))
          (budget (lw-ray-power-step-budget (len (lw-polynomial-without-leading coefficients))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-outer-step lw-pom-length-natural lw-rational-power-rational lw-pom-left-commutes lw-pom-left-distributes lw-pom-fold-constants lw-pom-times-negative lw-pom-negative-times lw-pom-zero-times lw-pom-minus-one lw-pom-double-negative lw-pom-add-cancel lw-pom-double lw-pom-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-outer-boundary-index-at-mesh
 (implies (and (lw-complex-coefficientsp coefficients)
               (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (posp factor)
               (<= (* 2 (/ (* 4 factor))) (lw-polynomial-outer-step coefficients)))
  (equal (lw-ray-polygon-index
           (lw-polynomial-path-values
            (lw-polynomial-rescale coefficients (lw-polynomial-leading-radius coefficients) 0)
            (lw-unit-square-boundary (* 4 factor))))
         (len (lw-polynomial-without-leading coefficients))))
 :hints (("Goal"
  :use (lw-polynomial-outer-step-data
        (:instance lw-unit-square-boundary-at-budget (error (lw-polynomial-outer-step coefficients)))
        (:instance lw-polynomial-outer-path-index (points (lw-unit-square-boundary (* 4 factor)))
          (error (lw-polynomial-outer-step coefficients))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pom-length-natural lw-pom-left-commutes lw-pom-left-distributes lw-pom-fold-constants lw-pom-times-negative lw-pom-negative-times lw-pom-zero-times lw-pom-minus-one lw-pom-double-negative lw-pom-add-cancel lw-pom-double lw-pom-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-computed-outer-boundary-index
 (implies (and (lw-complex-coefficientsp coefficients)
               (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0))))
  (equal (lw-ray-polygon-index
           (lw-polynomial-path-values
            (lw-polynomial-rescale coefficients (lw-polynomial-leading-radius coefficients) 0)
            (lw-unit-square-boundary
             (* 4 (lw-unit-square-mesh-factor (lw-polynomial-outer-step coefficients))))))
         (len (lw-polynomial-without-leading coefficients))))
 :hints (("Goal"
  :use (lw-polynomial-outer-step-data
        (:instance lw-unit-square-mesh-factor-data (error (lw-polynomial-outer-step coefficients)))
        (:instance lw-polynomial-outer-boundary-index-at-mesh
          (factor (lw-unit-square-mesh-factor (lw-polynomial-outer-step coefficients)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pom-left-commutes lw-pom-left-distributes lw-pom-fold-constants lw-pom-times-negative lw-pom-negative-times lw-pom-zero-times lw-pom-minus-one lw-pom-double-negative lw-pom-add-cancel lw-pom-double lw-pom-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
