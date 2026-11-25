(in-package "ACL2")

(include-book "polynomial-leading-radius")
(include-book "polynomial-coefficient-maps")

; The leading monomial on the normalized square has one fixed multiplier.

(local (defthm lw-plf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-plf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-plf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-plf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-plf-times-negative (a b) (b a)))
                 :in-theory (disable lw-plf-times-negative)))))

(local (defthm lw-plf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-plf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-plf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-plf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-plf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-plf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-plf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-plf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-plf-left-commutes)))))
(defun lw-polynomial-leading-factor (coefficients)
 (lw-complex-scale
  (lw-rational-power (lw-polynomial-leading-radius coefficients)
                     (len (lw-polynomial-without-leading coefficients)))
  (lw-polynomial-leading coefficients)))

(defun lw-polynomial-leading-floor (coefficients)
 (* (lw-complex-nonzero-lower (lw-polynomial-leading coefficients))
    (lw-rational-power (lw-polynomial-leading-radius coefficients)
                       (len (lw-polynomial-without-leading coefficients)))))

(defun lw-polynomial-leading-cap (coefficients)
 (* (lw-complex-l1 (lw-polynomial-leading coefficients))
    (lw-rational-power (lw-polynomial-leading-radius coefficients)
                       (len (lw-polynomial-without-leading coefficients)))))

(local (defthm lw-plf-length-natural
 (natp (len points)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-plf-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-plf-norm-scale
 (implies (and (lw-complexp point) (rationalp factor))
  (equal (lw-complex-norm-square (lw-complex-scale factor point))
         (* factor factor (lw-complex-norm-square point))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-norm-square lw-complex-scale lw-plf-left-commutes lw-plf-left-distributes lw-plf-fold-constants lw-plf-times-negative lw-plf-negative-times lw-plf-zero-times lw-plf-minus-one lw-plf-double-negative lw-plf-add-cancel lw-plf-double lw-plf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-plf-scaled-lower
 (implies (and (lw-complexp point) (rationalp factor) (< 0 factor)
               (rationalp lower) (< 0 lower)
               (<= (* lower lower) (lw-complex-norm-square point)))
  (<= (* lower factor lower factor)
      (lw-complex-norm-square (lw-complex-scale factor point))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-plf-multiply-order
          (a (* lower lower)) (b (lw-complex-norm-square point)) (factor (* factor factor))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-plf-norm-scale lw-plf-left-commutes lw-plf-left-distributes lw-plf-fold-constants lw-plf-times-negative lw-plf-negative-times lw-plf-zero-times lw-plf-minus-one lw-plf-double-negative lw-plf-add-cancel lw-plf-double lw-plf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-leading-factor-data
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0))))
  (and (lw-complexp (lw-polynomial-leading-factor coefficients))
       (not (equal (lw-polynomial-leading-factor coefficients) (cons 0 0)))
       (rationalp (lw-polynomial-leading-floor coefficients))
       (< 0 (lw-polynomial-leading-floor coefficients))
       (rationalp (lw-polynomial-leading-cap coefficients))
       (<= 0 (lw-polynomial-leading-cap coefficients))
       (lw-complex-diskp (lw-polynomial-leading-factor coefficients)
                         (lw-polynomial-leading-cap coefficients))
       (<= (* (lw-polynomial-leading-floor coefficients) (lw-polynomial-leading-floor coefficients))
           (lw-complex-norm-square (lw-polynomial-leading-factor coefficients)))))
 :hints (("Goal"
  :use (lw-polynomial-leading-valid lw-polynomial-leading-radius-data
        (:instance lw-complex-nonzero-lower-valid (point (lw-polynomial-leading coefficients)))
        (:instance lw-complex-l1-bound (point (lw-polynomial-leading coefficients)))
        (:instance lw-rational-power-at-least-one
          (base (lw-polynomial-leading-radius coefficients))
          (exponent (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-plf-positive-product
          (a (lw-complex-nonzero-lower (lw-polynomial-leading coefficients)))
          (b (lw-rational-power (lw-polynomial-leading-radius coefficients)
                               (len (lw-polynomial-without-leading coefficients)))))
        (:instance lw-plf-multiply-order
          (a 0) (b (lw-complex-l1 (lw-polynomial-leading coefficients)))
          (factor (lw-rational-power (lw-polynomial-leading-radius coefficients)
                                    (len (lw-polynomial-without-leading coefficients)))))
        (:instance lw-plf-scaled-lower
          (point (lw-polynomial-leading coefficients))
          (lower (lw-complex-nonzero-lower (lw-polynomial-leading coefficients)))
          (factor (lw-rational-power (lw-polynomial-leading-radius coefficients)
                                    (len (lw-polynomial-without-leading coefficients)))))
        (:instance lw-complex-scale-disk
          (point (lw-polynomial-leading coefficients))
          (radius (lw-complex-l1 (lw-polynomial-leading coefficients)))
          (factor (lw-rational-power (lw-polynomial-leading-radius coefficients)
                                    (len (lw-polynomial-without-leading coefficients)))))
        (:instance lw-complex-norm-lower-nonzero
          (point (lw-polynomial-leading-factor coefficients))
          (lower (lw-polynomial-leading-floor coefficients))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-leading-factor lw-polynomial-leading-floor lw-polynomial-leading-cap lw-rational-power-rational lw-complex-scale-rational lw-plf-length-natural lw-plf-product-rational abs lw-plf-left-commutes lw-plf-left-distributes lw-plf-fold-constants lw-plf-times-negative lw-plf-negative-times lw-plf-zero-times lw-plf-minus-one lw-plf-double-negative lw-plf-add-cancel lw-plf-double lw-plf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-plf-move-scale
 (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-mul a (lw-complex-scale factor b))
         (lw-complex-mul (lw-complex-scale factor a) b)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-mul lw-complex-scale lw-plf-left-commutes lw-plf-left-distributes lw-plf-fold-constants lw-plf-times-negative lw-plf-negative-times lw-plf-zero-times lw-plf-minus-one lw-plf-double-negative lw-plf-add-cancel lw-plf-double lw-plf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-leading-scaled-term
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (lw-complexp point))
  (equal (lw-complex-mul (lw-polynomial-leading coefficients)
          (lw-complex-power (lw-complex-scale (lw-polynomial-leading-radius coefficients) point)
                           (len (lw-polynomial-without-leading coefficients))))
         (lw-complex-mul (lw-polynomial-leading-factor coefficients)
          (lw-complex-power point (len (lw-polynomial-without-leading coefficients))))))
 :hints (("Goal"
  :use (lw-polynomial-leading-valid lw-polynomial-leading-radius-data)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-leading-factor lw-complex-power-scale lw-plf-move-scale lw-complex-power-rational lw-rational-power-rational lw-plf-length-natural lw-plf-left-commutes lw-plf-left-distributes lw-plf-fold-constants lw-plf-times-negative lw-plf-negative-times lw-plf-zero-times lw-plf-minus-one lw-plf-double-negative lw-plf-add-cancel lw-plf-double lw-plf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
