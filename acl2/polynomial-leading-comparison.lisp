(in-package "ACL2")

(include-book "polynomial-leading-factor")
(include-book "ray-multiplier-bounds")
(include-book "polygon-perturbation-budgets")
(include-book "polynomial-path-refinement")

; Generated comparison of P(R*z) with its leading monomial on 1 <= |z| <= 2.

(local (defthm lw-plc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-plc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-plc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-plc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-plc-times-negative (a b) (b a)))
                 :in-theory (disable lw-plc-times-negative)))))

(local (defthm lw-plc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-plc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-plc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-plc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-plc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-plc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-plc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-plc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-plc-left-commutes)))))
(local (defthm lw-plc-length-natural
 (natp (len points)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-plc-near-point
 (implies (and (lw-complex-coefficientsp coefficients)
               (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (lw-complex-diskp point 2))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-polynomial (lw-polynomial-rescale coefficients (lw-polynomial-leading-radius coefficients) 0) point 0)
    (lw-complex-mul (lw-polynomial-leading-factor coefficients)
     (lw-complex-power point (len (lw-polynomial-without-leading coefficients)))))
   (* 1/16 (lw-polynomial-leading-floor coefficients))))
 :hints (("Goal"
  :use (lw-polynomial-leading-radius-data
        (:instance lw-complex-scale-disk (radius 2) (factor (lw-polynomial-leading-radius coefficients)))
        (:instance lw-polynomial-computed-leading-remainder-bound
          (point (lw-complex-scale (lw-polynomial-leading-radius coefficients) point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-disk-data lw-polynomial-rescale-evaluation lw-polynomial-leading-scaled-term lw-polynomial-leading-floor abs lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-polynomial-leading-path-comparison
 (implies (and (lw-complex-coefficientsp coefficients)
               (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (lw-ray-annulus-pointsp points 1 2))
  (lw-ray-pointwise-nearp
   (lw-ray-multiply-points (lw-polynomial-leading-factor coefficients)
    (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients))))
   (lw-polynomial-path-values
    (lw-polynomial-rescale coefficients (lw-polynomial-leading-radius coefficients) 0) points)
   (* 1/16 (lw-polynomial-leading-floor coefficients))))
 :hints (("Goal" :induct (lw-ray-annulus-pointsp points 1 2)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-annulus-pointsp lw-ray-multiply-points lw-ray-power-points lw-polynomial-path-values lw-ray-pointwise-nearp lw-plc-near-point endp lw-complex-disk-data lw-polynomial-leading-factor-data lw-complex-power-rational lw-plc-length-natural lw-complex-ring-rational lw-complex-polynomial-rational lw-polynomial-rescale-valid lw-polynomial-leading-radius-data lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-leading-path-annulus
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (lw-ray-annulus-pointsp points 1 2))
  (lw-ray-annulus-pointsp
   (lw-ray-multiply-points (lw-polynomial-leading-factor coefficients)
    (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients))))
   (lw-polynomial-leading-floor coefficients)
   (* (lw-polynomial-leading-cap coefficients)
      (lw-rational-power 2 (len (lw-polynomial-without-leading coefficients))))))
 :hints (("Goal"
  :use (lw-polynomial-leading-factor-data
        (:instance lw-ray-power-points-annulus
          (degree (len (lw-polynomial-without-leading coefficients)))
          (index (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-multiplier-annulus
          (factor (lw-polynomial-leading-factor coefficients))
          (lower (lw-polynomial-leading-floor coefficients))
          (cap (lw-polynomial-leading-cap coefficients))
          (points (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients))))
          (upper (lw-rational-power 2 (len (lw-polynomial-without-leading coefficients))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-plc-length-natural lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-leading-path-step
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (lw-ray-annulus-pointsp points 1 2)
               (rationalp error) (<= 0 error) (lw-ray-path-step-check points error))
  (lw-ray-path-step-check
   (lw-ray-multiply-points (lw-polynomial-leading-factor coefficients)
    (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients))))
   (* (lw-polynomial-leading-cap coefficients)
      (lw-rational-power 4 (len (lw-polynomial-without-leading coefficients))) error)))
 :hints (("Goal"
  :use (lw-polynomial-leading-factor-data
        (:instance lw-ray-annulus-data (lower 1) (upper 2))
        (:instance lw-ray-power-points-data
          (index (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-power-points-step
          (index (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-multiplier-step
          (factor (lw-polynomial-leading-factor coefficients))
          (cap (lw-polynomial-leading-cap coefficients))
          (points (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients))))
          (error (* (lw-rational-power 4 (len (lw-polynomial-without-leading coefficients))) error))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-plc-length-natural lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
