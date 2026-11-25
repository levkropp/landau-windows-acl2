(in-package "ACL2")

(include-book "polynomial-leading-comparison")

; Dominance at the computed radius generates the polynomial's outer index.
; All path and mesh hypotheses are rational, executable checks.

(local (defthm lw-poi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-poi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-poi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-poi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-poi-times-negative (a b) (b a)))
                 :in-theory (disable lw-poi-times-negative)))))

(local (defthm lw-poi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-poi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-poi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-poi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-poi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-poi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-poi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-poi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-poi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-poi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-poi-left-commutes)))))
(local (defthm lw-poi-length-natural
 (natp (len points)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-poi-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-poi-power-head
 (implies (consp points)
  (equal (car (lw-ray-power-points points index)) (lw-complex-power (car points) index)))
 :hints (("Goal" :expand ((lw-ray-power-points points index)) :in-theory (union-theories
 '(fold-consts-in-+ lw-poi-left-commutes lw-poi-left-distributes lw-poi-fold-constants lw-poi-times-negative lw-poi-negative-times lw-poi-zero-times lw-poi-minus-one lw-poi-double-negative lw-poi-add-cancel lw-poi-double lw-poi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-poi-leading-index
 (implies (and (lw-complex-coefficientsp coefficients)
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (consp points) (lw-ray-annulus-pointsp points 1 2)
               (equal (lw-ray-row-last points) (car points))
               (rationalp error) (<= 0 error)
               (lw-ray-path-step-check points error)
               (<= error (lw-ray-power-step-budget (len (lw-polynomial-without-leading coefficients)))))
  (equal (lw-ray-polygon-index
           (lw-ray-multiply-points (lw-polynomial-leading-factor coefficients)
            (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients)))))
         (* (len (lw-polynomial-without-leading coefficients)) (lw-ray-polygon-index points))))
 :hints (("Goal"
  :use (lw-polynomial-leading-factor-data
        (:instance lw-ray-power-step-budget-valid (degree (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-path-step-enlarge (delta error)
          (larger (lw-ray-power-step-budget (len (lw-polynomial-without-leading coefficients)))))
        (:instance lw-ray-power-index-at-computed-step
          (degree (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-power-boundary-safe
          (degree (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-polygon-product-invariant
          (factor (lw-polynomial-leading-factor coefficients))
          (points (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-poi-length-natural lw-poi-left-commutes lw-poi-left-distributes lw-poi-fold-constants lw-poi-times-negative lw-poi-negative-times lw-poi-zero-times lw-poi-minus-one lw-poi-double-negative lw-poi-add-cancel lw-poi-double lw-poi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-outer-path-index
 (implies (and (lw-complex-coefficientsp coefficients)
               (consp coefficients) (consp (cdr coefficients))
               (not (equal (lw-polynomial-leading coefficients) (cons 0 0)))
               (consp points) (lw-ray-annulus-pointsp points 1 2)
               (equal (lw-ray-row-last points) (car points))
               (rationalp error) (<= 0 error)
               (lw-ray-path-step-check points error)
               (<= error (lw-ray-power-step-budget (len (lw-polynomial-without-leading coefficients))))
               (<= (* (lw-polynomial-leading-cap coefficients)
                      (lw-rational-power 4 (len (lw-polynomial-without-leading coefficients))) error)
                   (* 1/16 (lw-polynomial-leading-floor coefficients))))
  (equal (lw-ray-polygon-index
           (lw-polynomial-path-values
            (lw-polynomial-rescale coefficients (lw-polynomial-leading-radius coefficients) 0) points))
         (* (len (lw-polynomial-without-leading coefficients)) (lw-ray-polygon-index points))))
 :hints (("Goal"
  :use (lw-polynomial-leading-factor-data lw-polynomial-leading-path-comparison
        lw-polynomial-leading-path-annulus lw-polynomial-leading-path-step
        lw-poi-leading-index
        (:instance lw-ray-annulus-data (lower 1) (upper 2))
        (:instance lw-ray-power-points-data (index (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-power-points-last (index (len (lw-polynomial-without-leading coefficients))))
        (:instance lw-ray-multiply-points-data
          (factor (lw-polynomial-leading-factor coefficients))
          (points (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients)))))
        (:instance lw-ray-multiplier-closed
          (factor (lw-polynomial-leading-factor coefficients))
          (points (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients)))))
        (:instance lw-ray-path-step-enlarge
          (points (lw-ray-multiply-points (lw-polynomial-leading-factor coefficients)
                   (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients)))))
          (delta (* (lw-polynomial-leading-cap coefficients)
                    (lw-rational-power 4 (len (lw-polynomial-without-leading coefficients))) error))
          (larger (* 1/16 (lw-polynomial-leading-floor coefficients))))
        (:instance lw-ray-annulus-pointwise-perturbation
          (bottom (lw-ray-multiply-points (lw-polynomial-leading-factor coefficients)
                   (lw-ray-power-points points (len (lw-polynomial-without-leading coefficients)))))
          (top (lw-polynomial-path-values
                (lw-polynomial-rescale coefficients (lw-polynomial-leading-radius coefficients) 0) points))
          (lower (lw-polynomial-leading-floor coefficients))
          (upper (* (lw-polynomial-leading-cap coefficients)
                    (lw-rational-power 2 (len (lw-polynomial-without-leading coefficients)))))
          (beta (* 1/16 (lw-polynomial-leading-floor coefficients)))
          (delta (* 1/16 (lw-polynomial-leading-floor coefficients)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-poi-length-natural lw-poi-product-rational lw-poi-power-head lw-rational-power-rational lw-poi-left-commutes lw-poi-left-distributes lw-poi-fold-constants lw-poi-times-negative lw-poi-negative-times lw-poi-zero-times lw-poi-minus-one lw-poi-double-negative lw-poi-add-cancel lw-poi-double lw-poi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
