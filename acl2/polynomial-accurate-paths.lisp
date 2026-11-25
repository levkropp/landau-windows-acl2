(in-package "ACL2")

(include-book "polynomial-factor-accuracy")

; The generated product keeps a positive boundary collar and is pointwise
; close to the polynomial, ready for finite polygon homotopy.

(local (defthm lw-pap-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pap-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pap-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pap-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pap-times-negative (a b) (b a)))
                 :in-theory (disable lw-pap-times-negative)))))

(local (defthm lw-pap-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pap-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pap-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pap-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pap-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pap-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pap-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pap-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pap-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pap-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pap-left-commutes)))))
(local (defthm lw-pap-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pap-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pap-left-commutes lw-pap-left-distributes lw-pap-fold-constants lw-pap-times-negative lw-pap-negative-times lw-pap-zero-times lw-pap-minus-one lw-pap-double-negative lw-pap-add-cancel lw-pap-double lw-pap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-square-accurate-excludes-small
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-unit-square-pointp point))
  (not (lw-complex-diskp (lw-polynomial-linear-factor-value (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point) (* 2 (lw-polynomial-square-factor-request coefficients count tolerance)))))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-data lw-polynomial-square-factor-request-data
        lw-polynomial-square-accurate-approximation lw-polynomial-unit-square-excludes-clearance
        (:instance lw-polynomial-square-clearance-data (anchor (cons -1 -1)) (side 2))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial coefficients point 0)) (right (lw-polynomial-linear-factor-value (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point)) (radius (lw-polynomial-square-factor-request coefficients count tolerance)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial coefficients point 0)) (radius (+ (* 2 (lw-polynomial-square-factor-request coefficients count tolerance)) (lw-polynomial-square-factor-request coefficients count tolerance))) (cap (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count)))
        (:instance lw-complex-perturbation-excludes-small
          (left (lw-complex-polynomial coefficients point 0)) (right (lw-polynomial-linear-factor-value (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point)) (epsilon (* 2 (lw-polynomial-square-factor-request coefficients count tolerance))) (delta (lw-polynomial-square-factor-request coefficients count tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial-rational lw-polynomial-linear-factor-value-rational lw-pap-point-type lw-pap-product-rational lw-pap-left-commutes lw-pap-left-distributes lw-pap-fold-constants lw-pap-times-negative lw-pap-negative-times lw-pap-zero-times lw-pap-minus-one lw-pap-double-negative lw-pap-add-cancel lw-pap-double lw-pap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-square-accurate-path-avoids
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-ray-unit-square-pointsp points))
  (lw-ray-row-avoids (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points) (* 2 (lw-polynomial-square-factor-request coefficients count tolerance))))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-ray-row-avoids lw-ray-unit-square-pointsp lw-polynomial-square-accurate-excludes-small endp lw-pap-left-commutes lw-pap-left-distributes lw-pap-fold-constants lw-pap-times-negative lw-pap-negative-times lw-pap-zero-times lw-pap-minus-one lw-pap-double-negative lw-pap-add-cancel lw-pap-double lw-pap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-square-accurate-path-comparison
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-ray-unit-square-pointsp points))
  (lw-ray-pointwise-nearp (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points)
                          (lw-polynomial-path-values coefficients points) (lw-polynomial-square-factor-request coefficients count tolerance)))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-polynomial-path-values lw-ray-pointwise-nearp lw-ray-unit-square-pointsp lw-polynomial-square-accurate-approximation lw-polynomial-linear-factor-value-rational lw-complex-polynomial-rational lw-pap-point-type endp lw-pap-left-commutes lw-pap-left-distributes lw-pap-fold-constants lw-pap-times-negative lw-pap-negative-times lw-pap-zero-times lw-pap-minus-one lw-pap-double-negative lw-pap-add-cancel lw-pap-double lw-pap-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-polynomial-square-accurate-data) :do-not-induct t))))
