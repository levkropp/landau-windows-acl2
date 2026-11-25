(in-package "ACL2")

(include-book "polynomial-boundary-factors")

; The generated product keeps a positive boundary collar and is pointwise
; close to the polynomial, ready for finite polygon homotopy.

(local (defthm lw-pbp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pbp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pbp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pbp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pbp-times-negative (a b) (b a)))
                 :in-theory (disable lw-pbp-times-negative)))))

(local (defthm lw-pbp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pbp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pbp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pbp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pbp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pbp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pbp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pbp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pbp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pbp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pbp-left-commutes)))))
(local (defthm lw-pbp-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pbp-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pbp-left-commutes lw-pbp-left-distributes lw-pbp-fold-constants lw-pbp-times-negative lw-pbp-negative-times lw-pbp-zero-times lw-pbp-minus-one lw-pbp-double-negative lw-pbp-add-cancel lw-pbp-double lw-pbp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-square-factor-excludes-small
 (implies (and (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-unit-square-pointp point))
  (not (lw-complex-diskp (lw-polynomial-linear-factor-value (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point) (* 2 (lw-polynomial-square-factor-error coefficients count)))))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-data lw-polynomial-square-factor-error-data
        lw-polynomial-square-factor-approximation lw-polynomial-unit-square-excludes-clearance
        (:instance lw-polynomial-square-clearance-data (anchor (cons -1 -1)) (side 2))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial coefficients point 0)) (right (lw-polynomial-linear-factor-value (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point)) (radius (lw-polynomial-square-factor-error coefficients count)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial coefficients point 0)) (radius (+ (* 2 (lw-polynomial-square-factor-error coefficients count)) (lw-polynomial-square-factor-error coefficients count))) (cap (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count)))
        (:instance lw-complex-perturbation-excludes-small
          (left (lw-complex-polynomial coefficients point 0)) (right (lw-polynomial-linear-factor-value (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point)) (epsilon (* 2 (lw-polynomial-square-factor-error coefficients count))) (delta (lw-polynomial-square-factor-error coefficients count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial-rational lw-polynomial-linear-factor-value-rational lw-pbp-point-type lw-pbp-product-rational lw-pbp-left-commutes lw-pbp-left-distributes lw-pbp-fold-constants lw-pbp-times-negative lw-pbp-negative-times lw-pbp-zero-times lw-pbp-minus-one lw-pbp-double-negative lw-pbp-add-cancel lw-pbp-double lw-pbp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-square-factor-path-avoids
 (implies (and (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-ray-unit-square-pointsp points))
  (lw-ray-row-avoids (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points) (* 2 (lw-polynomial-square-factor-error coefficients count))))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-ray-row-avoids lw-ray-unit-square-pointsp lw-polynomial-square-factor-excludes-small endp lw-pbp-left-commutes lw-pbp-left-distributes lw-pbp-fold-constants lw-pbp-times-negative lw-pbp-negative-times lw-pbp-zero-times lw-pbp-minus-one lw-pbp-double-negative lw-pbp-add-cancel lw-pbp-double lw-pbp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-square-factor-path-comparison
 (implies (and (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-ray-unit-square-pointsp points))
  (lw-ray-pointwise-nearp (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points)
                          (lw-polynomial-path-values coefficients points) (lw-polynomial-square-factor-error coefficients count)))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-polynomial-path-values lw-ray-pointwise-nearp lw-ray-unit-square-pointsp lw-polynomial-square-factor-approximation lw-polynomial-linear-factor-value-rational lw-complex-polynomial-rational lw-pbp-point-type endp lw-pbp-left-commutes lw-pbp-left-distributes lw-pbp-fold-constants lw-pbp-times-negative lw-pbp-negative-times lw-pbp-zero-times lw-pbp-minus-one lw-pbp-double-negative lw-pbp-add-cancel lw-pbp-double lw-pbp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-polynomial-square-factor-data) :do-not-induct t))))
