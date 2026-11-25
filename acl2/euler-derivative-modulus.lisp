(in-package "ACL2")

(include-book "euler-quadratic-increment")

; Computed step and precision budgets for the Euler linear increment.
; The first physical coefficient is the derivative Cauchy name.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-euler-derivative-curvature lw-euler-uniform-coefficient-cap
 lw-complex-euler-continuation-value lw-complex-euler-local-coefficient-value lw-complex-linear-remainder
 lw-euler-rounding-precision)))

(local (defthm lw-edm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edm-times-negative (a b) (b a)))
                 :in-theory (disable lw-edm-times-negative)))))

(local (defthm lw-edm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edm-left-commutes)))))

(defthm lw-euler-derivative-curvature-positive
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate))
  (and (rationalp (lw-euler-derivative-curvature rate height radius)) (< 0 (lw-euler-derivative-curvature rate height radius))))
 :hints (("Goal"
  :use (lw-euler-uniform-coefficient-cap-valid
        (:instance lw-edm-positive-product (a (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)))) (b (/ radius)))
        (:instance lw-edm-positive-product
         (a (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (/ radius))) (b (/ radius))))
  :in-theory (union-theories
   '(lw-euler-derivative-curvature lw-edm-left-commutes lw-edm-left-distributes lw-edm-fold-constants lw-edm-times-negative lw-edm-negative-times lw-edm-zero-times lw-edm-minus-one lw-edm-double-negative lw-edm-add-cancel lw-edm-double lw-edm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-euler-derivative-modulus (rate height radius error)
 (min (/ radius 2) (lw-euler-rounding-precision (lw-euler-derivative-curvature rate height radius) (/ error 2))))

(local (in-theory (disable lw-euler-derivative-modulus)))

(defthm lw-euler-derivative-modulus-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-derivative-modulus rate height radius error)) (< 0 (lw-euler-derivative-modulus rate height radius error)) (<= (lw-euler-derivative-modulus rate height radius error) (/ radius 2)) (<= (lw-euler-derivative-modulus rate height radius error) 1)
       (<= (* (lw-euler-derivative-curvature rate height radius) (lw-euler-derivative-modulus rate height radius error)) (/ error 4))))
 :hints (("Goal"
  :use (lw-euler-derivative-curvature-positive
        (:instance lw-euler-rounding-precision-valid (cost (lw-euler-derivative-curvature rate height radius)) (error (/ error 2)))
        (:instance lw-edm-multiply-order (a (lw-euler-derivative-modulus rate height radius error))
         (b (lw-euler-rounding-precision (lw-euler-derivative-curvature rate height radius) (/ error 2))) (factor (lw-euler-derivative-curvature rate height radius))))
  :in-theory (union-theories
   '(lw-euler-derivative-modulus min lw-edm-left-commutes lw-edm-left-distributes lw-edm-fold-constants lw-edm-times-negative lw-edm-negative-times lw-edm-zero-times lw-edm-minus-one lw-edm-double-negative lw-edm-add-cancel lw-edm-double lw-edm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-derivative-step-budget
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error) (rationalp delta) (< 0 delta) (<= delta (lw-euler-derivative-modulus rate height radius error)))
  (and (<= delta (/ radius 2)) (rationalp (* error delta)) (< 0 (* error delta))
       (<= (+ (* (lw-euler-derivative-curvature rate height radius) delta delta) (* 3/4 error delta)) (* error delta))))
 :hints (("Goal"
  :use (lw-euler-derivative-curvature-positive lw-euler-derivative-modulus-valid
        (:instance lw-edm-positive-product (a error) (b delta))
        (:instance lw-edm-multiply-order (a delta) (b (lw-euler-derivative-modulus rate height radius error)) (factor (lw-euler-derivative-curvature rate height radius)))
        (:instance lw-edm-multiply-order (a (* (lw-euler-derivative-curvature rate height radius) delta)) (b (/ error 4)) (factor delta)))
  :in-theory (union-theories
   '( lw-edm-left-commutes lw-edm-left-distributes lw-edm-fold-constants lw-edm-times-negative lw-edm-negative-times lw-edm-zero-times lw-edm-minus-one lw-edm-double-negative lw-edm-add-cancel lw-edm-double lw-edm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-refined-linear-increment
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error) (rationalp delta) (< 0 delta) (<= delta (lw-euler-derivative-modulus rate height radius error))
               (lw-complex-diskp offset delta)
               (rationalp shifted-error) (< 0 shifted-error) (<= shifted-error (* error delta))
               (rationalp center-error) (< 0 center-error) (<= center-error (* error delta))
               (rationalp derivative-error) (< 0 derivative-error) (<= derivative-error (/ error 4)))
  (lw-complex-diskp (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-local-coefficient-value rate height radius 1 derivative-error) offset) (* error delta)))
 :hints (("Goal"
  :use (lw-euler-derivative-step-budget
        lw-complex-euler-quadratic-increment
        (:instance lw-edm-multiply-order (a derivative-error) (b (/ error 4)) (factor delta))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) shifted-error) (lw-complex-euler-continuation-value rate height center-error) (lw-complex-euler-local-coefficient-value rate height radius 1 derivative-error) offset))
         (radius (+ (* (lw-euler-derivative-curvature rate height radius) delta delta) (* 1/4 shifted-error) (* 1/4 center-error) (* derivative-error delta)))
         (cap (* error delta))))
  :in-theory (union-theories
   '( lw-edm-left-commutes lw-edm-left-distributes lw-edm-fold-constants lw-edm-times-negative lw-edm-negative-times lw-edm-zero-times lw-edm-minus-one lw-edm-double-negative lw-edm-add-cancel lw-edm-double lw-edm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-computed-linear-increment
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error) (rationalp delta) (< 0 delta) (<= delta (lw-euler-derivative-modulus rate height radius error))
               (lw-complex-diskp offset delta))
  (lw-complex-diskp
   (lw-complex-linear-remainder
    (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) (* error delta))
    (lw-complex-euler-continuation-value rate height (* error delta))
    (lw-complex-euler-local-coefficient-value rate height radius 1 (/ error 4)) offset)
   (* error delta)))
 :hints (("Goal"
  :use (lw-euler-derivative-step-budget
        (:instance lw-complex-euler-refined-linear-increment
         (shifted-error (* error delta)) (center-error (* error delta)) (derivative-error (/ error 4))))
  :in-theory (union-theories
   '( lw-edm-left-commutes lw-edm-left-distributes lw-edm-fold-constants lw-edm-times-negative lw-edm-negative-times lw-edm-zero-times lw-edm-minus-one lw-edm-double-negative lw-edm-add-cancel lw-edm-double lw-edm-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

