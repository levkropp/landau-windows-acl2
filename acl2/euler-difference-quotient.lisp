(in-package "ACL2")

(include-book "euler-derivative-modulus")
(include-book "complex-quotients")

; Every nonzero rational complex step has computed reciprocal clearance.
; The Euler difference quotient converges with an explicit uniform modulus.

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

(local (in-theory (disable lw-euler-derivative-modulus lw-euler-derivative-curvature
 lw-complex-euler-continuation-value lw-complex-euler-local-coefficient-value
 lw-complex-l1 lw-complex-norm-square lw-complex-reciprocal lw-complex-quotient lw-complex-linear-remainder)))

(local (defthm lw-edq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edq-times-negative (a b) (b a)))
                 :in-theory (disable lw-edq-times-negative)))))

(local (defthm lw-edq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edq-left-commutes)))))

(local (defthm lw-edq-square-nonnegative
 (implies (rationalp value) (<= 0 (* value value)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-l1-clearance
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
  (and (rationalp (lw-complex-l1 point)) (< 0 (lw-complex-l1 point))
       (lw-complex-diskp point (lw-complex-l1 point))
       (<= (* 1/4 (lw-complex-l1 point) (lw-complex-l1 point)) (lw-complex-norm-square point))))
 :hints (("Goal"
  :cases ((<= 0 (car point)) (<= 0 (cdr point)))
  :use (lw-complex-l1-bound
        (:instance lw-edq-square-nonnegative (value (car point)))
        (:instance lw-edq-square-nonnegative (value (cdr point)))
        (:instance lw-edq-square-nonnegative (value (- (car point) (cdr point))))
        (:instance lw-edq-square-nonnegative (value (+ (car point) (cdr point)))))
  :in-theory (union-theories
   '(lw-complexp lw-complex-l1 lw-complex-norm-square abs lw-edq-left-commutes lw-edq-left-distributes lw-edq-fold-constants lw-edq-times-negative lw-edq-negative-times lw-edq-zero-times lw-edq-minus-one lw-edq-double-negative lw-edq-add-cancel lw-edq-double lw-edq-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-complex-l1-reciprocal-bound
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
  (lw-complex-diskp (lw-complex-reciprocal point) (/ (* 1/2 (lw-complex-l1 point)))))
 :hints (("Goal"
  :use (lw-complex-l1-clearance
        (:instance lw-complex-reciprocal-disk-bound (lower (* 1/2 (lw-complex-l1 point)))))
  :in-theory (union-theories
   '( lw-edq-left-commutes lw-edq-left-distributes lw-edq-fold-constants lw-edq-times-negative lw-edq-negative-times lw-edq-zero-times lw-edq-minus-one lw-edq-double-negative lw-edq-add-cancel lw-edq-double lw-edq-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-linear-quotient-identity
 (implies (and (lw-complexp value) (lw-complexp anchor) (lw-complexp slope)
               (lw-complexp point) (not (equal point (cons 0 0))))
  (equal
   (lw-complex-sub (lw-complex-quotient (lw-complex-sub value anchor) point) slope)
   (lw-complex-mul (lw-complex-linear-remainder value anchor slope point) (lw-complex-reciprocal point))))
 :hints (("Goal"
  :use ((:instance lw-complex-operations-rational (left value) (right anchor) (factor 1))
        lw-complex-linear-remainder-rational
        (:instance lw-complex-operations-rational (left slope) (right point) (factor 1))
        (:instance lw-complex-reciprocal-rational)
        (:instance lw-complex-reciprocal-cancel-product (a point) (b slope))
        (:instance lw-complex-mul-commutative (left slope) (right point))
        (:instance lw-complex-mul-commutative
         (left (lw-complex-sub value anchor)) (right (lw-complex-reciprocal point)))
        (:instance lw-complex-mul-commutative
         (left (lw-complex-sub (lw-complex-sub value anchor) (lw-complex-mul slope point)))
         (right (lw-complex-reciprocal point)))
        (:instance lw-complex-mul-subtract (a (lw-complex-reciprocal point))
         (b (lw-complex-sub value anchor)) (c (lw-complex-mul slope point))))
  :in-theory (union-theories
   '(lw-complex-linear-remainder lw-complex-quotient lw-edq-left-commutes lw-edq-left-distributes lw-edq-fold-constants lw-edq-times-negative lw-edq-negative-times lw-edq-zero-times lw-edq-minus-one lw-edq-double-negative lw-edq-add-cancel lw-edq-double lw-edq-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-computed-difference-quotient
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error) (lw-complexp offset) (not (equal offset (cons 0 0)))
               (<= (lw-complex-l1 offset) (lw-euler-derivative-modulus rate height radius (/ error 2))))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-quotient (lw-complex-sub (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) (* 1/2 error (lw-complex-l1 offset))) (lw-complex-euler-continuation-value rate height (* 1/2 error (lw-complex-l1 offset)))) offset) (lw-complex-euler-local-coefficient-value rate height radius 1 (/ error 8)))
   error))
 :hints (("Goal"
  :use ((:instance lw-complex-l1-clearance (point offset))
        (:instance lw-complex-l1-reciprocal-bound (point offset))
        (:instance lw-euler-derivative-modulus-valid (error (/ error 2)))
        (:instance lw-complex-disk-enlarge (point offset) (radius (lw-complex-l1 offset)) (cap radius))
        (:instance lw-euler-disk-point-data)
        (:instance lw-edq-positive-product (a (/ error 2)) (b (lw-complex-l1 offset)))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car offset))) (height (+ height (cdr offset))) (error (* 1/2 error (lw-complex-l1 offset))))
        (:instance lw-complex-euler-continuation-value-rational (error (* 1/2 error (lw-complex-l1 offset))))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (/ error 8)))
        (:instance lw-complex-euler-computed-linear-increment (error (/ error 2)) (delta (lw-complex-l1 offset)))
        (:instance lw-complex-linear-quotient-identity (value (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) (* 1/2 error (lw-complex-l1 offset)))) (anchor (lw-complex-euler-continuation-value rate height (* 1/2 error (lw-complex-l1 offset)))) (slope (lw-complex-euler-local-coefficient-value rate height radius 1 (/ error 8))) (point offset))
        (:instance lw-complex-mul-disk (left (lw-complex-linear-remainder (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) (* 1/2 error (lw-complex-l1 offset))) (lw-complex-euler-continuation-value rate height (* 1/2 error (lw-complex-l1 offset))) (lw-complex-euler-local-coefficient-value rate height radius 1 (/ error 8)) offset)) (right (lw-complex-reciprocal offset))
         (radius (* 1/2 error (lw-complex-l1 offset))) (other-radius (/ (* 1/2 (lw-complex-l1 offset)))))
        (:instance lw-edq-inverse-factor (divisor (* 1/2 (lw-complex-l1 offset))) (coefficient error)))
  :in-theory (union-theories
   '( lw-edq-left-commutes lw-edq-left-distributes lw-edq-fold-constants lw-edq-times-negative lw-edq-negative-times lw-edq-zero-times lw-edq-minus-one lw-edq-double-negative lw-edq-add-cancel lw-edq-double lw-edq-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

