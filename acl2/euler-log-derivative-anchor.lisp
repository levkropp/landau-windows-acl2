(in-package "ACL2")
(include-book "euler-log-derivative")
(include-book "euler-anchor-derivative")

; Calibrate the checked actual V'/V name at one.
; The denominator check is generated from V(1)=1.

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
(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))
(local (in-theory (disable lw-complex-euler-continuation-value
 lw-complex-euler-local-coefficient-value lw-euler-uniform-coefficient-cap
 lw-euler-value-clearance-size lw-euler-value-clearance-lower
 lw-euler-value-clearance-check lw-complex-quotient
 lw-euler-log-derivative-numerator-cap lw-euler-log-derivative-cost
 lw-euler-log-derivative-request lw-complex-euler-log-derivative-value)))
(local (defthm lw-ela-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ela-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ela-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ela-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ela-times-negative (a b) (b a)))
                 :in-theory (disable lw-ela-times-negative)))))

(local (defthm lw-ela-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ela-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ela-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ela-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ela-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ela-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ela-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ela-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ela-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ela-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ela-left-commutes)))))

(local (defthm lw-ela-reconstruction
 (implies (lw-complexp point) (equal (cons (car point) (cdr point)) point))
 :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-ela-unit-quotient
 (implies (lw-complexp point)
  (equal (lw-complex-quotient point (cons 1 0)) point))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complex-quotient lw-complex-mul lw-complex-reciprocal lw-complex-conjugate lw-complex-norm-square lw-complex-scale lw-complexp lw-ela-reconstruction lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ela-self-difference
 (implies (lw-complexp point)
  (equal (lw-complex-sub point point) (cons 0 0)))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ela-zero-disk
 (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-diskp lw-diskp lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ela-unit-denominator-comparison
 (implies (and (lw-complexp numerator) (lw-complexp denominator)
               (rationalp lower) (< 0 lower)
               (<= (* lower lower) (lw-complex-norm-square denominator))
               (rationalp numerator-cap) (lw-complex-diskp numerator numerator-cap)
               (rationalp value-error)
               (lw-complex-diskp (lw-complex-sub denominator (cons 1 0)) value-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-quotient numerator denominator) numerator)
   (* numerator-cap (/ lower) value-error)))
 :hints (("Goal"
  :use ((:instance lw-complex-quotient-difference-bound
         (approximate-numerator numerator) (approximate-denominator (cons 1 0))
         (left-clearance lower) (right-clearance 1)
         (numerator-error 0) (denominator-error value-error)))
  :in-theory (union-theories
 '(lw-ela-unit-quotient lw-ela-self-difference lw-ela-zero-disk (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-norm-square) lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ela-cost-majorant
 (implies (and (rationalp lower) (< 0 lower) (<= lower 1)
               (rationalp mass) (< 0 mass))
  (<= (+ 1 (* 1/4 mass (/ lower)))
      (+ (/ lower) (* mass (/ lower) (/ lower)))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-antitone (left lower) (right 1))
        (:instance lw-reciprocal-positive (value lower))
        (:instance lw-ela-positive-product (a mass) (b (/ lower)))
        (:instance lw-ela-multiply-order
         (a 1/4) (b (/ lower)) (factor (* mass (/ lower)))))
  :in-theory (union-theories
 '( lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))


(defthm lw-euler-log-derivative-anchor-check
 (and (lw-euler-value-clearance-check 1 0 1/64)
      (<= 255/1024 (lw-euler-value-clearance-lower 1 0 1/64))
      (<= (lw-euler-value-clearance-lower 1 0 1/64) 1/2))
 :hints (("Goal"
  :use ((:instance lw-euler-value-anchor-clearance (anchor-error 1/64)))
  :in-theory (union-theories
 '( lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-log-derivative-anchor
 (implies (and (rationalp anchor-error) (< 0 anchor-error) (<= anchor-error 1/64)
               (rationalp radius) (< 0 radius) (< radius 1)
               (rationalp error) (< 0 error)
               (rationalp gamma-error) (< 0 gamma-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value 1 0 radius anchor-error error) (cons (car (lw-euler-bounds gamma-error)) 0)) (+ error gamma-error)))
 :hints (("Goal"
  :use (lw-euler-value-anchor-clearance
        (:instance lw-euler-value-clearance-data (rate 1) (height 0))
        (:instance lw-euler-log-derivative-cost-valid (rate 1) (height 0))
        (:instance lw-euler-log-derivative-request-data (rate 1) (height 0))
        (:instance lw-euler-log-derivative-numerator-cap-data (rate 1) (height 0) (error (lw-euler-log-derivative-request 1 0 radius anchor-error error)))
        (:instance lw-complex-euler-value-clearance (rate 1) (height 0) (request (lw-euler-log-derivative-request 1 0 radius anchor-error error)))
        (:instance lw-complex-euler-continuation-value-rational (rate 1) (height 0) (error (lw-euler-log-derivative-request 1 0 radius anchor-error error)))
        (:instance lw-complex-euler-local-coefficient-rational (rate 1) (height 0) (index 1) (error (lw-euler-log-derivative-request 1 0 radius anchor-error error)))
        (:instance lw-complex-euler-log-derivative-rational (rate 1) (height 0))
        (:instance lw-complex-euler-anchor-value (error (lw-euler-log-derivative-request 1 0 radius anchor-error error)))
        (:instance lw-complex-euler-anchor-derivative (coefficient-error (lw-euler-log-derivative-request 1 0 radius anchor-error error)))
        (:instance lw-euler-bounds-interval (epsilon gamma-error))
        (:instance lw-ela-unit-denominator-comparison
         (numerator (lw-complex-euler-local-coefficient-value 1 0 radius 1 (lw-euler-log-derivative-request 1 0 radius anchor-error error))) (denominator (lw-complex-euler-continuation-value 1 0 (lw-euler-log-derivative-request 1 0 radius anchor-error error))) (lower (lw-euler-value-clearance-lower 1 0 anchor-error))
         (numerator-cap (lw-euler-log-derivative-numerator-cap 1 0 radius)) (value-error (* 1/4 (lw-euler-log-derivative-request 1 0 radius anchor-error error))))
        (:instance lw-ela-cost-majorant (lower (lw-euler-value-clearance-lower 1 0 anchor-error)) (mass (lw-euler-log-derivative-numerator-cap 1 0 radius)))
        (:instance lw-ela-multiply-order (a (+ 1 (* 1/4 (lw-euler-log-derivative-numerator-cap 1 0 radius) (/ (lw-euler-value-clearance-lower 1 0 anchor-error))))) (b (lw-euler-log-derivative-cost 1 0 radius anchor-error)) (factor (lw-euler-log-derivative-request 1 0 radius anchor-error error)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-log-derivative-value 1 0 radius anchor-error error)) (middle (lw-complex-euler-local-coefficient-value 1 0 radius 1 (lw-euler-log-derivative-request 1 0 radius anchor-error error))) (right (cons (car (lw-euler-bounds gamma-error)) 0))
         (radius (* (lw-euler-log-derivative-numerator-cap 1 0 radius) (/ (lw-euler-value-clearance-lower 1 0 anchor-error)) (* 1/4 (lw-euler-log-derivative-request 1 0 radius anchor-error error)))) (other-radius (+ (lw-euler-log-derivative-request 1 0 radius anchor-error error) gamma-error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value 1 0 radius anchor-error error) (cons (car (lw-euler-bounds gamma-error)) 0)))
         (radius (+ (* (lw-euler-log-derivative-numerator-cap 1 0 radius) (/ (lw-euler-value-clearance-lower 1 0 anchor-error)) (* 1/4 (lw-euler-log-derivative-request 1 0 radius anchor-error error))) (lw-euler-log-derivative-request 1 0 radius anchor-error error) gamma-error))
         (cap (+ error gamma-error))))
  :in-theory (union-theories
 '(lw-complex-euler-log-derivative-value lw-euler-log-derivative-cost lw-complex-quotient-gain lw-complexp lw-intervalp lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-log-derivative-anchor-computed
 (implies (and (rationalp radius) (< 0 radius) (< radius 1) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-log-derivative-value 1 0 radius 1/64 (/ error 2))
    (cons (car (lw-euler-bounds (/ error 2))) 0))
   error))
 :hints (("Goal"
  :use ((:instance lw-complex-euler-log-derivative-anchor
         (anchor-error 1/64) (error (/ error 2)) (gamma-error (/ error 2))))
  :in-theory (union-theories
 '( lw-ela-left-commutes lw-ela-left-distributes lw-ela-fold-constants lw-ela-times-negative lw-ela-negative-times lw-ela-zero-times lw-ela-minus-one lw-ela-double-negative lw-ela-add-cancel lw-ela-double lw-ela-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


