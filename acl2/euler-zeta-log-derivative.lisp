(in-package "ACL2")

(include-book "euler-zeta-log-algebra")

; Identify the two actual logarithmic-derivative Cauchy families.
; Finite product identities and division bounds give the comparison.

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
 lw-complex-euler-local-coefficient-value lw-complex-zeta-euler-value
 lw-zeta-euler-point-error lw-zeta-euler-inverse-cap lw-zeta-derivative-request
 lw-zeta-euler-log-derivative-request lw-complex-zeta-euler-derivative-value
 lw-complex-zeta-euler-log-derivative-value lw-complex-quotient
 lw-euler-value-clearance-check lw-euler-value-clearance-lower
 lw-euler-log-derivative-numerator-cap lw-euler-log-derivative-cost
 lw-complex-euler-log-derivative-value lw-euler-zeta-log-factor-numerator)))

(local (defthm lw-ezl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ezl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ezl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ezl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ezl-times-negative (a b) (b a)))
                 :in-theory (disable lw-ezl-times-negative)))))

(local (defthm lw-ezl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ezl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ezl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ezl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ezl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ezl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ezl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ezl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ezl-left-commutes)))))

(local (defthm lw-ezl-weights
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate))
  (and (rationalp (/ (lw-euler-value-clearance-lower rate height anchor-error))) (< 0 (/ (lw-euler-value-clearance-lower rate height anchor-error)))
       (rationalp (lw-euler-log-derivative-numerator-cap rate height radius)) (< 0 (lw-euler-log-derivative-numerator-cap rate height radius)) (rationalp (lw-euler-log-derivative-cost rate height radius anchor-error)) (< 0 (lw-euler-log-derivative-cost rate height radius anchor-error))
       (rationalp (* (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error)))) (< 0 (* (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error))))))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data
        (:instance lw-euler-log-derivative-numerator-cap-data (error 1))
        lw-euler-log-derivative-cost-valid
        (:instance lw-reciprocal-positive (value (lw-euler-value-clearance-lower rate height anchor-error)))
        (:instance lw-ezl-positive-product (a (/ (lw-euler-value-clearance-lower rate height anchor-error))) (b (/ (lw-euler-value-clearance-lower rate height anchor-error))))
        (:instance lw-ezl-positive-product (a (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2)) (b (* (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error))))))
  :in-theory (union-theories
 '( lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-zeta-log-comparison-cost (rate height radius anchor-error)
 (+ (lw-euler-log-derivative-cost rate height radius anchor-error) (* 2 (/ (lw-euler-value-clearance-lower rate height anchor-error))) (* 2 (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error)))))

(local (in-theory (disable lw-euler-zeta-log-comparison-cost)))

(defthm lw-euler-zeta-log-comparison-cost-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate))
  (and (rationalp (lw-euler-zeta-log-comparison-cost rate height radius anchor-error)) (< 0 (lw-euler-zeta-log-comparison-cost rate height radius anchor-error))))
 :hints (("Goal" :use (lw-ezl-weights)
  :in-theory (union-theories
 '(lw-euler-zeta-log-comparison-cost lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ezl-finite-factor-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error) (<= error 1) (<= error (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error))))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (lw-complex-euler-continuation-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius error))) (+ (* (/ (lw-euler-value-clearance-lower rate height anchor-error)) (+ (lw-zeta-euler-log-derivative-request rate height radius error) (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (* (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (+ (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error)))))))
 :hints (("Goal"
  :use (lw-euler-zeta-log-nested-request-data
        lw-euler-zeta-log-factor-numerator-data lw-euler-zeta-log-factor-quotient
        lw-euler-value-clearance-data
        (:instance lw-euler-zeta-value-product (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-euler-value-clearance (request (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-euler-value-clearance (request (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-euler-log-derivative-numerator-cap-data (error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-zeta-euler-value-cauchy (left-error (lw-zeta-euler-log-derivative-request rate height radius error)) (right-error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-zeta-euler-value-cauchy (left-error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (right-error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-euler-continuation-value-cauchy (left-error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (right-error (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))) (radius (+ (lw-zeta-euler-log-derivative-request rate height radius error) (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (cap 2))
        (:instance lw-complex-add-disk
         (left (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (right (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))) (radius (lw-euler-log-derivative-numerator-cap rate height radius)) (other-radius 2))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (denominator (lw-complex-euler-continuation-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
         (approximate-numerator (lw-euler-zeta-log-factor-numerator rate height radius error)) (approximate-denominator (lw-complex-mul (cons (- rate 1) height) (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
         (left-clearance (lw-euler-value-clearance-lower rate height anchor-error)) (right-clearance (lw-euler-value-clearance-lower rate height anchor-error)) (numerator-cap (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2))
         (numerator-error (+ (lw-zeta-euler-log-derivative-request rate height radius error) (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (denominator-error (+ (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error))))))
  :in-theory (union-theories
 '( lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-ezl-three-budget
 (implies (and (rationalp h) (<= 0 h) (rationalp b) (<= 0 b) (rationalp j) (<= 0 j)
               (rationalp q) (rationalp v) (rationalp p) (rationalp error)
               (<= q error) (<= v error) (<= p error))
  (<= (+ (* h q) (* b (+ v q)) (* j (+ q p)))
      (* (+ h (* 2 b) (* 2 j)) error)))
 :hints (("Goal"
  :use ((:instance lw-ezl-multiply-order (a q) (b error) (factor h))
        (:instance lw-ezl-multiply-order (a (+ v q)) (b (* 2 error)) (factor b))
        (:instance lw-ezl-multiply-order (a (+ q p)) (b (* 2 error)) (factor j)))
  :in-theory (union-theories
 '( lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ezl-with-auxiliary-error
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp error) (< 0 error) (<= error 1) (<= error (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error))))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius error))) (+ euler-error (* (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) error))))
 :hints (("Goal"
  :use (lw-euler-zeta-log-nested-request-data lw-euler-value-clearance-data
        lw-ezl-weights lw-euler-zeta-log-comparison-cost-valid
        lw-zeta-euler-inverse-cap-data lw-ezl-finite-factor-comparison
        (:instance lw-complex-euler-log-derivative-rational (error euler-error))
        lw-complex-zeta-euler-log-derivative-rational
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-euler-continuation-value-rational (error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-zeta-euler-log-derivative-value rate height radius error)) (factor 1))
        (:instance lw-complex-euler-log-derivative-common-comparison (error euler-error) (request (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-ezl-three-budget (h (lw-euler-log-derivative-cost rate height radius anchor-error)) (b (/ (lw-euler-value-clearance-lower rate height anchor-error))) (j (* (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error)))) (q (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (v (lw-zeta-euler-log-derivative-request rate height radius error)) (p (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error)) (middle (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (lw-complex-euler-continuation-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))) (right (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius error)))
         (radius (+ euler-error (* (lw-euler-log-derivative-cost rate height radius anchor-error) (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))) (other-radius (+ (* (/ (lw-euler-value-clearance-lower rate height anchor-error)) (+ (lw-zeta-euler-log-derivative-request rate height radius error) (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (* (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (+ (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error)))))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius error))))
         (radius (+ euler-error (* (lw-euler-log-derivative-cost rate height radius anchor-error) (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (+ (* (/ (lw-euler-value-clearance-lower rate height anchor-error)) (+ (lw-zeta-euler-log-derivative-request rate height radius error) (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (* (+ (lw-euler-log-derivative-numerator-cap rate height radius) 2) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error)) (+ (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error))))))) (cap (+ euler-error (* (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) error)))))
  :in-theory (union-theories
 '(lw-euler-zeta-log-comparison-cost lw-complex-quotient-rational lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-ezl-complement-difference
 (implies (and (lw-complexp point) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-sub point left) (lw-complex-sub point right))
         (lw-complex-scale -1 (lw-complex-sub left right))))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ezl-target-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp euler-error) (< 0 euler-error) (rationalp zeta-error) (< 0 zeta-error)
               (rationalp error) (< 0 error) (<= error 1) (<= error (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error))))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error)))
   (+ euler-error zeta-error (* (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1) error))))
 :hints (("Goal"
  :use (lw-ezl-with-auxiliary-error lw-euler-zeta-log-comparison-cost-valid
        lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-euler-log-derivative-rational (error euler-error))
        lw-complex-zeta-euler-log-derivative-rational
        (:instance lw-complex-zeta-euler-log-derivative-rational (error zeta-error))
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-zeta-euler-log-derivative-value rate height radius error)) (factor 1))
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error)) (factor 1))
        (:instance lw-complex-zeta-euler-log-derivative-cauchy (left-error error) (right-error zeta-error))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-zeta-euler-log-derivative-value rate height radius error) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))) (radius (+ error zeta-error)) (factor -1))
        (:instance lw-complex-difference-triangle (left (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error)) (middle (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius error))) (right (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error)))
         (radius (+ euler-error (* (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) error))) (other-radius (+ error zeta-error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))))
         (radius (+ euler-error (* (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) error) error zeta-error))
         (cap (+ euler-error zeta-error (* (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1) error)))))
  :in-theory (union-theories
 '(lw-ezl-complement-difference (:executable-counterpart abs) lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-euler-zeta-log-comparison-request (rate height radius anchor-error margin)
 (min (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error)) (lw-euler-rounding-precision (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1) (* 2 margin))))

(local (in-theory (disable lw-euler-zeta-log-comparison-request)))

(defthm lw-euler-zeta-log-comparison-request-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp margin) (< 0 margin))
  (and (rationalp (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin)) (< 0 (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin)) (<= (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin) 1)
       (<= (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin) (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error))) (<= (* (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1) (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin)) margin)))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data lw-euler-zeta-log-comparison-cost-valid
        (:instance lw-euler-rounding-precision-valid (cost (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1)) (error (* 2 margin)))
        (:instance lw-ezl-multiply-order (a (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin))
         (b (lw-euler-rounding-precision (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1) (* 2 margin))) (factor (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1))))
  :in-theory (union-theories
 '(lw-euler-zeta-log-comparison-request min lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ezl-with-margin
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp euler-error) (< 0 euler-error) (rationalp zeta-error) (< 0 zeta-error)
               (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))) (+ euler-error zeta-error margin)))
 :hints (("Goal"
  :use (lw-euler-zeta-log-comparison-request-data lw-euler-zeta-log-comparison-cost-valid
        (:instance lw-ezl-target-comparison (error (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))))
         (radius (+ euler-error zeta-error (* (+ (lw-euler-zeta-log-comparison-cost rate height radius anchor-error) 1) (lw-euler-zeta-log-comparison-request rate height radius anchor-error margin))))
         (cap (+ euler-error zeta-error margin))))
  :in-theory (union-theories
 '( lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-zeta-log-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp euler-error) (< 0 euler-error) (rationalp zeta-error) (< 0 zeta-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))) (+ euler-error zeta-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))) (+ euler-error zeta-error)))
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-euler-log-derivative-rational (error euler-error))
        (:instance lw-complex-zeta-euler-log-derivative-rational (error zeta-error))
        (:instance lw-complex-operations-rational (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error)) (factor 1))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error)) (right (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error)))) (radius (+ euler-error zeta-error)) (cost 1))
        (:instance lw-ezl-with-margin
         (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error euler-error) (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))) (+ euler-error zeta-error) 1))))
  :in-theory (union-theories
 '( lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-zeta-log-right-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp euler-error) (< 0 euler-error) (rationalp zeta-error) (< 0 zeta-error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-euler-log-derivative-value rate height radius (lw-euler-zeta-clearance-request rate height) euler-error)
    (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius zeta-error))) (+ euler-error zeta-error)))
 :hints (("Goal"
  :use (lw-euler-zeta-clearance-check
        (:instance lw-complex-euler-zeta-log-agreement (anchor-error (lw-euler-zeta-clearance-request rate height))))
  :in-theory (union-theories
 '( lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-zeta-log-computed-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-euler-log-derivative-value rate height radius (lw-euler-zeta-clearance-request rate height) (/ error 2))
    (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius (/ error 2))))
   error))
 :hints (("Goal"
  :use ((:instance lw-complex-euler-zeta-log-right-agreement (euler-error (/ error 2)) (zeta-error (/ error 2))))
  :in-theory (union-theories
 '( lw-ezl-left-commutes lw-ezl-left-distributes lw-ezl-fold-constants lw-ezl-times-negative lw-ezl-negative-times lw-ezl-zero-times lw-ezl-minus-one lw-ezl-double-negative lw-ezl-add-cancel lw-ezl-double lw-ezl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



