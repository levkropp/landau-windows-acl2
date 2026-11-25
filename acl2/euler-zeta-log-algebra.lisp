(in-package "ACL2")

(include-book "euler-zeta-clearance")
(include-book "zeta-euler-log-derivative")

; Exact finite factors connect the Euler and zeta evaluator families.
; All nested requests remain independently computed.

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
 lw-euler-value-clearance-check lw-euler-value-clearance-lower)))

(local (defthm lw-eza-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eza-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eza-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eza-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eza-times-negative (a b) (b a)))
                 :in-theory (disable lw-eza-times-negative)))))

(local (defthm lw-eza-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eza-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eza-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eza-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eza-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eza-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eza-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eza-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eza-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eza-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eza-left-commutes)))))

(local (defthm lw-eza-pair-equality
 (implies (equal left right)
  (and (equal (car left) (car right)) (equal (cdr left) (cdr right))))
 :rule-classes nil))

(local (defthm lw-eza-shift-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0))))
  (and (lw-complexp (cons (- rate 1) height)) (not (equal (cons (- rate 1) height) (cons 0 0)))))
 :hints (("Goal"
  :use ((:instance lw-eza-pair-equality (left (cons (- rate 1) height)) (right (cons 0 0))))
  :in-theory (union-theories
 '(lw-complexp lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-zeta-log-nested-request-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-euler-log-derivative-request rate height radius error)) (< 0 (lw-zeta-euler-log-derivative-request rate height radius error)) (<= (lw-zeta-euler-log-derivative-request rate height radius error) 1) (<= (lw-zeta-euler-log-derivative-request rate height radius error) error)
       (rationalp (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (< 0 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (<= (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-zeta-euler-log-derivative-request rate height radius error))
       (rationalp (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (< 0 (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (<= (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-zeta-euler-log-derivative-request rate height radius error))))
 :hints (("Goal"
  :use (lw-zeta-euler-log-derivative-request-data lw-zeta-euler-inverse-cap-data
        (:instance lw-zeta-derivative-request-data (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-zeta-euler-point-error-data (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-eza-multiply-order (a 1) (b (* 2 (lw-zeta-euler-inverse-cap rate height))) (factor (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-eza-multiply-order (a 1) (b (lw-zeta-euler-inverse-cap rate height)) (factor (lw-zeta-euler-point-error rate height (lw-zeta-euler-log-derivative-request rate height radius error)))))
  :in-theory (union-theories
 '( lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-zeta-value-product
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (rationalp error) (< 0 error))
  (equal (lw-complex-mul (cons (- rate 1) height) (lw-complex-zeta-euler-value rate height error))
   (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height error))))
 :hints (("Goal"
  :use (lw-eza-shift-data lw-zeta-euler-point-error-data
        (:instance lw-complex-euler-continuation-value-rational
         (error (lw-zeta-euler-point-error rate height error)))
        (:instance lw-complex-reciprocal-cancel-product
         (a (cons (- rate 1) height)) (b (lw-complex-euler-continuation-value rate height (lw-zeta-euler-point-error rate height error)))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-value lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-zeta-derivative-product
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (not (and (equal rate 1) (equal height 0)))
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (equal (lw-complex-mul (cons (- rate 1) height) (lw-complex-zeta-euler-derivative-value rate height radius error))
   (lw-complex-sub
    (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error))
    (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error)))))
 :hints (("Goal"
  :use (lw-eza-shift-data lw-zeta-derivative-request-data
        (:instance lw-complex-euler-local-coefficient-rational
         (index 1) (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-operations-rational
         (left (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error)))
         (right (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error))) (factor 1))
        (:instance lw-complex-reciprocal-cancel-product (a (cons (- rate 1) height))
         (b (lw-complex-sub
          (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error))
          (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error))))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-derivative-value lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(local (defthm lw-eza-add-residual
 (implies (and (lw-complexp a) (lw-complexp z) (lw-complexp zD))
  (and (equal (lw-complex-add z (lw-complex-sub a zD))
              (lw-complex-add a (lw-complex-sub z zD)))
       (equal (lw-complex-sub a (lw-complex-add z (lw-complex-sub a zD)))
              (lw-complex-sub zD z))))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defun lw-euler-zeta-log-factor-numerator (rate height radius error)
 (lw-complex-add (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-complex-mul (cons (- rate 1) height) (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius error)))))

(local (in-theory (disable lw-euler-zeta-log-factor-numerator)))

(defthm lw-euler-zeta-log-factor-numerator-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (and (lw-complexp (lw-euler-zeta-log-factor-numerator rate height radius error))
       (equal (lw-euler-zeta-log-factor-numerator rate height radius error) (lw-complex-add (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error)) (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))))
       (equal (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (lw-euler-zeta-log-factor-numerator rate height radius error)) (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error))))))
 :hints (("Goal"
  :use (lw-euler-zeta-log-nested-request-data
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-euler-zeta-derivative-product (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-eza-add-residual (a (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error)))) (z (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (zD (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height (lw-zeta-euler-log-derivative-request rate height radius error))))))
  :in-theory (union-theories
 '(lw-euler-zeta-log-factor-numerator lw-complexp lw-complex-add lw-complex-sub lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eza-unit-numerator
 (implies (lw-complexp point)
  (equal (lw-complex-quotient (cons 1 0) point) (lw-complex-reciprocal point)))
 :hints (("Goal"
  :use (lw-complex-reciprocal-rational)
  :in-theory (union-theories
 '(lw-complex-quotient lw-complex-mul-one lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-eza-negated-quotient
 (implies (and (lw-complexp numerator) (lw-complexp denominator))
  (equal (lw-complex-quotient (lw-complex-scale -1 numerator) denominator)
         (lw-complex-scale -1 (lw-complex-quotient numerator denominator))))
 :hints (("Goal"
  :use ((:instance lw-complex-reciprocal-rational (point denominator)))
  :in-theory (union-theories
 '(lw-complex-quotient lw-complexp lw-complex-mul lw-complex-scale lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-eza-negative-log-complement
 (implies (and (lw-complexp point) (lw-complexp numerator) (lw-complexp denominator))
  (equal
   (lw-complex-sub point (lw-complex-quotient (lw-complex-scale -1 numerator) denominator))
   (lw-complex-add point (lw-complex-quotient numerator denominator))))
 :hints (("Goal"
  :use (lw-eza-negated-quotient lw-complex-quotient-rational)
  :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-add lw-complex-scale lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-zeta-log-factor-quotient
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (equal (lw-complex-quotient (lw-euler-zeta-log-factor-numerator rate height radius error) (lw-complex-mul (cons (- rate 1) height) (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error))))
         (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-zeta-euler-log-derivative-value rate height radius error))))
 :hints (("Goal"
  :use (lw-euler-zeta-log-nested-request-data lw-eza-shift-data
        lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-euler-clearance (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-complex-zeta-euler-derivative-rational (error (lw-zeta-euler-log-derivative-request rate height radius error)))
        (:instance lw-eza-unit-numerator (point (cons (- rate 1) height)))
        (:instance lw-complex-quotient-product-rule
         (p (cons (- rate 1) height)) (h (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error))) (dp (cons 1 0)) (dh (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius error))))
        (:instance lw-eza-negative-log-complement
         (point (lw-complex-reciprocal (cons (- rate 1) height))) (numerator (lw-complex-zeta-euler-derivative-value rate height radius (lw-zeta-euler-log-derivative-request rate height radius error))) (denominator (lw-complex-zeta-euler-value rate height (lw-zeta-euler-log-derivative-request rate height radius error)))))
  :in-theory (union-theories
 '(lw-euler-zeta-log-factor-numerator lw-complex-zeta-euler-log-derivative-value lw-complex-mul-one (:executable-counterpart lw-complexp) lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


