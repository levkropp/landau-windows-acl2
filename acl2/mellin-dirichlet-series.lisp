(in-package "ACL2")

(include-book "mellin-series-precision")
(include-book "dirichlet-transform")

; Arithmetic identity of the actual improper Mellin and normalized
; Dirichlet Cauchy names, with a fully computed auxiliary request.

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

(local (defthm lw-mds-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mds-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mds-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mds-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mds-times-negative (a b) (b a)))
                 :in-theory (disable lw-mds-times-negative)))))

(local (defthm lw-mds-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mds-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mds-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mds-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mds-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mds-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mds-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mds-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mds-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mds-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mds-left-commutes)))))

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-quotient
          lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-complex-exp-value lw-complex-exp-cap lw-complex-exp-uniform-cap lw-exp-lipschitz-cap
          lw-mellin-prime-endpoint-mass lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-precision lw-signal-exponential-cost
          lw-smoothed-ramp-unit-error lw-smoothed-ramp-log-error
          lw-complex-log-ramp-family lw-complex-log-ramp-family-cost lw-complex-log-ramp-family-precision
          lw-complex-log-ramp-family-factorization lw-complex-dirichlet-prime-sum
          lw-mellin-finite-primitive lw-mellin-finite-boundary lw-mellin-finite-ray-endpoint
          lw-mellin-finite-dirichlet-model lw-mellin-finite-primitive-boundary
          lw-mellin-frozen-endpoint lw-mellin-endpoint-precision-factor
          lw-mellin-dirichlet-precision lw-mellin-component-endpoint-precision lw-mellin-moment-endpoint-precision
          lw-mellin-endpoint-request lw-mellin-endpoint-cost lw-mellin-endpoint-family-factor
          lw-mellin-computed-bounded-endpoint lw-mellin-bounded-integral lw-mellin-integral
          lw-mellin-integral-cutoff lw-mellin-integral-depth lw-mellin-integral-precision
          lw-kernel-spatial-cap lw-kernel-spatial-slope
          lw-complex-disk-enlarge lw-disk-enlarge lw-complex-sub-add-first
          lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory
 (disable lw-dirichlet-series-count lw-complex-dirichlet-series-value
          lw-dirichlet-transform-value lw-dirichlet-transform
          lw-mellin-series-precision-gain lw-mellin-dirichlet-prime-value
          lw-mellin-tail-coefficient lw-mellin-tail-cutoff
          lw-mellin-dirichlet-node-precision lw-mellin-computed-dirichlet-model)))

(local (defthm lw-mds-tail-mass-positive
 (implies (and (rationalp rate) (< 3 rate))
  (and (rationalp (lw-mellin-tail-coefficient (- rate 2) 0 4)) (< 0 (lw-mellin-tail-coefficient (- rate 2) 0 4))))
 :hints (("Goal"
  :use ((:instance lw-rational-power-positive (base (/ (- rate 2))) (exponent 2)))
  :in-theory (e/d (lw-mellin-tail-coefficient) (lw-rational-power-positive))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mds-request-scalar
 (implies (and (rationalp mass) (< 0 mass) (rationalp gain) (<= 0 gain)
               (natp count) (rationalp error) (< 0 error))
  (let ((request (min (/ error (* 16 (+ gain 10))) (/ (* 2 mass) (+ 1 count)))))
   (and (rationalp request) (< 0 request)
        (<= (* (+ gain 9) request) (* 1/16 error))
        (<= (* (+ 1 count) request) (* 2 mass)))))
 :hints (("Goal"
  :use ((:instance lw-mds-multiply-order
         (a (min (/ error (* 16 (+ gain 10))) (/ (* 2 mass) (+ 1 count)))) (b (/ error (* 16 (+ gain 10)))) (factor (+ gain 9)))
        (:instance lw-positive-division-bound
         (numerator (* (+ gain 9) error)) (divisor (* 16 (+ gain 10))) (bound (* 1/16 error)))
        (:instance lw-mds-multiply-order
         (a (min (/ error (* 16 (+ gain 10))) (/ (* 2 mass) (+ 1 count)))) (b (/ (* 2 mass) (+ 1 count))) (factor (+ 1 count)))
        (:instance lw-positive-division-bound
         (numerator (* (+ 1 count) 2 mass)) (divisor (+ 1 count)) (bound (* 2 mass))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-mellin-series-request (rate height error)
 (min (/ error (* 16 (+ (lw-mellin-series-precision-gain rate height) 10))) (/ (* 2 (lw-mellin-tail-coefficient (- rate 2) 0 4)) (+ 1 (lw-dirichlet-series-count (* 1/4 error))))))

(local (in-theory (disable lw-mellin-series-request)))

(defthm lw-mellin-series-request-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-series-request rate height error)) (< 0 (lw-mellin-series-request rate height error))
       (<= (* (+ (lw-mellin-series-precision-gain rate height) 9) (lw-mellin-series-request rate height error)) (* 1/16 error))
       (<= (* (+ 1 (lw-dirichlet-series-count (* 1/4 error))) (lw-mellin-series-request rate height error)) (* 2 (lw-mellin-tail-coefficient (- rate 2) 0 4)))))
 :hints (("Goal"
  :use (lw-mds-tail-mass-positive lw-mellin-series-precision-gain-valid
        (:instance lw-dirichlet-series-count-valid (error (* 1/4 error)))
        (:instance lw-mds-request-scalar (mass (lw-mellin-tail-coefficient (- rate 2) 0 4)) (gain (lw-mellin-series-precision-gain rate height)) (count (lw-dirichlet-series-count (* 1/4 error)))))
  :in-theory (e/d (lw-mellin-series-request)
    (lw-mellin-series-precision-gain-valid lw-dirichlet-series-count-valid))
  :do-not-induct t)))

(local (defthm lw-mds-positive-cancel
 (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
               (<= (* a factor) (* b factor)))
  (<= a b))
 :hints (("Goal" :nonlinearp t))
 :rule-classes nil))

(defthm lw-mellin-series-request-covers-count
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (< 0 (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)))
       (natp (lw-log-signal-ramp-count (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)))) (<= (lw-dirichlet-series-count (* 1/4 error)) (lw-log-signal-ramp-count (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))))))
 :hints (("Goal"
  :use (lw-mellin-series-request-valid
        (:instance lw-dirichlet-series-count-valid (error (* 1/4 error)))
        (:instance lw-mellin-integral-cutoff-valid (sigma rate) (index 0) (error (lw-mellin-series-request rate height error)))
        (:instance lw-mellin-tail-cutoff-adequate (rate (- rate 2)) (index 0) (mass 4) (error (lw-mellin-series-request rate height error)))
        (:instance lw-mds-positive-cancel (a (+ 1 (lw-dirichlet-series-count (* 1/4 error)))) (b (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (factor (lw-mellin-series-request rate height error)))
        (:instance lw-log-signal-ramp-count-covers-cap (cap (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)))))
  :in-theory (e/d (lw-mellin-integral-cutoff)
    (lw-mellin-series-request-valid lw-dirichlet-series-count-valid
     lw-mellin-integral-cutoff-valid lw-mellin-tail-cutoff-adequate
     lw-log-signal-ramp-count-covers-cap))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mds-euler-rational
 (implies (and (rationalp error) (< 0 error))
  (rationalp (car (lw-euler-bounds error))))
 :hints (("Goal" :use ((:instance lw-euler-bounds-interval (epsilon error)))
                 :in-theory (e/d (lw-intervalp) (lw-euler-bounds-interval))
                 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mds-model-gamma-data
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
  (and (rationalp (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error))) (< 0 (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)))
       (<= (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)) (* 1/16 error)) (rationalp (car (lw-euler-bounds (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)))))))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid
        (:instance lw-signal-exponential-parameters (error (lw-mellin-endpoint-request cap error)))
        (:instance lw-signal-exponential-precision-at-most-request (error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mds-euler-rational (error (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)))))
  :in-theory (disable lw-mellin-endpoint-request-valid lw-signal-exponential-parameters
                      lw-signal-exponential-precision-at-most-request)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mds-prime-series
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-dirichlet-prime-value (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) rate height (lw-mellin-series-request rate height error)) (lw-complex-dirichlet-series-value rate height (* 1/4 error)))
                   (+ (* (lw-mellin-series-precision-gain rate height) (lw-mellin-series-request rate height error)) (* 11/64 error))))
 :hints (("Goal"
  :use (lw-mellin-series-request-valid lw-mellin-series-request-covers-count
        lw-mellin-series-precision-gain-valid
        (:instance lw-mellin-dirichlet-prime-value-rational (cap (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (error (lw-mellin-series-request rate height error)))
        (:instance lw-complex-dirichlet-finite-value-rational (count (lw-log-signal-ramp-count (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)))) (error (* 1/64 error)))
        (:instance lw-complex-dirichlet-series-value-rational (error (* 1/4 error)))
        (:instance lw-mellin-dirichlet-prime-finite-comparison
         (cap (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (error (lw-mellin-series-request rate height error)) (finite-error (* 1/64 error)))
        (:instance lw-complex-dirichlet-series-finite-comparison (count (lw-log-signal-ramp-count (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))))
         (error (* 1/4 error)) (finite-error (* 1/64 error)))
        (:instance lw-complex-difference-triangle (left (lw-mellin-dirichlet-prime-value (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) rate height (lw-mellin-series-request rate height error))) (middle (lw-complex-dirichlet-finite-value rate height (lw-log-signal-ramp-count (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (* 1/64 error))) (right (lw-complex-dirichlet-series-value rate height (* 1/4 error)))
         (radius (+ (* (lw-mellin-series-precision-gain rate height) (lw-mellin-series-request rate height error)) (* 1/64 error))) (other-radius (+ (* 3/8 (* 1/4 error)) (* 4 (* 1/64 error)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-dirichlet-prime-value (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) rate height (lw-mellin-series-request rate height error)) (lw-complex-dirichlet-series-value rate height (* 1/4 error))))
         (radius (+ (+ (* (lw-mellin-series-precision-gain rate height) (lw-mellin-series-request rate height error)) (* 1/64 error)) (+ (* 3/8 (* 1/4 error)) (* 4 (* 1/64 error))))) (cap (+ (* (lw-mellin-series-precision-gain rate height) (lw-mellin-series-request rate height error)) (* 11/64 error)))))
  :in-theory (disable lw-mellin-series-request-valid lw-mellin-series-request-covers-count
                      lw-mellin-series-precision-gain-valid
                      lw-mellin-dirichlet-prime-value-rational
                      lw-complex-dirichlet-finite-value-rational
                      lw-complex-dirichlet-series-value-rational
                      lw-mellin-dirichlet-prime-finite-comparison
                      lw-complex-dirichlet-series-finite-comparison
                      lw-complex-difference-triangle)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mds-model-transform-identity
 (equal (lw-mellin-computed-dirichlet-model cap rate height error)
        (lw-dirichlet-transform rate height
         (lw-mellin-dirichlet-prime-value cap rate height error)
         (car (lw-euler-bounds (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error))))))
 :hints (("Goal"
  :in-theory (enable lw-mellin-computed-dirichlet-model lw-mellin-finite-dirichlet-model
                     lw-dirichlet-transform lw-mellin-dirichlet-prime-value)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mds-computed-model-rational
 (implies (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-computed-dirichlet-model cap rate height error)))
 :hints (("Goal"
  :use (lw-mds-model-gamma-data lw-mds-model-transform-identity
        lw-mellin-dirichlet-prime-value-rational
        (:instance lw-dirichlet-transform-rational
         (prime-value (lw-mellin-dirichlet-prime-value cap rate height error))
         (gamma-value (car (lw-euler-bounds (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)))))))
  :in-theory (disable lw-mellin-dirichlet-prime-value-rational lw-dirichlet-transform-rational)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mds-model-series
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) rate height (lw-mellin-series-request rate height error)) (lw-dirichlet-transform-value rate height error))
                   (+ (* (+ (lw-mellin-series-precision-gain rate height) 1) (lw-mellin-series-request rate height error)) (* 27/64 error))))
 :hints (("Goal"
  :use (lw-mellin-series-request-valid lw-mellin-series-request-covers-count
        lw-mellin-series-precision-gain-valid lw-mds-prime-series
        (:instance lw-mds-model-gamma-data (cap (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (error (lw-mellin-series-request rate height error)))
        (:instance lw-mds-model-transform-identity (cap (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (error (lw-mellin-series-request rate height error)))
        (:instance lw-mellin-dirichlet-prime-value-rational (cap (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error))) (error (lw-mellin-series-request rate height error)))
        (:instance lw-complex-dirichlet-series-value-rational (error (* 1/4 error)))
        (:instance lw-mds-euler-rational (error (* 1/4 error)))
        (:instance lw-euler-lower-cauchy (left-error (lw-signal-exponential-precision (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) (lw-mellin-series-request rate height error)))) (right-error (* 1/4 error)))
        (:instance lw-dirichlet-transform-transport
         (left (lw-mellin-dirichlet-prime-value (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) rate height (lw-mellin-series-request rate height error))) (right (lw-complex-dirichlet-series-value rate height (* 1/4 error))) (left-gamma (car (lw-euler-bounds (lw-signal-exponential-precision (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) (lw-mellin-series-request rate height error)))))) (right-gamma (car (lw-euler-bounds (* 1/4 error))))
         (prime-error (+ (* (lw-mellin-series-precision-gain rate height) (lw-mellin-series-request rate height error)) (* 11/64 error))) (gamma-error (+ (* 1/16 (lw-mellin-series-request rate height error)) (* 1/4 error))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height error)) rate height (lw-mellin-series-request rate height error)) (lw-dirichlet-transform-value rate height error)))
         (radius (+ (+ (* (lw-mellin-series-precision-gain rate height) (lw-mellin-series-request rate height error)) (* 11/64 error)) (+ (* 1/16 (lw-mellin-series-request rate height error)) (* 1/4 error)))) (cap (+ (* (+ (lw-mellin-series-precision-gain rate height) 1) (lw-mellin-series-request rate height error)) (* 27/64 error)))))
  :in-theory (e/d (lw-dirichlet-transform-value)
    (lw-mellin-series-request-valid lw-mellin-series-request-covers-count
     lw-mellin-series-precision-gain-valid lw-mellin-dirichlet-prime-value-rational
     lw-complex-dirichlet-series-value-rational lw-euler-lower-cauchy
     lw-dirichlet-transform-transport))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-dirichlet-series-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-dirichlet-transform-value rate height right-error))
                   (+ (* 5 left-error) right-error)))
 :hints (("Goal"
  :use ((:instance lw-mellin-series-request-valid (error right-error))
        (:instance lw-mellin-series-request-covers-count (error right-error))
        (:instance lw-mellin-series-precision-gain-valid)
        (:instance lw-mellin-integral-rational (sigma rate) (index 0) (error left-error))
        (:instance lw-mellin-integral-rational (sigma rate) (index 0) (error (lw-mellin-series-request rate height right-error)))
        (:instance lw-mds-computed-model-rational (cap (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height right-error))) (error (lw-mellin-series-request rate height right-error)))
        (:instance lw-dirichlet-transform-value-rational (error right-error))
        (:instance lw-mellin-integral-cauchy (sigma rate) (index 0) (right-error (lw-mellin-series-request rate height right-error)))
        (:instance lw-mellin-improper-dirichlet-without-boundary (error (lw-mellin-series-request rate height right-error)))
        (:instance lw-mds-model-series (error right-error))
        (:instance lw-complex-difference-triangle
         (left (lw-mellin-integral rate height 0 left-error)) (middle (lw-mellin-integral rate height 0 (lw-mellin-series-request rate height right-error))) (right (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height right-error)) rate height (lw-mellin-series-request rate height right-error)))
         (radius (* 5 (+ left-error (lw-mellin-series-request rate height right-error)))) (other-radius (* 3 (lw-mellin-series-request rate height right-error))))
        (:instance lw-complex-difference-triangle
         (left (lw-mellin-integral rate height 0 left-error)) (middle (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 (lw-mellin-series-request rate height right-error)) rate height (lw-mellin-series-request rate height right-error))) (right (lw-dirichlet-transform-value rate height right-error))
         (radius (+ (* 5 (+ left-error (lw-mellin-series-request rate height right-error))) (* 3 (lw-mellin-series-request rate height right-error)))) (other-radius (+ (* (+ (lw-mellin-series-precision-gain rate height) 1) (lw-mellin-series-request rate height right-error)) (* 27/64 right-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-dirichlet-transform-value rate height right-error)))
         (radius (+ (+ (* 5 (+ left-error (lw-mellin-series-request rate height right-error))) (* 3 (lw-mellin-series-request rate height right-error))) (+ (* (+ (lw-mellin-series-precision-gain rate height) 1) (lw-mellin-series-request rate height right-error)) (* 27/64 right-error))))
         (cap (+ (* 5 left-error) right-error))))
  :in-theory (disable lw-mellin-series-request-valid lw-mellin-series-request-covers-count
                      lw-mellin-series-precision-gain-valid lw-mellin-integral-rational
                      lw-dirichlet-transform-value-rational lw-mellin-integral-cauchy
                      lw-mellin-improper-dirichlet-without-boundary lw-complex-difference-triangle)
  :nonlinearp nil :do-not-induct t)))




