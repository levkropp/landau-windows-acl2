(in-package "ACL2")

(include-book "mellin-endpoint-precision")

; Relate the actual bounded and improper Mellin evaluators to the finite
; Dirichlet model. The computed upper boundary remains explicit here;
; its uniform decay is a separate remaining obligation.

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

(local (defthm lw-mdc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mdc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mdc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mdc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mdc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mdc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mdc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mdc-left-commutes)))))

(local (defthm lw-mdc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))
(local (defthm lw-mdc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mdc-times-negative (a b) (b a)))
                 :in-theory (disable lw-mdc-times-negative)))))
(local (defthm lw-mdc-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mdc-parameters
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (and (natp (lw-log-signal-ramp-count cap))
       (rationalp (lw-signal-exponential-precision cap model-error))
       (< 0 (lw-signal-exponential-precision cap model-error))
       (rationalp (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))))
 :hints (("Goal"
   :use (lw-log-signal-spatial-cap-valid
         (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
         (:instance lw-signal-exponential-parameters (error model-error))
         (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error))))
   :in-theory (e/d (lw-log-signal-ramp-count lw-intervalp)
     (lw-log-signal-spatial-cap-valid lw-signal-exponential-parameters lw-euler-bounds-interval))
   :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mdc-corrections-cancel
 (equal
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a correction) rest)
   (lw-complex-add (lw-complex-sub b correction) rest))
  (lw-complex-sub a b))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(defthm lw-complex-log-ramp-family-refined-normalization
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total) (<= count total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta) (<= delta (lw-complex-log-ramp-family-precision rate height count error)))
  (lw-complex-diskp (lw-complex-sub (lw-complex-log-ramp-family nil rate height count total model-error primitive-error delta) (lw-complex-mul (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta) (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))
                   (+ (* 1/16 error) (* 1/8 model-error (/ (- rate 1))))))
 :hints (("Goal"
  :use (lw-complex-log-ramp-family-cost-valid lw-complex-log-ramp-family-precision-valid
        lw-complex-log-ramp-family-log-budget
        (:instance lw-mdc-nonnegative-product (a (lw-complex-log-ramp-family-cost rate height count)) (b (/ (- rate 1))))
        (:instance lw-mdc-multiply-order (a delta) (b (lw-complex-log-ramp-family-precision rate height count error)) (factor (* (lw-complex-log-ramp-family-cost rate height count) (/ (- rate 1)))))
        lw-complex-log-ramp-family-normalization lw-complex-log-ramp-family-factorization
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-log-ramp-family nil rate height count total model-error primitive-error delta) (lw-complex-mul (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta) (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))) (radius (* (+ (* delta (lw-complex-log-ramp-family-cost rate height count)) (* 2 (nfix (- count 1)) (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1))))
         (cap (+ (* 1/16 error) (* 1/8 model-error (/ (- rate 1)))))))
  :in-theory (disable lw-complex-log-ramp-family-cost-valid lw-complex-log-ramp-family-precision-valid
                      lw-complex-log-ramp-family-log-budget lw-complex-log-ramp-family-normalization
                      lw-complex-log-ramp-family-factorization)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-finite-boundary-refined-normalization
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp end) (<= 0 end)
       (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error)
       (rationalp delta) (< 0 delta) (<= delta (lw-complex-log-ramp-family-precision rate height (lw-log-signal-ramp-count cap) error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-add (lw-mellin-finite-primitive cap end rate height model-error delta)
                    (lw-mellin-finite-boundary cap end rate height model-error delta))
    (lw-mellin-finite-dirichlet-model cap rate height model-error delta))
   (+ (* 1/16 error) (* 1/8 model-error (/ (- rate 1))))))
 :hints (("Goal"
  :use (lw-mdc-parameters lw-mellin-finite-primitive-boundary
        (:instance lw-complex-log-ramp-family-refined-normalization
          (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error))))
  :in-theory (e/d (lw-mellin-finite-ray-endpoint lw-mellin-finite-dirichlet-model)
                 (lw-mellin-finite-primitive-boundary lw-complex-log-ramp-family-refined-normalization))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mdc-telescope
         (equal (lw-complex-sub left right)
                (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
         :rule-classes nil))

(local (defthm lw-mdc-triangle
         (implies (and (lw-complex-diskp (lw-complex-sub left middle) radius)
                       (lw-complex-diskp (lw-complex-sub middle right) other-radius))
                  (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mdc-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mdc-common-addend-cancels
 (equal (lw-complex-sub (lw-complex-add left boundary) (lw-complex-add right boundary))
        (lw-complex-sub left right))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(local (defthm lw-mdc-cost-dominates
 (implies (and (rationalp cap) (<= 0 cap))
          (<= (lw-mellin-endpoint-family-factor cap) (lw-mellin-endpoint-cost cap)))
 :hints (("Goal"
  :use (lw-mellin-endpoint-cost-valid
        (:instance lw-kernel-spatial-parameters (sigma 0) (step 1))
        (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
        (:instance lw-mdc-nonnegative-product (a cap) (b (lw-kernel-spatial-cap cap 1)))
        (:instance lw-mdc-nonnegative-product
         (a (lw-mellin-endpoint-family-factor cap)) (b (+ 1 (* 2 (lw-complex-exp-uniform-cap cap)))))
        (:instance lw-mdc-nonnegative-product
         (a cap) (b (* (lw-mellin-endpoint-family-factor cap) (+ 1 (* 2 (lw-complex-exp-uniform-cap cap)))))))
  :in-theory (e/d (lw-mellin-endpoint-cost)
    (lw-mellin-endpoint-cost-valid lw-kernel-spatial-parameters lw-complex-exp-uniform-cap-data))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mdc-precision-budget
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
  (<= (* (lw-mellin-endpoint-precision-factor cap (lw-mellin-endpoint-request cap error)) 1/16 (lw-mellin-endpoint-request cap error)) (* 1/256 error)))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid lw-mellin-endpoint-cost-valid lw-mdc-cost-dominates
        (:instance lw-mellin-endpoint-precision-factor-valid (model-error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mdc-multiply-order
         (a (lw-mellin-endpoint-precision-factor cap (lw-mellin-endpoint-request cap error))) (b (lw-mellin-endpoint-cost cap))
         (factor (* 1/16 (lw-mellin-endpoint-request cap error)))))
  :in-theory (disable lw-mellin-endpoint-request-valid lw-mellin-endpoint-cost-valid
                      lw-mellin-endpoint-precision-factor-valid)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mdc-quarter-budget
 (implies
  (and (rationalp clearance) (<= 1 clearance) (rationalp error) (< 0 error)
       (rationalp request) (< 0 request) (<= request (* 1/16 error)))
  (<= (+ (* 1/16 error) (* 1/256 error) (* 1/16 error) (* 1/8 request (/ clearance))) (* 1/4 error)))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound (numerator request) (divisor clearance) (bound (* 1/16 error))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-mellin-dirichlet-node-precision (cap rate height error)
 (lw-mellin-dirichlet-precision cap cap rate height (lw-mellin-endpoint-request cap error) error))

(defun lw-mellin-computed-dirichlet-boundary (cap rate height error)
 (lw-mellin-finite-boundary cap cap rate height (lw-mellin-endpoint-request cap error)
                          (lw-mellin-dirichlet-node-precision cap rate height error)))

(defun lw-mellin-computed-dirichlet-model (cap rate height error)
 (lw-mellin-finite-dirichlet-model cap rate height (lw-mellin-endpoint-request cap error)
                                 (lw-mellin-dirichlet-node-precision cap rate height error)))

(local (in-theory (disable lw-mellin-dirichlet-node-precision
                          lw-mellin-computed-dirichlet-boundary lw-mellin-computed-dirichlet-model)))

(defthm lw-mellin-bounded-dirichlet-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 2 rate) (rationalp height)
       (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-add (lw-mellin-bounded-integral cap rate height 0 (lw-mellin-endpoint-request cap error)) (lw-mellin-computed-dirichlet-boundary cap rate height error)) (lw-mellin-computed-dirichlet-model cap rate height error)) (* 1/4 error)))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid lw-mdc-precision-budget
        (:instance lw-mellin-dirichlet-precision-valid (end cap) (component-error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mellin-computed-bounded-endpoint-comparison (sigma rate))
        (:instance lw-mellin-frozen-endpoint-precision-comparison
         (end cap) (model-error (lw-mellin-endpoint-request cap error)) (error (lw-mellin-endpoint-request cap error)) (delta (lw-mellin-dirichlet-node-precision cap rate height error)))
        (:instance lw-mellin-finite-boundary-refined-normalization
         (end cap) (model-error (lw-mellin-endpoint-request cap error)) (delta (lw-mellin-dirichlet-node-precision cap rate height error)))
        (:instance lw-mdc-quarter-budget (clearance (- rate 1)) (request (lw-mellin-endpoint-request cap error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-mellin-frozen-endpoint cap 0 cap rate height (lw-mellin-endpoint-request cap error) (lw-mellin-endpoint-request cap error)) (lw-mellin-finite-primitive cap cap rate height (lw-mellin-endpoint-request cap error) (lw-mellin-dirichlet-node-precision cap rate height error))))
         (radius (* (lw-mellin-endpoint-precision-factor cap (lw-mellin-endpoint-request cap error)) 1/16 (lw-mellin-endpoint-request cap error))) (cap (* 1/256 error)))
        (:instance lw-mdc-triangle
         (left (lw-mellin-bounded-integral cap rate height 0 (lw-mellin-endpoint-request cap error))) (middle (lw-mellin-frozen-endpoint cap 0 cap rate height (lw-mellin-endpoint-request cap error) (lw-mellin-endpoint-request cap error))) (right (lw-mellin-finite-primitive cap cap rate height (lw-mellin-endpoint-request cap error) (lw-mellin-dirichlet-node-precision cap rate height error)))
         (radius (* 1/16 error)) (other-radius (* 1/256 error)))
        (:instance lw-mdc-triangle
         (left (lw-complex-add (lw-mellin-bounded-integral cap rate height 0 (lw-mellin-endpoint-request cap error)) (lw-mellin-computed-dirichlet-boundary cap rate height error)))
         (middle (lw-complex-add (lw-mellin-finite-primitive cap cap rate height (lw-mellin-endpoint-request cap error) (lw-mellin-dirichlet-node-precision cap rate height error)) (lw-mellin-computed-dirichlet-boundary cap rate height error))) (right (lw-mellin-computed-dirichlet-model cap rate height error))
         (radius (+ (* 1/16 error) (* 1/256 error))) (other-radius (+ (* 1/16 error) (* 1/8 (lw-mellin-endpoint-request cap error) (/ (- rate 1))))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-add (lw-mellin-bounded-integral cap rate height 0 (lw-mellin-endpoint-request cap error)) (lw-mellin-computed-dirichlet-boundary cap rate height error)) (lw-mellin-computed-dirichlet-model cap rate height error)))
         (radius (+ (+ (* 1/16 error) (* 1/256 error)) (+ (* 1/16 error) (* 1/8 (lw-mellin-endpoint-request cap error) (/ (- rate 1)))))) (cap (* 1/4 error))))
  :in-theory
   (e/d (lw-mellin-computed-dirichlet-boundary lw-mellin-computed-dirichlet-model
         lw-mellin-dirichlet-node-precision lw-mellin-computed-bounded-endpoint)
     (lw-mellin-endpoint-request-valid lw-mellin-dirichlet-precision-valid
      lw-mellin-computed-bounded-endpoint-comparison lw-mellin-frozen-endpoint-precision-comparison
      lw-mellin-finite-boundary-refined-normalization))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-improper-dirichlet-comparison
 (implies (and (rationalp rate) (< 2 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-add (lw-mellin-integral rate height 0 error) (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error)) (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 error) rate height error)) error))
 :hints (("Goal"
  :use ((:instance lw-mellin-integral-cutoff-valid (sigma rate) (index 0))
        (:instance lw-mellin-endpoint-request-valid (cap (lw-mellin-integral-cutoff rate 0 error)))
        (:instance lw-mellin-bounded-integral-cauchy
         (cap (lw-mellin-integral-cutoff rate 0 error)) (sigma rate) (index 0) (left-error (* 1/2 error)) (right-error (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error)))
        (:instance lw-mellin-bounded-dirichlet-comparison (cap (lw-mellin-integral-cutoff rate 0 error)))
        (:instance lw-mdc-triangle
         (left (lw-complex-add (lw-mellin-integral rate height 0 error) (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error)))
         (middle (lw-complex-add (lw-mellin-bounded-integral (lw-mellin-integral-cutoff rate 0 error) rate height 0 (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error)) (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error))) (right (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 error) rate height error))
         (radius (+ (* 1/2 error) (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error))) (other-radius (* 1/4 error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-add (lw-mellin-integral rate height 0 error) (lw-mellin-computed-dirichlet-boundary (lw-mellin-integral-cutoff rate 0 error) rate height error)) (lw-mellin-computed-dirichlet-model (lw-mellin-integral-cutoff rate 0 error) rate height error)))
         (radius (+ (* 1/2 error) (lw-mellin-endpoint-request (lw-mellin-integral-cutoff rate 0 error) error) (* 1/4 error))) (cap error)))
  :in-theory (e/d (lw-mellin-integral)
    (lw-mellin-integral-cutoff-valid lw-mellin-endpoint-request-valid
     lw-mellin-bounded-integral-cauchy lw-mellin-bounded-dirichlet-comparison))
  :nonlinearp nil :do-not-induct t)))



