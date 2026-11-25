(in-package "ACL2")

(include-book "mellin-interval-boundaries")

(include-book "mellin-refined-endpoint-budgets")

; Transfer refined tail estimates to the existing boundary at both ends.
; One computed node precision works, and every finer positive precision
; retains the bound. Uniform decay of the far endpoint is still separate.

(local (in-theory
 (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-precision lw-signal-exponential-cost
          lw-mellin-common-depth lw-mellin-component-minimum-depth
          lw-mellin-prime-endpoint-mass lw-mellin-common-base-radius
          lw-mellin-refined-endpoint lw-mellin-refined-endpoint-radius
          lw-kernel-spatial-cap lw-kernel-spatial-slope lw-complex-exp-uniform-cap
          lw-halved-width lw-halving-depth lw-precision-fuel
          lw-mellin-integral-cutoff lw-mellin-tail-coefficient
          lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
          lw-complex-disk-enlarge lw-disk-enlarge
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-mellin-finite-interval-primitive lw-mellin-finite-interval-boundary
 lw-mellin-finite-boundary lw-mellin-refined-comparison-cost
 lw-mellin-refined-endpoint-request lw-mellin-endpoint-precision-factor
 lw-mellin-computed-refined-endpoint lw-mellin-refined-endpoint)))

(local (defthm lw-mbt-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                       (:instance associativity-of-* (x b) (y a) (z c))
                       (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mbt-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mbt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mbt-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mbt-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mbt-times-negative (a b) (b a)))
                         :in-theory (disable lw-mbt-times-negative)))))

(local (defthm lw-mbt-multiply-order
 (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
  (<= (* a factor) (* b factor)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mbt-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mbt-input-data
 (implies
  (and (rationalp model-cap) (<= 0 model-cap)
       (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-signal-exponential-precision model-cap model-error)) (< 0 (lw-signal-exponential-precision model-cap model-error))
       (rationalp (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error))) (<= 0 (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error)))
       (rationalp (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error)))))) (<= 0 (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error))))))
       (rationalp (lw-kernel-spatial-cap cap 1)) (<= 0 (lw-kernel-spatial-cap cap 1))
       (rationalp (lw-complex-exp-uniform-cap cap)) (<= 0 (lw-complex-exp-uniform-cap cap))))
 :hints (("Goal"
  :use ((:instance lw-signal-exponential-parameters (cap model-cap) (error model-error))
        (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap model-cap)))
        (:instance lw-mellin-prime-endpoint-mass-valid (count (lw-log-signal-ramp-count model-cap)) (primitive-error (lw-signal-exponential-precision model-cap model-error)))
        (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision model-cap model-error)))
        (:instance lw-kernel-spatial-parameters (sigma 0) (step 1))
        (:instance lw-complex-exp-uniform-cap-data (argument-cap cap)))
  :in-theory (e/d (lw-log-signal-ramp-count lw-intervalp)
    (lw-signal-exponential-parameters lw-mellin-prime-endpoint-mass-valid
     lw-euler-bounds-interval lw-kernel-spatial-parameters lw-complex-exp-uniform-cap-data))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-mbt-domination-scalar
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp length) (<= 0 length)
       (rationalp mass) (<= 0 mass) (rationalp coefficient) (<= 0 coefficient)
       (rationalp kernel) (<= 0 kernel) (rationalp exponential) (<= 0 exponential)
       (rationalp model-error) (< 0 model-error))
  (<= (+ mass 1 coefficient)
      (+ 1 (* kernel model-error)
         (* length (+ mass cap coefficient) (+ 1 (* 2 exponential)))
         (+ mass 1 coefficient))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-refined-cost-dominates-precision-factor
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp length) (<= 0 length) (rationalp model-error) (< 0 model-error))
  (<= (lw-mellin-endpoint-precision-factor model-cap model-error) (lw-mellin-refined-comparison-cost model-cap cap length model-error)))
 :hints (("Goal"
  :use (lw-mbt-input-data
        (:instance lw-mbt-domination-scalar (mass (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count model-cap) (lw-signal-exponential-precision model-cap model-error))) (coefficient (abs (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision model-cap model-error))))))
         (kernel (lw-kernel-spatial-cap cap 1)) (exponential (lw-complex-exp-uniform-cap cap))))
  :in-theory (enable lw-mellin-refined-comparison-cost lw-mellin-endpoint-precision-factor)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-refined-endpoint-transfer-budget
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp length) (<= 0 length) (rationalp model-error) (< 0 model-error)
       (rationalp error) (< 0 error))
  (<= (* (lw-mellin-endpoint-precision-factor model-cap model-error) 1/16 (lw-mellin-refined-endpoint-request model-cap cap length model-error error)) (* 1/256 error)))
 :hints (("Goal"
  :use (lw-mellin-refined-cost-dominates-precision-factor
        lw-mellin-refined-endpoint-request-valid
        (:instance lw-mbt-multiply-order (a (lw-mellin-endpoint-precision-factor model-cap model-error)) (b (lw-mellin-refined-comparison-cost model-cap cap length model-error)) (factor (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))
  :in-theory (disable lw-mellin-refined-cost-dominates-precision-factor
                      lw-mellin-refined-endpoint-request-valid)
  :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-computed-tail-node-precision
 (model-cap cap start length rate model-error error)
 (lw-mellin-interval-node-precision cap start length rate (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))

(local (in-theory (disable lw-mellin-computed-tail-node-precision)))

(defthm lw-mellin-computed-tail-node-precision-valid
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
       (rationalp rate) (< 1 rate) (rationalp model-error) (< 0 model-error)
       (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-computed-tail-node-precision model-cap cap start length rate model-error error)) (< 0 (lw-mellin-computed-tail-node-precision model-cap cap start length rate model-error error)) (<= (lw-mellin-computed-tail-node-precision model-cap cap start length rate model-error error) 1)
       (<= (lw-mellin-computed-tail-node-precision model-cap cap start length rate model-error error) (lw-mellin-component-endpoint-precision 0 length rate (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))
       (<= (lw-mellin-computed-tail-node-precision model-cap cap start length rate model-error error) (lw-mellin-component-endpoint-precision 3 length rate (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))
       (<= (lw-mellin-computed-tail-node-precision model-cap cap start length rate model-error error) (lw-mellin-interval-moment-precision cap start length rate (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))))
 :hints (("Goal"
  :use (lw-mellin-refined-endpoint-request-valid
        (:instance lw-mellin-interval-node-precision-valid (error (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))
  :in-theory (e/d (lw-mellin-computed-tail-node-precision)
    (lw-mellin-refined-endpoint-request-valid lw-mellin-interval-node-precision-valid))
  :do-not-induct t)))


(local (defthm lw-mbt-recover
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal b (lw-complex-add a (lw-complex-sub b a))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))
 :rule-classes nil))

(local (defthm lw-mbt-approximation-tail
 (implies (and (lw-complexp b) (lw-complex-diskp a radius)
               (lw-complex-diskp (lw-complex-sub a b) error))
  (lw-complex-diskp b (+ radius error)))
 :hints (("Goal"
  :use (lw-mbt-recover
        (:instance lw-complex-difference-symmetric (left a) (right b) (radius error))
        (:instance lw-complex-add-disk (left a) (right (lw-complex-sub b a)) (other-radius error)))
  :in-theory (disable lw-complex-add-disk)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-common-node-boundary-tail
 (implies
  (and (rationalp model-cap) (<= 0 model-cap) (rationalp cap) (<= 0 cap)
       (rationalp start) (< 0 start) (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp rate) (< 2 rate) (rationalp height) (<= 2 (* (- rate 2) start))
       (rationalp model-error) (< 0 model-error) (<= model-error 1)
       (rationalp error) (< 0 error) (rationalp delta) (< 0 delta) (<= delta (lw-mellin-computed-tail-node-precision model-cap cap start length rate model-error error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-finite-boundary model-cap start rate height model-error delta) (lw-mellin-finite-boundary model-cap (+ start length) rate height model-error delta)) (+ (/ (* 10 (lw-mellin-tail-coefficient (- rate 2) 0 1)) start) (* 1/8 error))))
 :hints (("Goal"
  :use (lw-mellin-computed-tail-node-precision-valid
        lw-mellin-refined-endpoint-request-valid
        lw-mellin-refined-endpoint-transfer-budget
        (:instance lw-mellin-computed-refined-endpoint-tail-bound (sigma rate))
        (:instance lw-mellin-finite-interval-primitive-rational (cap model-cap))
        (:instance lw-mellin-finite-interval-boundary (cap model-cap))
        (:instance lw-mellin-interval-endpoint-precision-comparison (error (lw-mellin-refined-endpoint-request model-cap cap length model-error error)))
        (:instance lw-mbt-approximation-tail
         (a (lw-mellin-computed-refined-endpoint model-cap cap start length rate height model-error error)) (b (lw-mellin-finite-interval-primitive model-cap start length rate height model-error delta)) (radius (+ (/ (* 10 (lw-mellin-tail-coefficient (- rate 2) 0 1)) start) (* 1/16 error))) (error (* (lw-mellin-endpoint-precision-factor model-cap model-error) 1/16 (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))
        (:instance lw-complex-disk-enlarge (point (lw-mellin-finite-interval-primitive model-cap start length rate height model-error delta))
         (radius (+ (/ (* 10 (lw-mellin-tail-coefficient (- rate 2) 0 1)) start) (* 1/16 error) (* (lw-mellin-endpoint-precision-factor model-cap model-error) 1/16 (lw-mellin-refined-endpoint-request model-cap cap length model-error error))))
         (cap (+ (/ (* 10 (lw-mellin-tail-coefficient (- rate 2) 0 1)) start) (* 1/8 error)))))
  :in-theory (e/d (lw-mellin-computed-refined-endpoint)
    (lw-mellin-computed-tail-node-precision-valid lw-mellin-refined-endpoint-request-valid
     lw-mellin-refined-endpoint-transfer-budget lw-mellin-computed-refined-endpoint-tail-bound
     lw-mellin-finite-interval-primitive-rational lw-mellin-finite-interval-boundary
     lw-mellin-interval-endpoint-precision-comparison))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-common-node-boundary-at-integral-cutoff
 (implies
  (and (rationalp model-cap) (<= 0 model-cap)
       (rationalp rate) (< 2 rate) (rationalp height)
       (rationalp model-error) (< 0 model-error) (<= model-error 1)
       (rationalp error) (< 0 error) (rationalp cutoff-error) (< 0 cutoff-error)
       (rationalp end) (<= (lw-mellin-integral-cutoff rate 0 cutoff-error) end)
       (rationalp delta) (< 0 delta) (<= delta (lw-mellin-computed-tail-node-precision model-cap end (lw-mellin-integral-cutoff rate 0 cutoff-error) (- end (lw-mellin-integral-cutoff rate 0 cutoff-error)) rate model-error error)))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-finite-boundary model-cap (lw-mellin-integral-cutoff rate 0 cutoff-error) rate height model-error delta)
                   (lw-mellin-finite-boundary model-cap end rate height model-error delta)) (+ (* 5/4 cutoff-error) (* 1/8 error))))
 :hints (("Goal"
  :use ((:instance lw-mellin-integral-cutoff-valid (sigma rate) (index 0) (error cutoff-error))
        (:instance lw-mellin-tail-cutoff-adequate (rate (- rate 2)) (index 0) (mass 4) (error cutoff-error))
        (:instance lw-mellin-common-node-boundary-tail
         (cap end) (start (lw-mellin-integral-cutoff rate 0 cutoff-error)) (length (- end (lw-mellin-integral-cutoff rate 0 cutoff-error))))
        (:instance lw-positive-division-bound
         (numerator (* 10 (lw-mellin-tail-coefficient (- rate 2) 0 1)))
         (divisor (lw-mellin-integral-cutoff rate 0 cutoff-error)) (bound (* 5/4 cutoff-error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-finite-boundary model-cap (lw-mellin-integral-cutoff rate 0 cutoff-error) rate height model-error delta)
                   (lw-mellin-finite-boundary model-cap end rate height model-error delta)))
         (radius (+ (/ (* 10 (lw-mellin-tail-coefficient (- rate 2) 0 1)) (lw-mellin-integral-cutoff rate 0 cutoff-error)) (* 1/8 error))) (cap (+ (* 5/4 cutoff-error) (* 1/8 error)))))
  :in-theory (e/d (lw-mellin-integral-cutoff lw-mellin-tail-coefficient)
    (lw-mellin-integral-cutoff-valid lw-mellin-common-node-boundary-tail lw-rational-power))
  :nonlinearp t :do-not-induct t)))
