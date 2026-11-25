(in-package "ACL2")

(include-book "dirichlet-series")
(include-book "mellin-dirichlet-decay")

; Bounds independent of the Mellin truncation count for the existing
; finite Dirichlet model's coefficient and node precisions.

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

(local (defthm lw-msp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-msp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-msp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-msp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-msp-times-negative (a b) (b a)))
                 :in-theory (disable lw-msp-times-negative)))))

(local (defthm lw-msp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-msp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-msp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-msp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-msp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-msp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-msp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-msp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-msp-left-commutes)))))

(local (defthm lw-msp-point-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                       (rationalp start) (<= 0 start) (rationalp index) (<= start index))
                  (and
                   (lw-complexp (cons start 0))
                   (lw-complexp (lw-complex-scale start (lw-complex-laplace-point rate height)))
                   (<= 0 (* rate start))
                   (<= 0 (* (+ rate (abs height)) index))
                   (<= (lw-complex-l1 (cons start 0)) index)
                   (<= (lw-complex-l1 (lw-complex-scale start (lw-complex-laplace-point rate height)))
                       (* (+ rate (abs height)) index))
                   (equal (lw-complex-add (cons start 0)
                             (lw-complex-scale start (lw-complex-laplace-point rate height)))
                          (lw-complex-scale start (lw-complex-laplace-point (- rate 1) height)))))
         :hints (("Goal" :cases ((<= 0 height))
                         :in-theory (enable lw-complexp lw-complex-add lw-complex-scale
                                            lw-complex-laplace-point lw-complex-l1)
                         :nonlinearp t))))

(local (defthm lw-msp-cap-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index))
                  (and (rationalp (lw-complex-log-ramp-cap rate height index))
                       (<= 4 (lw-complex-log-ramp-cap rate height index))
                       (rationalp (lw-exp-lipschitz-cap index))
                       (<= 1 (lw-exp-lipschitz-cap index))))
         :hints (("Goal"
                  :use ((:instance lw-msp-point-data (start 0))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap index))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap (* (+ rate (abs height)) index)))
                        (:instance lw-exp-lipschitz-cap-valid (cap index)))
                  :in-theory (e/d (lw-complex-log-ramp-cap)
                                  (lw-msp-point-data lw-complex-exp-uniform-cap-data lw-exp-lipschitz-cap-valid))
                  :do-not-induct t))))

(local (in-theory
 (disable lw-complex-log-ramp-family-cost lw-complex-log-ramp-family-precision
          lw-complex-dirichlet-prime-sum lw-complex-dirichlet-finite-value
          lw-mellin-dirichlet-node-precision lw-mellin-dirichlet-precision
          lw-mellin-endpoint-request lw-mellin-endpoint-cost
          lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
          lw-signal-exponential-cost lw-signal-exponential-precision
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data
          lw-complex-log-ramp-family-cost-valid lw-complex-log-ramp-family-precision-valid)))

(local (defthm lw-msp-power-one
 (implies (rationalp value) (equal (lw-rational-power value 1) value))
 :hints (("Goal" :expand ((lw-rational-power value 1) (lw-rational-power value 0))))))

(local (defthm lw-msp-exp-dominates
 (implies (and (rationalp value) (<= 0 value)) (<= value (lw-exp-lipschitz-cap value)))
 :hints (("Goal"
  :use ((:instance lw-exp-linear-power-le-upper (index 1) (error 1)))
  :in-theory (e/d (lw-exp-lipschitz-cap) (lw-exp-linear-power-le-upper))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-msp-cap-dominates
 (implies (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index))
  (<= index (+ (lw-complex-log-ramp-cap rate height index) 4)))
 :hints (("Goal"
  :use ((:instance lw-msp-exp-dominates (value index))
        (:instance lw-msp-point-data (start 0))
        (:instance lw-complex-exp-uniform-cap-data (argument-cap (* (+ rate (abs height)) index))))
  :in-theory (e/d (lw-complex-log-ramp-cap lw-complex-exp-uniform-cap) (lw-msp-point-data))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-log-ramp-family-cost-covers-count
 (implies (and (rationalp rate) (< 1 rate) (rationalp height) (natp count))
  (<= (* count (+ 1 count)) (* 2 (+ 1 (lw-complex-log-ramp-family-cost rate height count)))))
 :hints (("Goal"
  :induct (lw-complex-log-ramp-family-cost rate height count)
  :in-theory (enable (:induction lw-complex-log-ramp-family-cost)
                     (:definition lw-complex-log-ramp-family-cost)))
  (and stable-under-simplificationp
   '(:use ((:instance lw-msp-cap-dominates (index count)))
     :do-not-induct t))))

(local (defthm lw-msp-precision-scalar
 (implies (and (rationalp cost) (<= 0 cost) (rationalp clearance) (< 0 clearance)
               (rationalp error) (< 0 error))
  (<= (* (+ 1 cost) (min 1 (/ (* clearance error) (* 16 (+ 1 cost))))) (* 1/16 clearance error)))
 :hints (("Goal"
  :use ((:instance lw-msp-multiply-order
         (a (min 1 (/ (* clearance error) (* 16 (+ 1 cost))))) (b (/ (* clearance error) (* 16 (+ 1 cost)))) (factor (+ 1 cost)))
        (:instance lw-positive-division-bound
         (numerator (* (+ 1 cost) clearance error)) (divisor (* 16 (+ 1 cost)))
         (bound (* 1/16 clearance error))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-log-ramp-family-precision-full-cost
 (implies (and (rationalp rate) (< 1 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (<= (* (+ 1 (lw-complex-log-ramp-family-cost rate height count)) (lw-complex-log-ramp-family-precision rate height count error))
      (* 1/16 (- rate 1) error)))
 :hints (("Goal"
  :use (lw-complex-log-ramp-family-cost-valid
        (:instance lw-msp-precision-scalar (cost (lw-complex-log-ramp-family-cost rate height count)) (clearance (- rate 1))))
  :in-theory (enable lw-complex-log-ramp-family-precision)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-log-signal-ramp-count-covers-cap
 (implies (and (rationalp cap) (<= 0 cap))
  (and (natp (lw-log-signal-ramp-count cap)) (<= 3 (lw-log-signal-ramp-count cap)) (<= cap (lw-log-signal-ramp-count cap))))
 :hints (("Goal"
  :use ((:instance lw-msp-exp-dominates (value cap))
        lw-log-signal-spatial-cap-valid
        (:instance lw-signal-count-covers (value (lw-log-signal-spatial-cap cap))))
  :in-theory (e/d (lw-log-signal-ramp-count lw-log-signal-spatial-cap)
                  (lw-log-signal-spatial-cap-valid lw-signal-count-covers))
  :do-not-induct t)))

(local (defthm lw-msp-model-data
 (implies (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 1 rate)
               (rationalp height) (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-endpoint-request cap error)) (< 0 (lw-mellin-endpoint-request cap error)) (<= (lw-mellin-endpoint-request cap error) (* 1/16 error))
       (rationalp (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error))) (< 0 (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error))) (<= (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)) (lw-mellin-endpoint-request cap error))
       (rationalp (lw-mellin-dirichlet-node-precision cap rate height error)) (< 0 (lw-mellin-dirichlet-node-precision cap rate height error)) (<= (lw-mellin-dirichlet-node-precision cap rate height error) 1) (<= (lw-mellin-dirichlet-node-precision cap rate height error) (lw-complex-log-ramp-family-precision rate height (lw-log-signal-ramp-count cap) error))))
 :hints (("Goal"
  :use (lw-mellin-endpoint-request-valid
        (:instance lw-signal-exponential-parameters (error (lw-mellin-endpoint-request cap error)))
        (:instance lw-signal-exponential-precision-at-most-request (error (lw-mellin-endpoint-request cap error)))
        (:instance lw-mellin-dirichlet-precision-valid
         (end cap) (component-error (lw-mellin-endpoint-request cap error))))
  :in-theory (e/d (lw-mellin-dirichlet-node-precision)
    (lw-mellin-endpoint-request-valid lw-signal-exponential-parameters
     lw-signal-exponential-precision-at-most-request lw-mellin-dirichlet-precision-valid))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-msp-node-count-budget
 (implies (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 1 rate)
               (rationalp height) (rationalp error) (< 0 error))
  (<= (* 16 (lw-log-signal-ramp-count cap) (+ 1 (lw-log-signal-ramp-count cap)) (lw-mellin-dirichlet-node-precision cap rate height error)) (* 2 (- rate 1) error)))
 :hints (("Goal"
  :use (lw-log-signal-ramp-count-covers-cap lw-msp-model-data
        (:instance lw-complex-log-ramp-family-cost-valid (count (lw-log-signal-ramp-count cap)))
        (:instance lw-complex-log-ramp-family-cost-covers-count (count (lw-log-signal-ramp-count cap)))
        (:instance lw-complex-log-ramp-family-precision-full-cost (count (lw-log-signal-ramp-count cap)))
        (:instance lw-msp-multiply-order (a (lw-mellin-dirichlet-node-precision cap rate height error)) (b (lw-complex-log-ramp-family-precision rate height (lw-log-signal-ramp-count cap) error)) (factor (+ 1 (lw-complex-log-ramp-family-cost rate height (lw-log-signal-ramp-count cap)))))
        (:instance lw-msp-multiply-order (a (* (lw-log-signal-ramp-count cap) (+ 1 (lw-log-signal-ramp-count cap)))) (b (* 2 (+ 1 (lw-complex-log-ramp-family-cost rate height (lw-log-signal-ramp-count cap))))) (factor (lw-mellin-dirichlet-node-precision cap rate height error))))
  :in-theory (disable lw-log-signal-ramp-count-covers-cap
                      lw-complex-log-ramp-family-cost-covers-count
                      lw-complex-log-ramp-family-precision-full-cost)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-msp-signal-cost-covers-count
 (implies (and (rationalp cap) (<= 0 cap))
  (and (rationalp (lw-signal-exponential-cost cap)) (<= (lw-log-signal-ramp-count cap) (lw-signal-exponential-cost cap))))
 :hints (("Goal"
  :use (lw-log-signal-ramp-count-covers-cap lw-log-signal-spatial-cap-valid)
  :in-theory (e/d (lw-signal-exponential-cost)
                  (lw-log-signal-ramp-count-covers-cap lw-log-signal-spatial-cap-valid))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-msp-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error))
       (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-msp-coefficient-count-budget
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (<= (* 2 (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) model-error))
 :hints (("Goal"
  :use (lw-log-signal-ramp-count-covers-cap lw-msp-signal-cost-covers-count
        (:instance lw-msp-unit-data (total (lw-log-signal-ramp-count cap)))
        (:instance lw-signal-exponential-parameters (error model-error))
        (:instance lw-msp-multiply-order (a (lw-log-signal-ramp-count cap)) (b (lw-signal-exponential-cost cap)) (factor (* 2 (lw-signal-exponential-precision cap model-error)))))
  :in-theory (disable lw-log-signal-ramp-count-covers-cap lw-signal-exponential-parameters)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-mellin-series-precision-gain (rate height)
 (+ 1 (* 4 rate) (* 2 (abs height))))

(defthm lw-mellin-series-precision-gain-valid
 (implies (and (rationalp rate) (< 1 rate) (rationalp height))
  (and (rationalp (lw-mellin-series-precision-gain rate height)) (< 0 (lw-mellin-series-precision-gain rate height)))))

(local (in-theory (disable lw-mellin-series-precision-gain lw-mellin-series-precision-gain-valid)))

(defun lw-mellin-dirichlet-prime-value (cap rate height error)
 (lw-complex-dirichlet-prime-sum rate height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) (lw-mellin-endpoint-request cap error) (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)) (lw-mellin-dirichlet-node-precision cap rate height error)))

(local (in-theory (disable lw-mellin-dirichlet-prime-value)))

(defthm lw-mellin-dirichlet-prime-value-rational
 (implies (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 1 rate)
               (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-dirichlet-prime-value cap rate height error)))
 :hints (("Goal"
  :use (lw-log-signal-ramp-count-covers-cap lw-msp-model-data
        (:instance lw-complex-dirichlet-prime-sum-rational
         (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (model-error (lw-mellin-endpoint-request cap error)) (primitive-error (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error))) (delta (lw-mellin-dirichlet-node-precision cap rate height error))))
  :in-theory (e/d (lw-mellin-dirichlet-prime-value)
    (lw-log-signal-ramp-count-covers-cap lw-complex-dirichlet-prime-sum-rational))
  :do-not-induct t)))

(defthm lw-mellin-dirichlet-prime-finite-comparison
 (implies (and (rationalp cap) (<= 0 cap) (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error) (rationalp finite-error) (< 0 finite-error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-dirichlet-prime-value cap rate height error) (lw-complex-dirichlet-finite-value rate height (lw-log-signal-ramp-count cap) finite-error))
                    (+ (* (lw-mellin-series-precision-gain rate height) error) finite-error)))
 :hints (("Goal"
  :use (lw-log-signal-ramp-count-covers-cap lw-msp-model-data lw-msp-node-count-budget
        (:instance lw-msp-coefficient-count-budget (model-error (lw-mellin-endpoint-request cap error)))
        (:instance lw-msp-multiply-order (a (lw-mellin-endpoint-request cap error)) (b (* 1/16 error))
         (factor (* (* 2 (+ rate (abs height))) 1/16)))
        (:instance lw-complex-dirichlet-prime-sum-finite-comparison
         (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (model-error (lw-mellin-endpoint-request cap error)) (primitive-error (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error)))
         (delta (lw-mellin-dirichlet-node-precision cap rate height error)) (error finite-error))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-dirichlet-prime-value cap rate height error) (lw-complex-dirichlet-finite-value rate height (lw-log-signal-ramp-count cap) finite-error)))
         (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (lw-mellin-endpoint-request cap error)) (* 16 (* (lw-log-signal-ramp-count cap) (+ 1 (lw-log-signal-ramp-count cap))) (lw-mellin-dirichlet-node-precision cap rate height error)) (* 2 (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap (lw-mellin-endpoint-request cap error))) finite-error)) (cap (+ (* (lw-mellin-series-precision-gain rate height) error) finite-error))))
  :in-theory (e/d (lw-mellin-dirichlet-prime-value lw-mellin-series-precision-gain)
    (lw-log-signal-ramp-count-covers-cap lw-complex-dirichlet-prime-sum-finite-comparison))
  :nonlinearp t :do-not-induct t)))



