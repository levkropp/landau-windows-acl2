(in-package "ACL2")

(include-book "signal-exponential-growth")

; Freeze Mangoldt/Euler coefficients and logarithmic cutpoints while
; independently refining the exponential point evaluations. The same
; global growth bound holds at every finer positive point precision.

(local (in-theory
        (disable lw-smoothed-sum-bounds lw-mangoldt-bounds lw-ramp
                 lw-log-ramp-extension lw-exp-lipschitz-cap
                 lw-log-signal-point lw-log-signal-delta lw-log-signal-cap
                 lw-log-signal-margin lw-log-signal-lipschitz lw-log-signal-budget
                 lw-log-signal-spatial-cap lw-signal-count lw-signal-precision
                 lw-log-signal-linear-precision lw-interval-add lw-interval-scale
                 lw-log-bounds lw-euler-bounds lw-exp-bounds lw-exp-index lw-exp-term lw-exp-sum
                 lw-smoothed-ramp-unit-error lw-smoothed-ramp-log-error lw-log-signal-ramp-count
                 lw-smoothed-ramp-extension-sum lw-smoothed-sum-bounds-zero-tail lw-exp-bounds-valid
                 lw-signal-exponential-value lw-signal-exponential-linear
                 lw-signal-exponential-cost lw-signal-exponential-precision)))

(local (defthm lw-serf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-serf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-serf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-serf-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-serf-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))

(local (defthm lw-serf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-serf-left-commutes)))))

(local (defthm lw-serf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-serf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-serf-unit-positive
         (implies (and (natp total) (rationalp error) (< 0 error))
                  (and (rationalp (lw-smoothed-ramp-unit-error total error))
                       (< 0 (lw-smoothed-ramp-unit-error total error))))
         :hints (("Goal" :use ((:instance lw-serf-positive-product (a error) (b (/ (+ 1 total)))))
                         :in-theory (enable lw-smoothed-ramp-unit-error)))
         :rule-classes nil))

(local (defthm lw-serf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-serf-exponential-data
         (implies (and (rationalp value) (<= 0 value) (rationalp exp-error) (< 0 exp-error))
                  (and (lw-intervalp (lw-exp-bounds value exp-error)) (<= 1 (car (lw-exp-bounds value exp-error)))))
         :hints (("Goal" :use ((:instance lw-exp-bounds-valid (epsilon exp-error)))))
         :rule-classes nil))

(local (defthm lw-serf-count-data
         (implies (and (rationalp cap) (<= 0 cap))
                  (and (rationalp (lw-log-signal-spatial-cap cap))
                       (<= 3 (lw-log-signal-spatial-cap cap))
                       (posp (lw-log-signal-ramp-count cap))
                       (<= (lw-log-signal-spatial-cap cap) (lw-log-signal-ramp-count cap))))
         :hints (("Goal"
                  :use (lw-log-signal-spatial-cap-valid
                        (:instance lw-signal-count-covers (value (lw-log-signal-spatial-cap cap))))
                  :in-theory (e/d (lw-log-signal-ramp-count)
                                  (lw-log-signal-spatial-cap-valid lw-signal-count-covers))))
         :rule-classes nil))

(local (defthm lw-serf-cost-lower
         (implies (and (rationalp cap) (<= 0 cap))
                  (and (rationalp (lw-signal-exponential-cost cap)) (<= (* 3 (lw-log-signal-ramp-count cap)) (lw-signal-exponential-cost cap))))
         :hints (("Goal"
                  :use (lw-serf-count-data
                        (:instance lw-serf-positive-product (a (+ (lw-log-signal-ramp-count cap) 1)) (b (lw-log-signal-spatial-cap cap))))
                  :in-theory (enable lw-signal-exponential-cost) :nonlinearp nil))
         :rule-classes nil))

(local (defthm lw-serf-native-budget
         (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
                  (<= (* (lw-log-signal-ramp-count cap) (+ (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error) (* 3 (lw-signal-exponential-precision cap error)))) error))
         :hints (("Goal"
                  :use (lw-serf-count-data lw-serf-cost-lower lw-signal-exponential-parameters
                        (:instance lw-serf-unit-positive (total (lw-log-signal-ramp-count cap)))
                        (:instance lw-serf-multiply-order
                          (a (* 3 (lw-log-signal-ramp-count cap))) (b (lw-signal-exponential-cost cap)) (factor (lw-signal-exponential-precision cap error))))
                  :in-theory (disable lw-signal-exponential-parameters)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-serf-negative-budget
 (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error)
               (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap error)))
  (<= (* (lw-log-signal-ramp-count cap)
         (+ (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error) (* 3 exp-error)))
      error))
 :hints (("Goal"
  :use (lw-serf-native-budget lw-serf-count-data lw-signal-exponential-parameters
        (:instance lw-serf-multiply-order (a exp-error) (b (lw-signal-exponential-precision cap error))
         (factor (* 3 (lw-log-signal-ramp-count cap)))))
  :in-theory (disable lw-signal-exponential-parameters)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defun lw-signal-exponential-refined-value (cap value error exp-error)
 (lw-signal-exponential-linear cap value (car (lw-exp-bounds value exp-error))
                               error (lw-signal-exponential-precision cap error)))

(defun lw-signal-exponential-refinement-precision (cap model-error error)
 (min (lw-signal-exponential-precision cap model-error) error))

(local (in-theory (disable lw-signal-exponential-refined-value lw-signal-exponential-refinement-precision)))

(defthm lw-signal-exponential-refined-native
 (equal (lw-signal-exponential-refined-value cap value error (lw-signal-exponential-precision cap error))
        (lw-signal-exponential-value cap value error))
 :hints (("Goal" :in-theory (enable lw-signal-exponential-refined-value lw-signal-exponential-value))))

(defthm lw-signal-exponential-refined-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp error) (< 0 error) (rationalp exp-error) (< 0 exp-error))
           (rationalp (lw-signal-exponential-refined-value cap value error exp-error)))
  :hints (("Goal"
           :use (lw-signal-exponential-parameters
                 (:instance lw-serf-exponential-data (exp-error exp-error)))
           :in-theory (e/d (lw-signal-exponential-refined-value lw-intervalp)
                           (lw-signal-exponential-parameters))
           :do-not-induct t)))

(local (defthm lw-serf-scalar-growth
         (implies (and (rationalp point) (<= 1 point) (rationalp value) (<= 0 value) (<= value point)
                       (rationalp gamma) (<= -1 gamma) (<= gamma 2)
                       (rationalp total) (rationalp error) (< 0 error)
                       (<= (- error) total) (<= total (* point point)))
                  (<= (abs (+ total (- (* value point)) (* point (+ 1 gamma))))
                      (+ (* 4 point point) error)))
         :hints (("Goal"
                  :use ((:instance lw-serf-multiply-order (a value) (b point) (factor point))
                        (:instance lw-serf-multiply-order (a -1) (b gamma) (factor point))
                        (:instance lw-serf-multiply-order (a gamma) (b 2) (factor point))
                        (:instance lw-serf-multiply-order (a 1) (b point) (factor (* 3 point)))
                        (:instance lw-serf-multiply-order (a 0) (b point) (factor point)))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defthm lw-signal-exponential-refined-growth
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp error) (< 0 error)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap error)))
           (<= (abs (lw-signal-exponential-refined-value cap value error exp-error))
               (+ (* 4 (car (lw-exp-bounds value exp-error)) (car (lw-exp-bounds value exp-error))) error)))
  :hints (("Goal"
           :use (lw-serf-count-data lw-serf-cost-lower lw-serf-negative-budget lw-signal-exponential-parameters
                 (:instance lw-serf-exponential-data (exp-error exp-error))
                 (:instance lw-exp-bounds-linear-lower (error exp-error))
                 (:instance lw-smoothed-ramp-exponential-error
                   (exp-error exp-error) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-ramp-extension-quadratic-upper
                   (point (car (lw-exp-bounds value exp-error))) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-sum-lower-linear-growth
                   (value (car (lw-exp-bounds value exp-error))) (count (lw-log-signal-ramp-count cap)) (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-sum-bounds-valid (value (car (lw-exp-bounds value exp-error))) (count (lw-log-signal-ramp-count cap)) (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-ramp-extension-sum-rational
                   (point (car (lw-exp-bounds value exp-error))) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-euler-bounds-coarse (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-serf-scalar-growth (point (car (lw-exp-bounds value exp-error))) (gamma (car (lw-euler-bounds (lw-signal-exponential-precision cap error)))) (total (lw-smoothed-ramp-extension-sum value (car (lw-exp-bounds value exp-error)) (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) error (lw-signal-exponential-precision cap error)))))
           :in-theory
           (e/d (lw-signal-exponential-refined-value lw-signal-exponential-linear lw-intervalp)
                (lw-signal-exponential-parameters lw-exp-bounds-linear-lower
                 lw-smoothed-ramp-exponential-error lw-smoothed-ramp-extension-quadratic-upper
                 lw-smoothed-sum-lower-linear-growth lw-smoothed-sum-bounds-valid
                 lw-smoothed-ramp-extension-sum-rational lw-euler-bounds-interval
                 lw-euler-bounds-coarse lw-euler-bounds-overlap))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-signal-exponential-refined-uniform-growth
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp error) (< 0 error)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap error)) (<= error 1))
           (<= (abs (lw-signal-exponential-refined-value cap value error exp-error)) (* 5 (car (lw-exp-bounds value exp-error)) (car (lw-exp-bounds value exp-error)))))
  :hints (("Goal"
           :use (lw-signal-exponential-refined-growth
                 (:instance lw-serf-exponential-data (exp-error exp-error))
                 (:instance lw-serf-multiply-order (a 1) (b (car (lw-exp-bounds value exp-error))) (factor (car (lw-exp-bounds value exp-error)))))
           :in-theory (e/d (lw-intervalp) (lw-signal-exponential-refined-growth))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-signal-exponential-refinement-precision-valid
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error)
               (rationalp error) (< 0 error))
  (let ((precision (lw-signal-exponential-refinement-precision cap model-error error)))
   (and (rationalp precision) (< 0 precision) (<= precision error)
        (<= precision (lw-signal-exponential-precision cap model-error)))))
 :hints (("Goal"
  :use ((:instance lw-signal-exponential-parameters (error model-error)))
  :in-theory (e/d (lw-signal-exponential-refinement-precision) (lw-signal-exponential-parameters))
  :nonlinearp nil :do-not-induct t)))

