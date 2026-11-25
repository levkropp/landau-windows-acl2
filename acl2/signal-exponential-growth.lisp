(in-package "ACL2")

(include-book "signal-exponential-decomposition")

; Global growth of the frozen signal family, even beyond the compact
; interval used to construct it. The bound is independent of the finite
; prime-sum truncation and will control the improper Mellin tail.

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

(local (defthm lw-seg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-seg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-seg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-seg-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-seg-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-seg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-seg-left-commutes)))))
(local (defthm lw-seg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-seg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-seg-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-seg-sum-error
         (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- c d)) other-radius))
                  (<= (abs (- (+ a c) (+ b d))) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= c d)))) :rule-classes nil))
(local (defthm lw-seg-weighted-error
         (implies
          (and (rationalp a) (rationalp b) (rationalp weight) (<= 0 weight)
               (rationalp index) (< 0 index) (<= weight index)
               (rationalp radius) (<= 0 radius) (<= (abs (- a b)) (* radius (/ index))))
          (<= (abs (- (* weight a) (* weight b))) radius))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x index))
                        (:instance lw-seg-multiply-order
                          (a (abs (- a b))) (b (* radius (/ index))) (factor weight))
                        (:instance lw-seg-multiply-order
                          (a weight) (b index) (factor (* radius (/ index)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))


(local (defthm lw-seg-unit-positive
         (implies (and (natp total) (rationalp error) (< 0 error))
                  (and (rationalp (lw-smoothed-ramp-unit-error total error))
                       (< 0 (lw-smoothed-ramp-unit-error total error))))
         :hints (("Goal" :use ((:instance lw-seg-positive-product (a error) (b (/ (+ 1 total)))))
                         :in-theory (enable lw-smoothed-ramp-unit-error)))
         :rule-classes nil))

(local (defthm lw-seg-mangoldt-one
         (equal (lw-mangoldt-bounds 1 epsilon) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-mangoldt-bounds)))))

(local (defthm lw-seg-smoothed-zero
         (equal (lw-smoothed-sum-bounds point 0 epsilon) (cons 0 0))
         :hints (("Goal" :expand ((lw-smoothed-sum-bounds point 0 epsilon))))))

(local (defthm lw-seg-smoothed-one
         (equal (lw-smoothed-sum-bounds point 1 epsilon) (cons 0 0))
         :hints (("Goal" :expand ((lw-smoothed-sum-bounds point 1 epsilon))
                         :in-theory (enable lw-interval-add lw-interval-scale)))))

(local (defthm lw-seg-smoothed-step
         (implies (posp count)
                  (equal
                   (car (lw-smoothed-sum-bounds point count epsilon))
                   (+ (* (lw-ramp point count) (car (lw-mangoldt-bounds count epsilon)))
                      (car (lw-smoothed-sum-bounds point (- count 1) epsilon)))))
         :hints (("Goal" :expand ((lw-smoothed-sum-bounds point count epsilon))
                         :in-theory (enable lw-interval-add lw-interval-scale)))
         :rule-classes nil))

(local (defthm lw-seg-extension-zero
         (equal (lw-smoothed-ramp-extension-sum value point 0 total error mangoldt-error) 0)
         :hints (("Goal" :expand ((lw-smoothed-ramp-extension-sum value point 0 total error mangoldt-error))))))

(local (defthm lw-seg-extension-one
         (equal (lw-smoothed-ramp-extension-sum value point 1 total error mangoldt-error) 0)
         :hints (("Goal" :expand ((lw-smoothed-ramp-extension-sum value point 1 total error mangoldt-error))))))

(local (defthm lw-seg-zero-times (equal (* 0 a) 0)))


(local (defthm lw-seg-exponential-data
         (implies (and (rationalp value) (<= 0 value) (rationalp exp-error) (< 0 exp-error))
                  (and (lw-intervalp (lw-exp-bounds value exp-error)) (<= 1 (car (lw-exp-bounds value exp-error)))))
         :hints (("Goal" :use ((:instance lw-exp-bounds-valid (epsilon exp-error)))))
         :rule-classes nil))

(defthm lw-log-ramp-extension-upper
  (implies (and (rationalp value) (rationalp point) (rationalp index) (< 1 index)
                (rationalp log-error) (< 0 log-error))
           (<= (lw-log-ramp-extension value point index log-error) (lw-ramp point index)))
  :hints (("Goal" :in-theory (enable lw-log-ramp-extension lw-ramp))))

(local (defthm lw-seg-weighted-exponential
         (implies
          (and (rationalp value) (<= 0 value) (rationalp exp-error) (< 0 exp-error)
               (integerp index) (< 1 index) (natp total)
               (rationalp error) (< 0 error) (rationalp mangoldt-error) (< 0 mangoldt-error))
          (<= (abs
                (- (* (car (lw-mangoldt-bounds index mangoldt-error)) (lw-ramp (car (lw-exp-bounds value exp-error)) index))
                   (* (car (lw-mangoldt-bounds index mangoldt-error))
                      (lw-log-ramp-extension value (car (lw-exp-bounds value exp-error)) index (lw-smoothed-ramp-log-error index total error)))))
              (+ (lw-smoothed-ramp-unit-error total error) (* 3 exp-error))))
         :hints (("Goal"
                  :use (lw-seg-unit-positive lw-seg-exponential-data
                        (:instance lw-smoothed-ramp-log-error-adequate)
                        (:instance lw-exp-lipschitz-cap-valid (cap index))
                        (:instance lw-seg-positive-product (a (lw-exp-lipschitz-cap index)) (b (lw-smoothed-ramp-log-error index total error)))
                        (:instance lw-mangoldt-lower-coarse (epsilon mangoldt-error))
                        (:instance lw-log-ramp-cutpoint-error
                          (log-error (lw-smoothed-ramp-log-error index total error)) (point (car (lw-exp-bounds value exp-error))) (slack 0))
                        (:instance lw-seg-weighted-error
                          (a (lw-ramp (car (lw-exp-bounds value exp-error)) index))
                          (b (lw-log-ramp-extension value (car (lw-exp-bounds value exp-error)) index (lw-smoothed-ramp-log-error index total error)))
                          (weight (car (lw-mangoldt-bounds index mangoldt-error)))
                          (radius (+ (* (lw-exp-lipschitz-cap index) (lw-smoothed-ramp-log-error index total error)) (* 3 exp-error)))))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-smoothed-ramp-log-error-adequate lw-exp-lipschitz-cap-valid
                                   lw-mangoldt-lower-coarse lw-log-ramp-cutpoint-error))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-smoothed-ramp-exponential-error
  (implies
   (and (rationalp value) (<= 0 value) (rationalp exp-error) (< 0 exp-error)
        (natp count) (natp total) (rationalp error) (< 0 error)
        (rationalp mangoldt-error) (< 0 mangoldt-error))
   (<= (abs (- (car (lw-smoothed-sum-bounds (car (lw-exp-bounds value exp-error)) count mangoldt-error))
                (lw-smoothed-ramp-extension-sum value (car (lw-exp-bounds value exp-error)) count total error mangoldt-error)))
       (* count (+ (lw-smoothed-ramp-unit-error total error) (* 3 exp-error)))))
  :hints
  (("Goal" :induct (lw-smoothed-ramp-extension-sum value (car (lw-exp-bounds value exp-error)) count total error mangoldt-error)
           :in-theory (e/d ((:induction lw-smoothed-ramp-extension-sum))
                           ((:definition lw-smoothed-ramp-extension-sum)
                            lw-smoothed-ramp-extension-sum-rational)))
   (and stable-under-simplificationp
        '(:use (lw-seg-unit-positive lw-seg-exponential-data
                (:instance lw-seg-weighted-exponential (index count))
                (:instance lw-smoothed-sum-bounds-valid
                  (value (car (lw-exp-bounds value exp-error))) (count (- count 1)) (epsilon mangoldt-error))
                (:instance lw-smoothed-ramp-extension-sum-rational (point (car (lw-exp-bounds value exp-error))) (count (- count 1)))
                (:instance lw-seg-smoothed-step (point (car (lw-exp-bounds value exp-error))) (epsilon mangoldt-error))
                (:instance lw-seg-sum-error
                  (a (car (lw-smoothed-sum-bounds (car (lw-exp-bounds value exp-error)) (- count 1) mangoldt-error)))
                  (b (lw-smoothed-ramp-extension-sum value (car (lw-exp-bounds value exp-error)) (- count 1) total error mangoldt-error))
                  (c (* (car (lw-mangoldt-bounds count mangoldt-error)) (lw-ramp (car (lw-exp-bounds value exp-error)) count)))
                  (d (* (car (lw-mangoldt-bounds count mangoldt-error))
                        (lw-log-ramp-extension value (car (lw-exp-bounds value exp-error)) count
                          (lw-smoothed-ramp-log-error count total error))))
                  (radius (* (- count 1) (+ (lw-smoothed-ramp-unit-error total error) (* 3 exp-error))))
                  (other-radius (+ (lw-smoothed-ramp-unit-error total error) (* 3 exp-error)))))
          :expand ((lw-smoothed-ramp-extension-sum value (car (lw-exp-bounds value exp-error)) count total error mangoldt-error))
          :in-theory (e/d (lw-intervalp)
                          (lw-smoothed-sum-bounds-valid lw-smoothed-ramp-extension-sum-rational))
          :nonlinearp nil :do-not-induct t))))

(local (defthm lw-seg-weighted-upper
         (implies (and (rationalp value) (rationalp point) (integerp index) (< 1 index)
                       (natp total) (rationalp error) (< 0 error)
                       (rationalp mangoldt-error) (< 0 mangoldt-error))
                  (<= (* (car (lw-mangoldt-bounds index mangoldt-error))
                         (lw-log-ramp-extension value point index (lw-smoothed-ramp-log-error index total error)))
                      (* (car (lw-mangoldt-bounds index mangoldt-error)) (lw-ramp point index))))
         :hints (("Goal"
                  :use ((:instance lw-smoothed-ramp-log-error-adequate)
                        (:instance lw-mangoldt-lower-coarse (epsilon mangoldt-error))
                        (:instance lw-log-ramp-extension-upper (log-error (lw-smoothed-ramp-log-error index total error)))
                        (:instance lw-seg-multiply-order
                          (a (lw-log-ramp-extension value point index (lw-smoothed-ramp-log-error index total error)))
                          (b (lw-ramp point index)) (factor (car (lw-mangoldt-bounds index mangoldt-error)))))
                  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse
                                      lw-log-ramp-extension-upper)
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-seg-sum-upper
         (implies (and (rationalp value) (rationalp point) (<= 0 point) (natp count) (natp total)
                       (rationalp error) (< 0 error) (rationalp mangoldt-error) (< 0 mangoldt-error))
                  (<= (lw-smoothed-ramp-extension-sum value point count total error mangoldt-error)
                      (car (lw-smoothed-sum-bounds point count mangoldt-error))))
         :hints (("Goal"
                  :induct (lw-smoothed-ramp-extension-sum value point count total error mangoldt-error)
                  :in-theory (e/d ((:induction lw-smoothed-ramp-extension-sum))
                                  ((:definition lw-smoothed-ramp-extension-sum))))
                 (and stable-under-simplificationp
                      '(:use ((:instance lw-seg-weighted-upper (index count))
                              (:instance lw-seg-smoothed-step (epsilon mangoldt-error))
                              (:instance lw-smoothed-ramp-extension-sum-rational (count (- count 1)))
                              (:instance lw-smoothed-sum-bounds-valid
                                (value point) (count (- count 1)) (epsilon mangoldt-error)))
                        :expand ((lw-smoothed-ramp-extension-sum value point count total error mangoldt-error))
                        :in-theory (e/d (lw-intervalp) (lw-smoothed-sum-bounds-valid))
                        :nonlinearp nil :do-not-induct t)))
         :rule-classes nil))

(defthm lw-smoothed-ramp-extension-quadratic-upper
  (implies (and (rationalp value) (rationalp point) (<= 0 point) (natp count) (natp total)
                (rationalp error) (< 0 error) (rationalp mangoldt-error) (< 0 mangoldt-error))
           (<= (lw-smoothed-ramp-extension-sum value point count total error mangoldt-error) (* point point)))
  :hints (("Goal" :use (lw-seg-sum-upper
                         (:instance lw-smoothed-sum-lower-quadratic-growth (value point) (epsilon mangoldt-error)))
                   :in-theory (disable lw-smoothed-sum-lower-quadratic-growth)
                   :do-not-induct t)))

(local (defthm lw-seg-sum-one
         (implies (rationalp value) (equal (lw-exp-sum value 1) (+ 1 value)))
         :hints (("Goal" :expand ((lw-exp-sum value 1) (lw-exp-sum value 0)
                                  (lw-exp-term value 1) (lw-exp-term value 0))))))

(defthm lw-exp-bounds-linear-lower
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (+ 1 value) (car (lw-exp-bounds value error))))
  :hints (("Goal"
           :cases ((equal value 0))
           :use ((:instance lw-exp-bounds-valid (epsilon error))
                 (:instance lw-exp-index-adequate (epsilon error))
                 (:instance lw-exp-sum-monotone-index
                   (small 1) (large (lw-exp-index value error))))
           :in-theory (e/d (lw-exp-bounds lw-exp-band lw-intervalp)
                           (lw-exp-index-adequate))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-seg-count-data
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


(local (defthm lw-seg-cost-lower
         (implies (and (rationalp cap) (<= 0 cap))
                  (and (rationalp (lw-signal-exponential-cost cap)) (<= (* 3 (lw-log-signal-ramp-count cap)) (lw-signal-exponential-cost cap))))
         :hints (("Goal"
                  :use (lw-seg-count-data
                        (:instance lw-seg-positive-product (a (+ (lw-log-signal-ramp-count cap) 1)) (b (lw-log-signal-spatial-cap cap))))
                  :in-theory (enable lw-signal-exponential-cost) :nonlinearp nil))
         :rule-classes nil))

(local (defthm lw-seg-negative-budget
         (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
                  (<= (* (lw-log-signal-ramp-count cap) (+ (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error) (* 3 (lw-signal-exponential-precision cap error)))) error))
         :hints (("Goal"
                  :use (lw-seg-count-data lw-seg-cost-lower lw-signal-exponential-parameters
                        (:instance lw-seg-unit-positive (total (lw-log-signal-ramp-count cap)))
                        (:instance lw-seg-multiply-order
                          (a (* 3 (lw-log-signal-ramp-count cap))) (b (lw-signal-exponential-cost cap)) (factor (lw-signal-exponential-precision cap error))))
                  :in-theory (disable lw-signal-exponential-parameters)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-signal-exponential-global-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp error) (< 0 error))
           (rationalp (lw-signal-exponential-value cap value error)))
  :hints (("Goal"
           :use (lw-signal-exponential-parameters
                 (:instance lw-seg-exponential-data (exp-error (lw-signal-exponential-precision cap error))))
           :in-theory (e/d (lw-signal-exponential-value lw-intervalp)
                           (lw-signal-exponential-parameters))
           :do-not-induct t)))

(local (defthm lw-seg-scalar-growth
         (implies (and (rationalp point) (<= 1 point) (rationalp value) (<= 0 value) (<= value point)
                       (rationalp gamma) (<= -1 gamma) (<= gamma 2)
                       (rationalp total) (rationalp error) (< 0 error)
                       (<= (- error) total) (<= total (* point point)))
                  (<= (abs (+ total (- (* value point)) (* point (+ 1 gamma))))
                      (+ (* 4 point point) error)))
         :hints (("Goal"
                  :use ((:instance lw-seg-multiply-order (a value) (b point) (factor point))
                        (:instance lw-seg-multiply-order (a -1) (b gamma) (factor point))
                        (:instance lw-seg-multiply-order (a gamma) (b 2) (factor point))
                        (:instance lw-seg-multiply-order (a 1) (b point) (factor (* 3 point)))
                        (:instance lw-seg-multiply-order (a 0) (b point) (factor point)))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defthm lw-signal-exponential-global-growth
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp error) (< 0 error))
           (<= (abs (lw-signal-exponential-value cap value error))
               (+ (* 4 (car (lw-exp-bounds value (lw-signal-exponential-precision cap error))) (car (lw-exp-bounds value (lw-signal-exponential-precision cap error)))) error)))
  :hints (("Goal"
           :use (lw-seg-count-data lw-seg-cost-lower lw-seg-negative-budget lw-signal-exponential-parameters
                 (:instance lw-seg-exponential-data (exp-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-exp-bounds-linear-lower (error (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-ramp-exponential-error
                   (exp-error (lw-signal-exponential-precision cap error)) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-ramp-extension-quadratic-upper
                   (point (car (lw-exp-bounds value (lw-signal-exponential-precision cap error)))) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-sum-lower-linear-growth
                   (value (car (lw-exp-bounds value (lw-signal-exponential-precision cap error)))) (count (lw-log-signal-ramp-count cap)) (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-sum-bounds-valid (value (car (lw-exp-bounds value (lw-signal-exponential-precision cap error)))) (count (lw-log-signal-ramp-count cap)) (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-smoothed-ramp-extension-sum-rational
                   (point (car (lw-exp-bounds value (lw-signal-exponential-precision cap error)))) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-euler-bounds-coarse (epsilon (lw-signal-exponential-precision cap error)))
                 (:instance lw-seg-scalar-growth (point (car (lw-exp-bounds value (lw-signal-exponential-precision cap error)))) (gamma (car (lw-euler-bounds (lw-signal-exponential-precision cap error)))) (total (lw-smoothed-ramp-extension-sum value (car (lw-exp-bounds value (lw-signal-exponential-precision cap error))) (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) error (lw-signal-exponential-precision cap error)))))
           :in-theory
           (e/d (lw-signal-exponential-value lw-signal-exponential-linear lw-intervalp)
                (lw-signal-exponential-parameters lw-exp-bounds-linear-lower
                 lw-smoothed-ramp-exponential-error lw-smoothed-ramp-extension-quadratic-upper
                 lw-smoothed-sum-lower-linear-growth lw-smoothed-sum-bounds-valid
                 lw-smoothed-ramp-extension-sum-rational lw-euler-bounds-interval
                 lw-euler-bounds-coarse lw-euler-bounds-overlap))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-signal-exponential-uniform-growth
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value)
                (rationalp error) (< 0 error) (<= error 1))
           (<= (abs (lw-signal-exponential-value cap value error)) (* 5 (car (lw-exp-bounds value (lw-signal-exponential-precision cap error))) (car (lw-exp-bounds value (lw-signal-exponential-precision cap error))))))
  :hints (("Goal"
           :use (lw-signal-exponential-global-growth
                 (:instance lw-seg-exponential-data (exp-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-seg-multiply-order (a 1) (b (car (lw-exp-bounds value (lw-signal-exponential-precision cap error)))) (factor (car (lw-exp-bounds value (lw-signal-exponential-precision cap error))))))
           :in-theory (e/d (lw-intervalp) (lw-signal-exponential-global-growth))
           :nonlinearp nil :do-not-induct t)))
