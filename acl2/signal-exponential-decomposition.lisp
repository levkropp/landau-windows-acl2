(in-package "ACL2")

(include-book "smoothed-ramp-sums")

; Freeze the finite signal decomposition over a compact log interval:
; all Mangoldt and Euler approximations and all logarithmic breakpoints
; are fixed, while the variable enters through u and exp(u).

(local (in-theory
        (disable lw-smoothed-sum-bounds lw-mangoldt-bounds lw-ramp
                 lw-log-ramp-extension lw-exp-lipschitz-cap
                 lw-log-signal-point lw-log-signal-delta lw-log-signal-cap
                 lw-log-signal-margin lw-log-signal-lipschitz lw-log-signal-budget
                 lw-log-signal-spatial-cap lw-signal-count lw-signal-precision
                 lw-log-signal-linear-precision lw-interval-add lw-interval-scale
                 lw-log-bounds lw-euler-bounds lw-exp-bounds lw-exp-index lw-exp-term lw-exp-sum
                 lw-smoothed-ramp-unit-error lw-smoothed-ramp-log-error lw-log-signal-ramp-count
                 lw-smoothed-ramp-extension-sum lw-smoothed-sum-bounds-zero-tail)))

(local (defthm lw-ser-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-ser-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ser-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-ser-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ser-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-ser-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-ser-left-commutes)))))
(local (defthm lw-ser-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-ser-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-ser-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-ser-sum-error
         (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- c d)) other-radius))
                  (<= (abs (- (+ a c) (+ b d))) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= c d)))) :rule-classes nil))
(local (defthm lw-ser-weighted-error
         (implies
          (and (rationalp a) (rationalp b) (rationalp weight) (<= 0 weight)
               (rationalp index) (< 0 index) (<= weight index)
               (rationalp radius) (<= 0 radius) (<= (abs (- a b)) (* radius (/ index))))
          (<= (abs (- (* weight a) (* weight b))) radius))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x index))
                        (:instance lw-ser-multiply-order
                          (a (abs (- a b))) (b (* radius (/ index))) (factor weight))
                        (:instance lw-ser-multiply-order
                          (a weight) (b index) (factor (* radius (/ index)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))


(defthm lw-smoothed-sum-lower-cauchy
  (implies (and (rationalp point) (<= 1 point) (natp count)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-smoothed-sum-bounds point count left-error))
                        (car (lw-smoothed-sum-bounds point count right-error))))
               (* count point (+ left-error right-error))))
  :hints (("Goal"
           :use ((:instance lw-smoothed-sum-bounds-valid (value point) (epsilon left-error))
                 (:instance lw-smoothed-sum-bounds-valid (value point) (epsilon right-error))
                 (:instance lw-smoothed-sum-bounds-width (value point) (epsilon left-error))
                 (:instance lw-smoothed-sum-bounds-width (value point) (epsilon right-error))
                 (:instance lw-smoothed-sum-bounds-transport (left point) (right point))
                 (:instance lw-smoothed-sum-bounds-transport
                   (left point) (right point) (left-error right-error) (right-error left-error)))
           :in-theory (e/d (lw-intervalp)
                           (lw-smoothed-sum-bounds-valid lw-smoothed-sum-bounds-width
                            lw-smoothed-sum-bounds-transport))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-ser-extension-point
         (implies (and (rationalp value) (rationalp left) (rationalp right)
                       (rationalp index) (< 1 index) (rationalp log-error) (< 0 log-error))
                  (<= (abs (- (lw-log-ramp-extension value left index log-error)
                              (lw-log-ramp-extension value right index log-error)))
                      (* (abs (- left right)) (/ index))))
         :hints (("Goal"
                  :use ((:instance lw-ser-multiply-order (a left) (b right) (factor (/ index)))
                        (:instance lw-ser-multiply-order (a right) (b left) (factor (/ index))))
                  :in-theory (enable lw-log-ramp-extension) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-ser-weighted-point
         (implies (and (rationalp value) (rationalp left) (rationalp right)
                       (integerp index) (< 1 index) (natp total)
                       (rationalp error) (< 0 error)
                       (rationalp mangoldt-error) (< 0 mangoldt-error))
                  (<= (abs
                        (- (* (car (lw-mangoldt-bounds index mangoldt-error))
                              (lw-log-ramp-extension value left index (lw-smoothed-ramp-log-error index total error)))
                           (* (car (lw-mangoldt-bounds index mangoldt-error))
                              (lw-log-ramp-extension value right index (lw-smoothed-ramp-log-error index total error)))))
                      (abs (- left right))))
         :hints (("Goal"
                  :use ((:instance lw-smoothed-ramp-log-error-adequate)
                        (:instance lw-mangoldt-lower-coarse (epsilon mangoldt-error))
                        (:instance lw-ser-extension-point
                          (log-error (lw-smoothed-ramp-log-error index total error)))
                        (:instance lw-ser-weighted-error
                          (a (lw-log-ramp-extension value left index (lw-smoothed-ramp-log-error index total error)))
                          (b (lw-log-ramp-extension value right index (lw-smoothed-ramp-log-error index total error)))
                          (weight (car (lw-mangoldt-bounds index mangoldt-error))) (radius (abs (- left right)))))
                  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-ser-extension-zero
         (equal (lw-smoothed-ramp-extension-sum value point 0 total error mangoldt-error) 0)
         :hints (("Goal" :expand ((lw-smoothed-ramp-extension-sum value point 0 total error mangoldt-error))))))

(local (defthm lw-ser-extension-one
         (equal (lw-smoothed-ramp-extension-sum value point 1 total error mangoldt-error) 0)
         :hints (("Goal" :expand ((lw-smoothed-ramp-extension-sum value point 1 total error mangoldt-error))))))

(local (defthm lw-ser-zero-times (equal (* 0 a) 0)))

(defthm lw-smoothed-ramp-extension-point-bound
  (implies (and (rationalp value) (rationalp left) (rationalp right) (natp count) (natp total)
                (rationalp error) (< 0 error) (rationalp mangoldt-error) (< 0 mangoldt-error))
           (<= (abs
                 (- (lw-smoothed-ramp-extension-sum value left count total error mangoldt-error)
                    (lw-smoothed-ramp-extension-sum value right count total error mangoldt-error)))
               (* count (abs (- left right)))))
  :hints (("Goal" :induct (lw-smoothed-ramp-extension-sum value left count total error mangoldt-error)
                   :in-theory (e/d ((:induction lw-smoothed-ramp-extension-sum))
                                   ((:definition lw-smoothed-ramp-extension-sum))))
          (and stable-under-simplificationp
               '(:use ((:instance lw-ser-weighted-point (index count))
                       (:instance lw-smoothed-ramp-extension-sum-rational (point left) (count (- count 1)))
                       (:instance lw-smoothed-ramp-extension-sum-rational (point right) (count (- count 1)))
                       (:instance lw-ser-sum-error
                         (a (lw-smoothed-ramp-extension-sum value left (- count 1) total error mangoldt-error))
                         (b (lw-smoothed-ramp-extension-sum value right (- count 1) total error mangoldt-error))
                         (c (* (car (lw-mangoldt-bounds count mangoldt-error))
                               (lw-log-ramp-extension value left count (lw-smoothed-ramp-log-error count total error))))
                         (d (* (car (lw-mangoldt-bounds count mangoldt-error))
                               (lw-log-ramp-extension value right count (lw-smoothed-ramp-log-error count total error))))
                         (radius (* (- count 1) (abs (- left right)))) (other-radius (abs (- left right)))))
                 :expand ((lw-smoothed-ramp-extension-sum value left count total error mangoldt-error)
                          (lw-smoothed-ramp-extension-sum value right count total error mangoldt-error))
                 :nonlinearp nil :do-not-induct t))))

(local (defthm lw-ser-primitive-scalar
         (implies (and (rationalp point) (<= 1 point) (natp count)
                       (rationalp budget) (< 0 budget) (rationalp error) (< 0 error) (<= budget error))
                  (<= (/ (* 1/2 budget) (+ 1 (* (+ count 2) point))) error))
         :hints (("Goal"
                  :use ((:instance lw-positive-division-bound
                          (numerator (* 1/2 budget)) (divisor (+ 1 (* (+ count 2) point))) (bound error)))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(defthm lw-log-signal-primitive-error-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (let ((epsilon (lw-log-signal-linear-precision value error)))
             (and (rationalp epsilon) (< 0 epsilon) (<= epsilon error))))
  :hints (("Goal"
           :use (lw-log-signal-budget-valid lw-log-signal-point-valid
                 (:instance lw-signal-precision-positive (value (lw-log-signal-point value error))
                   (ceiling 0) (error (* 1/2 (lw-log-signal-budget error))))
                 (:instance lw-ser-primitive-scalar
                   (point (lw-log-signal-point value error)) (count (lw-signal-count (lw-log-signal-point value error)))
                   (budget (lw-log-signal-budget error))))
           :in-theory (e/d (lw-log-signal-linear-precision lw-signal-precision lw-signal-error-factor)
                           (lw-log-signal-budget-valid lw-log-signal-point-valid lw-signal-precision-positive))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-log-signal-point-exponential-error
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (abs (- (lw-log-signal-point value error) (car (lw-exp-bounds value error))))
               (* 3 error)))
  :hints (("Goal"
           :use (lw-log-signal-delta-valid lw-log-signal-delta-budget
                 (:instance lw-exp-bounds-valid (epsilon error))
                 (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value error)))
                 (:instance lw-exp-bounds-lower-cauchy
                   (left-error (lw-log-signal-delta value error)) (right-error error)))
           :in-theory (e/d (lw-log-signal-point lw-intervalp)
                           (lw-log-signal-delta-valid lw-log-signal-delta-budget lw-exp-bounds-valid
                            lw-exp-bounds-lower-cauchy))
           :nonlinearp nil :do-not-induct t)))

(defun lw-signal-exponential-linear (cap value point log-error primitive-error)
  (let ((count (lw-log-signal-ramp-count cap)))
    (+ (lw-smoothed-ramp-extension-sum value point count count log-error primitive-error)
       (- (* point value)) (* point (+ 1 (car (lw-euler-bounds primitive-error)))))))

(local (defthm lw-ser-count-data
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

(defthm lw-signal-exponential-linear-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (rationalp point)
                (rationalp log-error) (< 0 log-error)
                (rationalp primitive-error) (< 0 primitive-error))
           (rationalp (lw-signal-exponential-linear cap value point log-error primitive-error)))
  :hints (("Goal"
           :use (lw-ser-count-data (:instance lw-euler-bounds-interval (epsilon primitive-error)))
           :in-theory (e/d (lw-intervalp) (lw-euler-bounds-interval))
           :do-not-induct t)))

(local (defthm lw-ser-prediction-point
         (implies
          (and (rationalp a) (rationalp b) (rationalp left) (rationalp right)
               (natp count) (rationalp value) (<= 0 value)
               (rationalp cap) (<= value cap)
               (rationalp gamma) (<= -1 gamma) (<= gamma 2)
               (<= (abs (- a b)) (* count (abs (- left right)))))
          (<= (abs (- (+ a (- (* left value)) (* left (+ 1 gamma)))
                      (+ b (- (* right value)) (* right (+ 1 gamma)))))
              (* (+ count cap 3) (abs (- left right)))))
         :hints (("Goal"
                  :cases ((<= left right))
                  :use ((:instance lw-ser-multiply-order
                          (a (abs (- left right))) (b (abs (- left right))) (factor value))
                        (:instance lw-ser-multiply-order
                          (a value) (b cap) (factor (abs (- left right))))
                        (:instance lw-ser-multiply-order
                          (a (+ 1 gamma)) (b 3) (factor (abs (- left right)))))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(defthm lw-signal-exponential-linear-point-bound
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
        (rationalp left) (rationalp right)
        (rationalp log-error) (< 0 log-error)
        (rationalp primitive-error) (< 0 primitive-error) (<= primitive-error 1))
   (<= (abs (- (lw-signal-exponential-linear cap value left log-error primitive-error)
               (lw-signal-exponential-linear cap value right log-error primitive-error)))
       (* (+ (lw-log-signal-ramp-count cap) cap 3) (abs (- left right)))))
  :hints (("Goal"
           :use (lw-ser-count-data
                 (:instance lw-euler-bounds-interval (epsilon primitive-error))
                 (:instance lw-euler-bounds-coarse (epsilon primitive-error))
                 (:instance lw-smoothed-ramp-extension-point-bound
                   (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap))
                   (error log-error) (mangoldt-error primitive-error))
                 (:instance lw-ser-prediction-point
                   (a (lw-smoothed-ramp-extension-sum value left (lw-log-signal-ramp-count cap)
                        (lw-log-signal-ramp-count cap) log-error primitive-error))
                   (b (lw-smoothed-ramp-extension-sum value right (lw-log-signal-ramp-count cap)
                        (lw-log-signal-ramp-count cap) log-error primitive-error))
                   (count (lw-log-signal-ramp-count cap)) (gamma (car (lw-euler-bounds primitive-error)))))
           :in-theory (e/d (lw-intervalp)
                           (lw-euler-bounds-interval lw-euler-bounds-coarse lw-euler-bounds-overlap
                            lw-smoothed-ramp-extension-point-bound))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-ser-source-data
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp source-error) (< 0 source-error))
                  (and (posp (lw-log-signal-ramp-count cap)) (rationalp (lw-log-signal-spatial-cap cap)) (<= 3 (lw-log-signal-spatial-cap cap))
                       (<= (lw-log-signal-spatial-cap cap) (lw-log-signal-ramp-count cap))
                       (rationalp (lw-log-signal-point value source-error)) (< 1 (lw-log-signal-point value source-error)) (<= (lw-log-signal-point value source-error) (lw-log-signal-spatial-cap cap)) (<= (lw-log-signal-point value source-error) (lw-log-signal-ramp-count cap))
                       (rationalp (lw-log-signal-linear-precision value source-error)) (< 0 (lw-log-signal-linear-precision value source-error)) (<= (lw-log-signal-linear-precision value source-error) source-error)
                       (rationalp (lw-log-signal-delta value source-error)) (< 0 (lw-log-signal-delta value source-error)) (<= (lw-log-signal-delta value source-error) source-error)
                       (rationalp (car (lw-exp-bounds value source-error)))
                       (<= 1 (car (lw-exp-bounds value source-error)))))
         :hints (("Goal"
                  :use (lw-ser-count-data
                        (:instance lw-log-signal-point-valid (error source-error))
                        (:instance lw-log-signal-point-spatial-cap (error source-error))
                        (:instance lw-log-signal-primitive-error-bound (error source-error))
                        (:instance lw-log-signal-delta-valid (error source-error))
                        (:instance lw-log-signal-delta-budget (error source-error))
                        (:instance lw-exp-bounds-valid (epsilon source-error)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-log-signal-point-valid lw-log-signal-point-spatial-cap
                                   lw-log-signal-primitive-error-bound lw-log-signal-delta-valid
                                   lw-log-signal-delta-budget lw-exp-bounds-valid))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-ser-unit-data
         (implies (and (natp count) (rationalp error) (< 0 error))
                  (and (rationalp (lw-smoothed-ramp-unit-error count error))
                       (< 0 (lw-smoothed-ramp-unit-error count error))
                       (<= (* count (lw-smoothed-ramp-unit-error count error)) (* 1/16 error))))
         :hints (("Goal"
                  :use ((:instance lw-ser-positive-product (a error) (b (/ (+ 1 count))))
                        (:instance lw-positive-division-bound
                          (numerator (* count error)) (divisor (+ 1 count)) (bound error)))
                  :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp nil))
         :rule-classes nil))

(local (defthm lw-ser-correction-error
         (implies (and (rationalp a) (rationalp b) (rationalp g) (rationalp h)
                       (rationalp point) (<= 0 point) (rationalp value)
                       (rationalp radius) (rationalp gamma-error)
                       (<= (abs (- a b)) radius) (<= (abs (- g h)) gamma-error))
                  (<= (abs (- (+ a (- (* point value)) (* point (+ 1 g)))
                              (+ b (- (* point value)) (* point (+ 1 h)))))
                      (+ radius (* point gamma-error))))
         :hints (("Goal" :cases ((<= g h) (<= a b))
                         :use ((:instance lw-ser-multiply-order
                                 (a (abs (- g h))) (b gamma-error) (factor point)))
                         :nonlinearp t :do-not-induct t)) :rule-classes nil))

(local (defthm lw-ser-freeze-coarsen
         (implies (and (natp count) (rationalp point) (<= 1 point) (rationalp cap) (<= point cap)
                       (rationalp source-error) (< 0 source-error)
                       (rationalp epsilon) (< 0 epsilon) (<= epsilon source-error))
                  (<= (* (+ count 1) point (+ epsilon source-error))
                      (* 2 (+ count 1) cap source-error)))
         :hints (("Goal"
                  :use ((:instance lw-ser-multiply-order
                          (a (+ epsilon source-error)) (b (* 2 source-error)) (factor (* (+ count 1) point)))
                        (:instance lw-ser-multiply-order
                          (a point) (b cap) (factor (* 2 (+ count 1) source-error))))
                  :nonlinearp t :do-not-induct t)) :rule-classes nil))

(local (defun lw-ser-frozen-raw (cap value source-error)
         (+ (car (lw-smoothed-sum-bounds (lw-log-signal-point value source-error) (lw-log-signal-ramp-count cap) source-error)) (- (* (lw-log-signal-point value source-error) value)) (* (lw-log-signal-point value source-error) (+ 1 (car (lw-euler-bounds source-error)))))))

(local (defthm lw-ser-frozen-rational
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp source-error) (< 0 source-error))
                  (rationalp (lw-ser-frozen-raw cap value source-error)))
         :hints (("Goal"
                  :use (lw-ser-source-data
                        (:instance lw-smoothed-sum-bounds-valid (value (lw-log-signal-point value source-error)) (count (lw-log-signal-ramp-count cap)) (epsilon source-error))
                        (:instance lw-euler-bounds-interval (epsilon source-error)))
                  :in-theory (e/d (lw-intervalp) (lw-smoothed-sum-bounds-valid lw-euler-bounds-interval))
                  :do-not-induct t))))

(local (defthm lw-ser-freeze-raw-error
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp source-error) (< 0 source-error))
                  (<= (abs (- (lw-log-signal-linear-value value source-error) (lw-ser-frozen-raw cap value source-error))) (* 2 (+ 1 (lw-log-signal-ramp-count cap)) (lw-log-signal-spatial-cap cap) source-error)))
         :hints (("Goal"
                  :use (lw-ser-source-data
                        (:instance lw-signal-count-covers (value (lw-log-signal-point value source-error)))
                        (:instance lw-smoothed-sum-bounds-stable-count
                          (value (lw-log-signal-point value source-error)) (left-count (lw-signal-count (lw-log-signal-point value source-error))) (right-count (lw-log-signal-ramp-count cap)) (epsilon (lw-log-signal-linear-precision value source-error)))
                        (:instance lw-smoothed-sum-lower-cauchy
                          (point (lw-log-signal-point value source-error)) (count (lw-log-signal-ramp-count cap)) (left-error (lw-log-signal-linear-precision value source-error)) (right-error source-error))
                        (:instance lw-euler-lower-cauchy (left-error (lw-log-signal-linear-precision value source-error)) (right-error source-error))
                        (:instance lw-smoothed-sum-bounds-valid (value (lw-log-signal-point value source-error)) (count (lw-log-signal-ramp-count cap)) (epsilon (lw-log-signal-linear-precision value source-error)))
                        (:instance lw-smoothed-sum-bounds-valid (value (lw-log-signal-point value source-error)) (count (lw-log-signal-ramp-count cap)) (epsilon source-error))
                        (:instance lw-euler-bounds-interval (epsilon (lw-log-signal-linear-precision value source-error)))
                        (:instance lw-euler-bounds-interval (epsilon source-error))
                        (:instance lw-ser-correction-error (a (car (lw-smoothed-sum-bounds (lw-log-signal-point value source-error) (lw-signal-count (lw-log-signal-point value source-error)) (lw-log-signal-linear-precision value source-error)))) (b (car (lw-smoothed-sum-bounds (lw-log-signal-point value source-error) (lw-log-signal-ramp-count cap) source-error))) (g (car (lw-euler-bounds (lw-log-signal-linear-precision value source-error)))) (h (car (lw-euler-bounds source-error)))
                          (point (lw-log-signal-point value source-error)) (radius (* (lw-log-signal-ramp-count cap) (lw-log-signal-point value source-error) (+ (lw-log-signal-linear-precision value source-error) source-error)))
                          (gamma-error (+ (lw-log-signal-linear-precision value source-error) source-error)))
                        (:instance lw-ser-freeze-coarsen (count (lw-log-signal-ramp-count cap)) (point (lw-log-signal-point value source-error)) (cap (lw-log-signal-spatial-cap cap)) (epsilon (lw-log-signal-linear-precision value source-error))))
                  :in-theory
                  (e/d (lw-log-signal-linear-value lw-intervalp)
                       (lw-signal-count-covers lw-smoothed-sum-lower-cauchy lw-euler-lower-cauchy
                        lw-log-signal-point-valid lw-log-signal-primitive-error-bound
                        lw-log-signal-delta-valid lw-log-signal-delta-budget
                        lw-smoothed-sum-bounds-valid lw-euler-bounds-interval))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-ser-triangle
         (implies (and (rationalp a) (rationalp b) (rationalp c)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- b c)) other-radius))
                  (<= (abs (- a c)) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= b c)))) :rule-classes nil))

(local (defthm lw-ser-source-raw-error
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp source-error) (< 0 source-error))
                  (<= (abs (- (car (lw-log-signal-bounds value source-error)) (lw-ser-frozen-raw cap value source-error))) (+ source-error (* 2 (+ 1 (lw-log-signal-ramp-count cap)) (lw-log-signal-spatial-cap cap) source-error))))
         :hints (("Goal"
                  :use (lw-ser-source-data lw-ser-frozen-rational lw-ser-freeze-raw-error
                        (:instance lw-log-signal-computed-linearization (error source-error))
                        (:instance lw-log-signal-linear-value-rational (error source-error))
                        (:instance lw-log-signal-bounds-valid (error source-error))
                        (:instance lw-ser-triangle (a (car (lw-log-signal-bounds value source-error))) (b (lw-log-signal-linear-value value source-error)) (c (lw-ser-frozen-raw cap value source-error))
                          (radius source-error) (other-radius (* 2 (+ 1 (lw-log-signal-ramp-count cap)) (lw-log-signal-spatial-cap cap) source-error))))
                  :in-theory
                  (e/d (lw-intervalp)
                       (lw-log-signal-computed-linearization lw-log-signal-linear-value-rational
                        lw-log-signal-bounds-valid lw-ser-frozen-rational))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-ser-raw-ramp-error
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp source-error) (< 0 source-error) (rationalp error) (< 0 error))
                  (<= (abs (- (lw-ser-frozen-raw cap value source-error) (lw-signal-exponential-linear cap value (lw-log-signal-point value source-error) error source-error))) (* (lw-log-signal-ramp-count cap) (+ (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error) (* 4 (lw-log-signal-delta value source-error))))))
         :hints (("Goal"
                  :use (lw-ser-source-data
                        (:instance lw-smoothed-ramp-sum-cutpoint-error
                          (signal-error source-error) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error source-error))
                        (:instance lw-smoothed-sum-bounds-valid (value (lw-log-signal-point value source-error)) (count (lw-log-signal-ramp-count cap)) (epsilon source-error))
                        (:instance lw-euler-bounds-interval (epsilon source-error)))
                  :in-theory (e/d (lw-signal-exponential-linear lw-intervalp)
                                  (lw-smoothed-ramp-sum-cutpoint-error lw-smoothed-sum-bounds-valid lw-euler-bounds-interval))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-ser-source-ramp-error
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp source-error) (< 0 source-error) (rationalp error) (< 0 error))
                  (<= (abs (- (car (lw-log-signal-bounds value source-error)) (lw-signal-exponential-linear cap value (lw-log-signal-point value source-error) error source-error))) (+ source-error (* 2 (+ 1 (lw-log-signal-ramp-count cap)) (lw-log-signal-spatial-cap cap) source-error) (* (lw-log-signal-ramp-count cap) (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error)) (* 4 (lw-log-signal-ramp-count cap) source-error))))
         :hints (("Goal"
                  :use (lw-ser-source-data lw-ser-source-raw-error lw-ser-raw-ramp-error lw-ser-frozen-rational
                        (:instance lw-ser-unit-data (count (lw-log-signal-ramp-count cap)))
                        (:instance lw-signal-exponential-linear-rational
                          (point (lw-log-signal-point value source-error)) (log-error error) (primitive-error source-error))
                        (:instance lw-log-signal-bounds-valid (error source-error))
                        (:instance lw-ser-multiply-order (a (lw-log-signal-delta value source-error)) (b source-error) (factor (* 4 (lw-log-signal-ramp-count cap))))
                        (:instance lw-ser-triangle (a (car (lw-log-signal-bounds value source-error))) (b (lw-ser-frozen-raw cap value source-error)) (c (lw-signal-exponential-linear cap value (lw-log-signal-point value source-error) error source-error))
                          (radius (+ source-error (* 2 (+ 1 (lw-log-signal-ramp-count cap)) (lw-log-signal-spatial-cap cap) source-error))) (other-radius (* (lw-log-signal-ramp-count cap) (+ (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error) (* 4 (lw-log-signal-delta value source-error)))))))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-log-signal-bounds-valid lw-ser-frozen-rational
                                   lw-signal-exponential-linear-rational
                                   lw-log-signal-point-valid lw-log-signal-primitive-error-bound
                                   lw-log-signal-delta-valid lw-log-signal-delta-budget))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defun lw-signal-exponential-cost (cap)
  (let ((count (lw-log-signal-ramp-count cap)))
    (+ 1 (* 2 (+ count 1) (lw-log-signal-spatial-cap cap))
       (* 4 count) (* 3 (+ count cap 3)))))

(defun lw-signal-exponential-precision (cap error)
  (min 1 (/ error (* 16 (lw-signal-exponential-cost cap)))))

(defun lw-signal-exponential-value (cap value error)
  (let ((epsilon (lw-signal-exponential-precision cap error)))
    (lw-signal-exponential-linear cap value (car (lw-exp-bounds value epsilon)) error epsilon)))

(local (defthm lw-ser-canonical-error
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp source-error) (< 0 source-error) (<= source-error 1)
                       (rationalp error) (< 0 error))
                  (<= (abs (- (car (lw-log-signal-bounds value source-error)) (lw-signal-exponential-linear cap value (car (lw-exp-bounds value source-error)) error source-error)))
                      (+ (* (lw-signal-exponential-cost cap) source-error)
                         (* (lw-log-signal-ramp-count cap) (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error)))))
         :hints (("Goal"
                  :use (lw-ser-source-data lw-ser-source-ramp-error
                        (:instance lw-ser-unit-data (count (lw-log-signal-ramp-count cap)))
                        (:instance lw-log-signal-bounds-valid (error source-error))
                        (:instance lw-log-signal-point-exponential-error (error source-error))
                        (:instance lw-signal-exponential-linear-rational
                          (point (lw-log-signal-point value source-error)) (log-error error) (primitive-error source-error))
                        (:instance lw-signal-exponential-linear-rational
                          (point (car (lw-exp-bounds value source-error))) (log-error error) (primitive-error source-error))
                        (:instance lw-signal-exponential-linear-point-bound
                          (left (lw-log-signal-point value source-error)) (right (car (lw-exp-bounds value source-error))) (log-error error) (primitive-error source-error))
                        (:instance lw-ser-multiply-order (a (abs (- (lw-log-signal-point value source-error) (car (lw-exp-bounds value source-error)))))
                          (b (* 3 source-error)) (factor (+ (lw-log-signal-ramp-count cap) cap 3)))
                        (:instance lw-ser-triangle (a (car (lw-log-signal-bounds value source-error))) (b (lw-signal-exponential-linear cap value (lw-log-signal-point value source-error) error source-error)) (c (lw-signal-exponential-linear cap value (car (lw-exp-bounds value source-error)) error source-error))
                          (radius (+ source-error (* 2 (+ 1 (lw-log-signal-ramp-count cap)) (lw-log-signal-spatial-cap cap) source-error) (* (lw-log-signal-ramp-count cap) (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error)) (* 4 (lw-log-signal-ramp-count cap) source-error))) (other-radius (* (+ (lw-log-signal-ramp-count cap) cap 3) (abs (- (lw-log-signal-point value source-error) (car (lw-exp-bounds value source-error))))))))
                  :in-theory (e/d (lw-signal-exponential-cost lw-intervalp)
                                  (lw-log-signal-bounds-valid lw-log-signal-point-exponential-error
                                   lw-signal-exponential-linear-rational
                                   lw-signal-exponential-linear-point-bound))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-ser-cost-data
         (implies (and (rationalp cap) (<= 0 cap))
                  (and (rationalp (lw-signal-exponential-cost cap))
                       (<= 1 (lw-signal-exponential-cost cap))))
         :hints (("Goal"
                  :use (lw-ser-count-data
                        (:instance lw-ser-positive-product
                          (a (+ 1 (lw-log-signal-ramp-count cap))) (b (lw-log-signal-spatial-cap cap))))
                  :in-theory (enable lw-signal-exponential-cost) :nonlinearp nil))
         :rule-classes nil))

(local (defthm lw-ser-precision-data
         (implies (and (rationalp cost) (<= 1 cost) (rationalp error) (< 0 error))
                  (let ((delta (min 1 (/ error (* 16 cost)))))
                    (and (rationalp delta) (< 0 delta) (<= delta 1)
                         (<= (* cost delta) (* 1/16 error)))))
         :hints (("Goal"
                  :use ((:instance lw-ser-multiply-order
                          (a (min 1 (/ error (* 16 cost)))) (b (/ error (* 16 cost))) (factor cost))
                        (:instance lw-positive-division-bound
                          (numerator (* cost error)) (divisor (* 16 cost)) (bound (* 1/16 error))))
                  :nonlinearp t :do-not-induct t)) :rule-classes nil))

(defthm lw-signal-exponential-parameters
  (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
           (let ((epsilon (lw-signal-exponential-precision cap error)))
             (and (rationalp epsilon) (< 0 epsilon) (<= epsilon 1)
                  (<= (+ (* (lw-signal-exponential-cost cap) epsilon)
                         (* (lw-log-signal-ramp-count cap) (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error))) error)
                  (<= (+ (* 2 (lw-signal-exponential-cost cap) epsilon)
                         (* (lw-log-signal-ramp-count cap) (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error))) error))))
  :hints (("Goal"
           :use (lw-ser-cost-data lw-ser-count-data
                 (:instance lw-ser-precision-data (cost (lw-signal-exponential-cost cap)))
                 (:instance lw-ser-unit-data (count (lw-log-signal-ramp-count cap))))
           :in-theory (enable lw-signal-exponential-precision)
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-signal-exponential-cost lw-signal-exponential-precision
                 lw-signal-exponential-linear lw-log-signal-bounds)))

(defthm lw-signal-exponential-value-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error))
           (rationalp (lw-signal-exponential-value cap value error)))
  :hints (("Goal"
           :use (lw-signal-exponential-parameters
                 (:instance lw-exp-bounds-valid (epsilon (lw-signal-exponential-precision cap error))))
           :in-theory (e/d (lw-intervalp) (lw-signal-exponential-parameters lw-exp-bounds-valid))
           :do-not-induct t)))

(defthm lw-signal-exponential-computed-decomposition
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error))
           (<= (abs (- (car (lw-log-signal-bounds value (lw-signal-exponential-precision cap error))) (lw-signal-exponential-value cap value error))) error))
  :hints (("Goal"
           :use (lw-signal-exponential-parameters
                 (:instance lw-ser-canonical-error (source-error (lw-signal-exponential-precision cap error))))
           :in-theory (disable lw-signal-exponential-parameters)
           :nonlinearp nil :do-not-induct t)))

(defthm lw-signal-exponential-independent-error
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error) (rationalp signal-error) (< 0 signal-error))
           (<= (abs (- (car (lw-log-signal-bounds value signal-error)) (lw-signal-exponential-value cap value error))) (+ signal-error error)))
  :hints (("Goal"
           :use (lw-signal-exponential-parameters lw-ser-count-data lw-ser-cost-data
                 lw-signal-exponential-value-rational
                 (:instance lw-ser-unit-data (count (lw-log-signal-ramp-count cap)))
                 (:instance lw-ser-canonical-error (source-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-log-signal-lower-cauchy (left-error signal-error) (right-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-log-signal-bounds-valid (error signal-error))
                 (:instance lw-log-signal-bounds-valid (error (lw-signal-exponential-precision cap error)))
                 (:instance lw-ser-multiply-order
                   (a 1) (b (lw-signal-exponential-cost cap)) (factor (lw-signal-exponential-precision cap error)))
                 (:instance lw-ser-triangle (a (car (lw-log-signal-bounds value signal-error))) (b (car (lw-log-signal-bounds value (lw-signal-exponential-precision cap error)))) (c (lw-signal-exponential-value cap value error))
                   (radius (+ signal-error (lw-signal-exponential-precision cap error))) (other-radius (+ (* (lw-signal-exponential-cost cap) (lw-signal-exponential-precision cap error)) (* (lw-log-signal-ramp-count cap) (lw-smoothed-ramp-unit-error (lw-log-signal-ramp-count cap) error))))))
           :in-theory (e/d (lw-intervalp)
                           (lw-signal-exponential-parameters lw-signal-exponential-value-rational
                            lw-log-signal-lower-cauchy lw-log-signal-bounds-valid))
           :nonlinearp nil :do-not-induct t)))
