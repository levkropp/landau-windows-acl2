(in-package "ACL2")

(include-book "exp-log-ramp")
(include-book "log-signal-continuity")

; Assemble logarithmic breakpoint errors with the actual Mangoldt
; coefficients and the padded prime sum used by the signal evaluator.

(local (in-theory
        (disable lw-smoothed-sum-bounds lw-mangoldt-bounds lw-ramp
                 lw-log-ramp-extension lw-exp-lipschitz-cap
                 lw-log-signal-point lw-log-signal-delta lw-log-signal-cap
                 lw-log-signal-margin lw-log-signal-lipschitz lw-log-signal-budget
                 lw-log-signal-spatial-cap lw-signal-count lw-signal-precision
                 lw-log-signal-linear-precision lw-interval-add lw-interval-scale)))

(local (defthm lw-srs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-srs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-srs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-srs-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-srs-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-srs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-srs-left-commutes)))))
(local (defthm lw-srs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-srs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-srs-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-srs-sum-error
         (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- c d)) other-radius))
                  (<= (abs (- (+ a c) (+ b d))) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= c d)))) :rule-classes nil))
(local (defthm lw-srs-weighted-error
         (implies
          (and (rationalp a) (rationalp b) (rationalp weight) (<= 0 weight)
               (rationalp index) (< 0 index) (<= weight index)
               (rationalp radius) (<= 0 radius) (<= (abs (- a b)) (* radius (/ index))))
          (<= (abs (- (* weight a) (* weight b))) radius))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x index))
                        (:instance lw-srs-multiply-order
                          (a (abs (- a b))) (b (* radius (/ index))) (factor weight))
                        (:instance lw-srs-multiply-order
                          (a weight) (b index) (factor (* radius (/ index)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(defun lw-smoothed-ramp-unit-error (total error) (* 1/16 error (/ (+ 1 total))))

(defun lw-smoothed-ramp-log-error (index total error)
  (min 1 (/ (lw-smoothed-ramp-unit-error total error) (lw-exp-lipschitz-cap index))))

(local (defthm lw-srs-small-precision
         (implies (and (rationalp slope) (< 0 slope) (rationalp budget) (< 0 budget))
                  (let ((delta (min 1 (/ budget slope))))
                    (and (rationalp delta) (< 0 delta) (<= delta 1) (<= (* slope delta) budget))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x slope))
                        (:instance lw-srs-multiply-order
                          (a (min 1 (/ budget slope))) (b (/ budget slope)) (factor slope)))
                  :in-theory (disable inverse-of-*) :nonlinearp nil))
         :rule-classes nil))

(defthm lw-smoothed-ramp-log-error-adequate
  (implies (and (natp index) (natp total) (rationalp error) (< 0 error))
           (let ((delta (lw-smoothed-ramp-log-error index total error)))
             (and (rationalp delta) (< 0 delta) (<= delta 1)
                  (<= (* (lw-exp-lipschitz-cap index) delta) (lw-smoothed-ramp-unit-error total error)))))
  :hints (("Goal"
           :use ((:instance lw-exp-lipschitz-cap-valid (cap index))
                 (:instance lw-srs-positive-product (a error) (b (/ (+ 1 total))))
                 (:instance lw-srs-small-precision
                   (slope (lw-exp-lipschitz-cap index)) (budget (lw-smoothed-ramp-unit-error total error))))
           :in-theory (disable lw-exp-lipschitz-cap-valid)
           :nonlinearp nil :do-not-induct t)))

(defun lw-smoothed-ramp-extension-sum (value point count total error mangoldt-error)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1)) 0
    (+ (* (car (lw-mangoldt-bounds count mangoldt-error))
          (lw-log-ramp-extension value point count (lw-smoothed-ramp-log-error count total error)))
       (lw-smoothed-ramp-extension-sum value point (- count 1) total error mangoldt-error))))

(defthm lw-smoothed-ramp-extension-sum-rational
  (implies (and (rationalp value) (rationalp point) (natp count) (natp total)
                (rationalp error) (< 0 error) (rationalp mangoldt-error) (< 0 mangoldt-error))
           (rationalp (lw-smoothed-ramp-extension-sum value point count total error mangoldt-error)))
  :hints (("Goal" :induct (lw-smoothed-ramp-extension-sum value point count total error mangoldt-error)
                   :in-theory (disable lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mangoldt-lower-coarse (index count) (epsilon mangoldt-error))
                       (:instance lw-smoothed-ramp-log-error-adequate (index count)))
                 :in-theory (disable lw-mangoldt-lower-coarse lw-smoothed-ramp-log-error-adequate)
                 :do-not-induct t))))

(local (in-theory (disable lw-smoothed-ramp-unit-error lw-smoothed-ramp-log-error)))

(local (defthm lw-srs-unit-positive
         (implies (and (natp total) (rationalp error) (< 0 error))
                  (and (rationalp (lw-smoothed-ramp-unit-error total error))
                       (< 0 (lw-smoothed-ramp-unit-error total error))))
         :hints (("Goal" :use ((:instance lw-srs-positive-product (a error) (b (/ (+ 1 total)))))
                         :in-theory (enable lw-smoothed-ramp-unit-error)))
         :rule-classes nil))

(local (defthm lw-srs-weighted-cutpoint
         (implies
          (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error)
               (integerp index) (< 1 index) (natp total)
               (rationalp error) (< 0 error) (rationalp mangoldt-error) (< 0 mangoldt-error))
          (<= (abs
                (- (* (car (lw-mangoldt-bounds index mangoldt-error))
                      (lw-ramp (lw-log-signal-point value signal-error) index))
                   (* (car (lw-mangoldt-bounds index mangoldt-error))
                      (lw-log-ramp-extension value (lw-log-signal-point value signal-error) index
                        (lw-smoothed-ramp-log-error index total error)))))
              (+ (lw-smoothed-ramp-unit-error total error) (* 4 (lw-log-signal-delta value signal-error)))))
         :hints (("Goal"
                  :use (lw-srs-unit-positive
                        (:instance lw-log-signal-point-valid (error signal-error))
                        (:instance lw-log-signal-delta-valid (error signal-error))
                        (:instance lw-smoothed-ramp-log-error-adequate)
                        (:instance lw-exp-lipschitz-cap-valid (cap index))
                        (:instance lw-srs-positive-product
                          (a (lw-exp-lipschitz-cap index)) (b (lw-smoothed-ramp-log-error index total error)))
                        (:instance lw-mangoldt-lower-coarse (epsilon mangoldt-error))
                        (:instance lw-log-signal-ramp-cutpoint-error
                          (log-error (lw-smoothed-ramp-log-error index total error)))
                        (:instance lw-srs-weighted-error
                          (a (lw-ramp (lw-log-signal-point value signal-error) index))
                          (b (lw-log-ramp-extension value (lw-log-signal-point value signal-error) index
                               (lw-smoothed-ramp-log-error index total error)))
                          (weight (car (lw-mangoldt-bounds index mangoldt-error)))
                          (radius (+ (* (lw-exp-lipschitz-cap index)
                                        (lw-smoothed-ramp-log-error index total error))
                                     (* 4 (lw-log-signal-delta value signal-error))))))
                  :in-theory
                  (disable lw-log-signal-point-valid lw-log-signal-delta-valid
                           lw-smoothed-ramp-log-error-adequate lw-exp-lipschitz-cap-valid
                           lw-mangoldt-lower-coarse lw-log-signal-ramp-cutpoint-error)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-srs-mangoldt-one
         (equal (lw-mangoldt-bounds 1 epsilon) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-mangoldt-bounds)))))

(local (defthm lw-srs-smoothed-zero
         (equal (lw-smoothed-sum-bounds point 0 epsilon) (cons 0 0))
         :hints (("Goal" :expand ((lw-smoothed-sum-bounds point 0 epsilon))))))

(local (defthm lw-srs-smoothed-one
         (equal (lw-smoothed-sum-bounds point 1 epsilon) (cons 0 0))
         :hints (("Goal" :expand ((lw-smoothed-sum-bounds point 1 epsilon))
                         :in-theory (enable lw-interval-add lw-interval-scale)))))

(local (defthm lw-srs-smoothed-step
         (implies (posp count)
                  (equal
                   (car (lw-smoothed-sum-bounds point count epsilon))
                   (+ (* (lw-ramp point count) (car (lw-mangoldt-bounds count epsilon)))
                      (car (lw-smoothed-sum-bounds point (- count 1) epsilon)))))
         :hints (("Goal" :expand ((lw-smoothed-sum-bounds point count epsilon))
                         :in-theory (enable lw-interval-add lw-interval-scale)))
         :rule-classes nil))

(defthm lw-smoothed-ramp-sum-cutpoint-error
  (implies
   (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error)
        (natp count) (natp total) (rationalp error) (< 0 error)
        (rationalp mangoldt-error) (< 0 mangoldt-error))
   (<= (abs
         (- (car (lw-smoothed-sum-bounds (lw-log-signal-point value signal-error) count mangoldt-error))
            (lw-smoothed-ramp-extension-sum value (lw-log-signal-point value signal-error)
              count total error mangoldt-error)))
       (* count (+ (lw-smoothed-ramp-unit-error total error)
                   (* 4 (lw-log-signal-delta value signal-error))))))
  :hints
  (("Goal" :induct (lw-smoothed-ramp-extension-sum value (lw-log-signal-point value signal-error)
                    count total error mangoldt-error)
           :in-theory (disable (:definition lw-smoothed-ramp-extension-sum)
                               lw-smoothed-ramp-extension-sum-rational))
   (and stable-under-simplificationp
        '(:use (lw-srs-unit-positive
                (:instance lw-log-signal-point-valid (error signal-error))
                (:instance lw-log-signal-delta-valid (error signal-error))
                (:instance lw-srs-weighted-cutpoint (index count))
                (:instance lw-smoothed-sum-bounds-valid
                  (value (lw-log-signal-point value signal-error)) (count (- count 1)) (epsilon mangoldt-error))
                (:instance lw-smoothed-ramp-extension-sum-rational
                  (point (lw-log-signal-point value signal-error)) (count (- count 1)))
                (:instance lw-srs-smoothed-step
                  (point (lw-log-signal-point value signal-error)) (epsilon mangoldt-error))
                (:instance lw-srs-sum-error
                  (a (car (lw-smoothed-sum-bounds (lw-log-signal-point value signal-error)
                             (- count 1) mangoldt-error)))
                  (b (lw-smoothed-ramp-extension-sum value (lw-log-signal-point value signal-error)
                       (- count 1) total error mangoldt-error))
                  (c (* (car (lw-mangoldt-bounds count mangoldt-error))
                        (lw-ramp (lw-log-signal-point value signal-error) count)))
                  (d (* (car (lw-mangoldt-bounds count mangoldt-error))
                        (lw-log-ramp-extension value (lw-log-signal-point value signal-error) count
                          (lw-smoothed-ramp-log-error count total error))))
                  (radius (* (- count 1)
                             (+ (lw-smoothed-ramp-unit-error total error)
                                (* 4 (lw-log-signal-delta value signal-error)))))
                  (other-radius (+ (lw-smoothed-ramp-unit-error total error)
                                   (* 4 (lw-log-signal-delta value signal-error))))))
          :expand ((lw-smoothed-ramp-extension-sum value (lw-log-signal-point value signal-error)
                     count total error mangoldt-error))
          :in-theory (e/d (lw-intervalp)
                          (lw-log-signal-point-valid lw-log-signal-delta-valid
                           lw-smoothed-sum-bounds-valid lw-smoothed-ramp-extension-sum-rational))
          :nonlinearp nil :do-not-induct t))))

(defun lw-log-signal-ramp-count (cap)
  (lw-signal-count (lw-log-signal-spatial-cap cap)))

(defun lw-log-signal-ramp-error (cap error)
  (* 1/64 error (/ (+ 1 (lw-log-signal-ramp-count cap)))))

(defun lw-log-signal-ramp-value (cap value error)
  (let* ((total (lw-log-signal-ramp-count cap))
         (signal-error (lw-log-signal-ramp-error cap error))
         (point (lw-log-signal-point value signal-error))
         (epsilon (lw-log-signal-linear-precision value signal-error)))
    (+ (lw-smoothed-ramp-extension-sum value point total total error epsilon)
       (- (* point value)) (* point (+ 1 (car (lw-euler-bounds epsilon)))))))

(local (defthm lw-srs-error-data
         (implies (and (natp count) (rationalp error) (< 0 error))
                  (and (rationalp (* 1/64 error (/ (+ 1 count))))
                       (< 0 (* 1/64 error (/ (+ 1 count))))
                       (<= (* 1/64 error (/ (+ 1 count))) (* 1/64 error))))
         :hints (("Goal"
                  :use ((:instance lw-srs-positive-product (a error) (b (/ (+ 1 count))))
                        (:instance lw-reciprocal-antitone (left 1) (right (+ 1 count)))
                        (:instance lw-srs-multiply-order
                          (a (/ (+ 1 count))) (b 1) (factor (* 1/64 error))))
                  :in-theory (disable lw-reciprocal-antitone) :nonlinearp nil))
         :rule-classes nil))

(local (defthm lw-srs-total-budget
         (implies (and (natp count) (rationalp error) (< 0 error)
                       (rationalp delta) (<= 0 delta) (<= delta (* 1/64 error (/ (+ 1 count)))))
                  (<= (* count (+ (lw-smoothed-ramp-unit-error count error) (* 4 delta))) (* 1/4 error)))
         :hints (("Goal"
                  :use ((:instance lw-srs-multiply-order
                          (a delta) (b (* 1/64 error (/ (+ 1 count)))) (factor (* 4 count)))
                        (:instance lw-positive-division-bound
                          (numerator (* count error)) (divisor (+ 1 count)) (bound error)))
                  :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-srs-primitive-positive
         (implies (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error))
                  (and (rationalp (lw-log-signal-linear-precision value signal-error))
                       (< 0 (lw-log-signal-linear-precision value signal-error))))
         :hints (("Goal"
                  :use ((:instance lw-log-signal-point-valid (error signal-error))
                        (:instance lw-log-signal-budget-valid (error signal-error))
                        (:instance lw-signal-precision-positive
                          (value (lw-log-signal-point value signal-error)) (ceiling 0)
                          (error (/ (lw-log-signal-budget signal-error) 2))))
                  :in-theory
                  (e/d (lw-log-signal-linear-precision)
                       (lw-log-signal-point-valid lw-log-signal-budget-valid lw-signal-precision-positive))
                  :do-not-induct t))
         :rule-classes nil))

(defthm lw-log-signal-ramp-parameters
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error))
           (let* ((count (lw-log-signal-ramp-count cap))
                  (signal-error (lw-log-signal-ramp-error cap error))
                  (point (lw-log-signal-point value signal-error))
                  (epsilon (lw-log-signal-linear-precision value signal-error)))
             (and (posp count) (rationalp signal-error) (< 0 signal-error)
                  (<= signal-error (* 1/64 error))
                  (rationalp point) (< 1 point) (<= point count)
                  (rationalp epsilon) (< 0 epsilon)
                  (<= (* count (+ (lw-smoothed-ramp-unit-error count error)
                                  (* 4 (lw-log-signal-delta value signal-error)))) (* 1/4 error)))))
  :hints (("Goal"
           :use ((:instance lw-log-signal-spatial-cap-valid)
                 (:instance lw-signal-count-covers (value (lw-log-signal-spatial-cap cap)))
                 (:instance lw-srs-error-data (count (lw-log-signal-ramp-count cap)))
                 (:instance lw-log-signal-point-valid (error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-log-signal-point-spatial-cap (error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-log-signal-delta-valid (error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-log-signal-delta-budget (error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-srs-primitive-positive (signal-error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-srs-total-budget
                   (count (lw-log-signal-ramp-count cap))
                   (delta (lw-log-signal-delta value (lw-log-signal-ramp-error cap error)))))
           :in-theory
           (e/d (lw-log-signal-ramp-count lw-log-signal-ramp-error)
                (lw-log-signal-spatial-cap-valid lw-signal-count-covers lw-log-signal-point-valid
                 lw-log-signal-point-spatial-cap lw-log-signal-delta-valid lw-log-signal-delta-budget))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-log-signal-ramp-count lw-log-signal-ramp-error
                          lw-smoothed-ramp-extension-sum lw-euler-bounds)))

(defthm lw-log-signal-ramp-value-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error))
           (rationalp (lw-log-signal-ramp-value cap value error)))
  :hints (("Goal"
           :use (lw-log-signal-ramp-parameters
                 (:instance lw-euler-bounds-interval (epsilon (lw-log-signal-linear-precision value (lw-log-signal-ramp-error cap error)))))
           :in-theory (e/d (lw-intervalp) (lw-log-signal-ramp-parameters lw-euler-bounds-interval))
           :do-not-induct t)))

(defthm lw-log-signal-ramp-prime-sum-error
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error))
           (let* ((count (lw-log-signal-ramp-count cap)) (signal-error (lw-log-signal-ramp-error cap error))
                  (point (lw-log-signal-point value signal-error))
                  (epsilon (lw-log-signal-linear-precision value signal-error)))
             (<= (abs (- (car (lw-smoothed-sum-bounds point (lw-signal-count point) epsilon))
                          (lw-smoothed-ramp-extension-sum value point count count error epsilon)))
                 (* 1/4 error))))
  :hints (("Goal"
           :use (lw-log-signal-ramp-parameters
                 (:instance lw-signal-count-covers (value (lw-log-signal-point value (lw-log-signal-ramp-error cap error))))
                 (:instance lw-smoothed-sum-bounds-stable-count
                   (value (lw-log-signal-point value (lw-log-signal-ramp-error cap error))) (left-count (lw-signal-count (lw-log-signal-point value (lw-log-signal-ramp-error cap error))))
                   (right-count (lw-log-signal-ramp-count cap)) (epsilon (lw-log-signal-linear-precision value (lw-log-signal-ramp-error cap error))))
                 (:instance lw-smoothed-ramp-sum-cutpoint-error
                   (signal-error (lw-log-signal-ramp-error cap error)) (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (mangoldt-error (lw-log-signal-linear-precision value (lw-log-signal-ramp-error cap error)))))
           :in-theory (disable lw-log-signal-ramp-parameters lw-smoothed-ramp-sum-cutpoint-error
                               lw-signal-count-covers)
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-srs-triangle
         (implies (and (rationalp a) (rationalp b) (rationalp c)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- b c)) other-radius))
                  (<= (abs (- a c)) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= b c)))) :rule-classes nil))

(defthm lw-log-signal-ramp-computed-decomposition
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error))
           (<= (abs (- (car (lw-log-signal-bounds value (lw-log-signal-ramp-error cap error)))
                        (lw-log-signal-ramp-value cap value error))) error))
  :hints (("Goal"
           :use (lw-log-signal-ramp-parameters lw-log-signal-ramp-prime-sum-error
                 lw-log-signal-ramp-value-rational
                 (:instance lw-log-signal-computed-linearization (error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-log-signal-linear-value-rational (error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-log-signal-bounds-valid (error (lw-log-signal-ramp-error cap error)))
                 (:instance lw-smoothed-sum-bounds-valid
                   (value (lw-log-signal-point value (lw-log-signal-ramp-error cap error))) (count (lw-signal-count (lw-log-signal-point value (lw-log-signal-ramp-error cap error)))) (epsilon (lw-log-signal-linear-precision value (lw-log-signal-ramp-error cap error))))
                 (:instance lw-euler-bounds-interval (epsilon (lw-log-signal-linear-precision value (lw-log-signal-ramp-error cap error))))
                 (:instance lw-srs-triangle
                   (a (car (lw-log-signal-bounds value (lw-log-signal-ramp-error cap error))))
                   (b (lw-log-signal-linear-value value (lw-log-signal-ramp-error cap error)))
                   (c (lw-log-signal-ramp-value cap value error))
                   (radius (lw-log-signal-ramp-error cap error)) (other-radius (* 1/4 error))))
           :in-theory
           (e/d (lw-log-signal-ramp-value lw-log-signal-linear-value lw-intervalp)
                (lw-log-signal-ramp-parameters lw-log-signal-ramp-prime-sum-error
                 lw-log-signal-ramp-value-rational lw-log-signal-computed-linearization
                 lw-log-signal-linear-value-rational lw-log-signal-bounds-valid
                 lw-smoothed-sum-bounds-valid lw-euler-bounds-interval))
           :nonlinearp nil :do-not-induct t)))
