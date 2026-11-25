(in-package "ACL2")

(include-book "log-exp")

; Quantitative inverse comparison for the actual rational logarithm and
; exponential evaluators. Finite Taylor sums have slope at least one
; on nonnegative inputs; no real exponential or logarithm is assumed.
; Apply the inverse estimate to the actual signal's logarithmic correction.

(local (in-theory
        (disable lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-band lw-exp-index
                 lw-exp-bounds-valid lw-exp-bounds-width lw-exp-bounds-overlap
                 lw-exp-bounds-monotone-overlap lw-exp-bounds-transport
                 lw-log-bounds lw-log-count lw-log-rectangles
                 lw-log-bounds-interval lw-log-bounds-width lw-log-bounds-nonnegative
                 lw-log-signal-point lw-log-signal-delta
                 lw-log-lower-bounds-taylor lw-log-upper-bounds-exp)))

(local (defun lw-lei-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-lei-countdown (- index 1)))))

(local (defthm lw-lei-term-one
         (implies (rationalp value) (equal (lw-exp-term value 1) value))
         :hints (("Goal" :expand ((lw-exp-term value 1) (lw-exp-term value 0))))))

(local (defthm lw-lei-sum-one
         (implies (rationalp value) (equal (lw-exp-sum value 1) (+ 1 value)))
         :hints (("Goal" :expand ((lw-exp-sum value 1) (lw-exp-sum value 0))))))

(defthm lw-exp-sum-unit-slope
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right) (posp index))
           (<= (+ (lw-exp-sum left index) (- right left)) (lw-exp-sum right index)))
  :hints (("Goal" :induct (lw-lei-countdown index)
                   :in-theory (disable lw-exp-term-monotone))
          (and stable-under-simplificationp
               '(:use (lw-exp-term-monotone)
                 :expand ((lw-exp-sum left index) (lw-exp-sum right index))
                 :do-not-induct t))))

(defthm lw-log-upper-bounds-taylor
  (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error))
           (<= point (lw-exp-sum (cdr (lw-log-bounds point log-error))
                                 (lw-log-count point log-error))))
  :hints (("Goal"
           :use ((:instance lw-log-step-adequate (value point) (epsilon log-error))
                 (:instance lw-log-grid-endpoint (value point) (epsilon log-error))
                 (:instance lw-log-count-positive (value point) (epsilon log-error))
                 (:instance lw-log-upper-rectangles-taylor (start 1)
                   (step (/ (- point 1) (lw-log-count point log-error)))
                   (count (lw-log-count point log-error))))
           :in-theory (enable lw-log-bounds)
           :do-not-induct t)))

(local (defthm lw-lei-log-data
         (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error))
                  (and (rationalp (car (lw-log-bounds point log-error)))
                       (rationalp (cdr (lw-log-bounds point log-error)))
                       (<= 0 (car (lw-log-bounds point log-error)))
                       (<= (car (lw-log-bounds point log-error)) (cdr (lw-log-bounds point log-error)))
                       (<= (- (cdr (lw-log-bounds point log-error))
                              (car (lw-log-bounds point log-error))) log-error)))
         :hints (("Goal"
                  :use ((:instance lw-log-bounds-interval (value point) (epsilon log-error))
                        (:instance lw-log-bounds-width (value point) (epsilon log-error))
                        (:instance lw-log-bounds-nonnegative))
                  :in-theory (enable lw-intervalp) :do-not-induct t))))

(local (defthm lw-lei-inverse-upper
         (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error)
                       (rationalp value) (<= 0 value)
                       (<= value (car (lw-log-bounds point log-error))))
                  (<= (- (car (lw-log-bounds point log-error)) value)
                      (- point (car (lw-exp-bounds value exp-error)))))
         :hints (("Goal"
                  :use (lw-lei-log-data
                        (:instance lw-exp-index-adequate (epsilon exp-error))
                        (:instance lw-exp-bounds-later-sum (error exp-error)
                          (index (+ 1 (lw-exp-index value exp-error) (lw-log-count point log-error))))
                        (:instance lw-log-lower-bounds-taylor
                          (index (+ 1 (lw-exp-index value exp-error) (lw-log-count point log-error))))
                        (:instance lw-exp-sum-unit-slope (left value)
                          (right (car (lw-log-bounds point log-error)))
                          (index (+ 1 (lw-exp-index value exp-error) (lw-log-count point log-error)))))
                  :in-theory (disable lw-lei-log-data lw-exp-start-index
                                      lw-exp-index-adequate lw-exp-bounds-later-sum lw-exp-sum-unit-slope)
                  :do-not-induct t)) :rule-classes nil))

(local (defthm lw-lei-inverse-lower
         (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error)
                       (rationalp value) (<= 0 value)
                       (<= (cdr (lw-log-bounds point log-error)) value))
                  (<= (- value (cdr (lw-log-bounds point log-error)))
                      (- (cdr (lw-exp-bounds value exp-error)) point)))
         :hints (("Goal"
                  :use (lw-lei-log-data lw-log-upper-bounds-taylor
                        (:instance lw-exp-index-adequate (epsilon exp-error))
                        (:instance lw-exp-bounds-later-sum (error exp-error)
                          (index (+ 1 (lw-exp-index value exp-error) (lw-log-count point log-error))))
                        (:instance lw-exp-sum-monotone-index
                          (value (cdr (lw-log-bounds point log-error)))
                          (small (lw-log-count point log-error))
                          (large (+ 1 (lw-exp-index value exp-error) (lw-log-count point log-error))))
                        (:instance lw-exp-sum-unit-slope
                          (left (cdr (lw-log-bounds point log-error))) (right value)
                          (index (+ 1 (lw-exp-index value exp-error) (lw-log-count point log-error)))))
                  :in-theory (disable lw-lei-log-data lw-exp-start-index
                                      lw-log-upper-bounds-taylor lw-exp-index-adequate
                                      lw-exp-bounds-later-sum lw-exp-sum-unit-slope)
                  :do-not-induct t)) :rule-classes nil))

(defthm lw-log-exp-point-inverse
  (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error)
                (rationalp value) (<= 0 value) (rationalp exp-error) (< 0 exp-error)
                (rationalp slack) (<= 0 slack)
                (<= (car (lw-exp-bounds value exp-error)) point)
                (<= point (+ (cdr (lw-exp-bounds value exp-error)) slack)))
           (and (<= (abs (- (car (lw-log-bounds point log-error)) value))
                    (+ exp-error slack log-error))
                (<= (abs (- (cdr (lw-log-bounds point log-error)) value))
                    (+ exp-error slack log-error))))
  :hints (("Goal"
           :cases ((<= value (car (lw-log-bounds point log-error)))
                   (<= (cdr (lw-log-bounds point log-error)) value))
           :use (lw-lei-log-data lw-lei-inverse-upper lw-lei-inverse-lower
                 (:instance lw-exp-bounds-valid (epsilon exp-error))
                 (:instance lw-exp-bounds-width (epsilon exp-error)))
           :in-theory (e/d (lw-intervalp) (lw-lei-log-data)) :do-not-induct t)))

(defthm lw-log-signal-point-log-error
  (implies (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error)
                (rationalp log-error) (< 0 log-error))
           (and
            (<= (abs (- (car (lw-log-bounds (lw-log-signal-point value signal-error) log-error)) value))
                (+ (* 2 (lw-log-signal-delta value signal-error)) log-error))
            (<= (abs (- (cdr (lw-log-bounds (lw-log-signal-point value signal-error) log-error)) value))
                (+ (* 2 (lw-log-signal-delta value signal-error)) log-error))))
  :hints (("Goal"
           :use ((:instance lw-log-signal-delta-valid (error signal-error))
                 (:instance lw-log-signal-point-valid (error signal-error))
                 (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value signal-error)))
                 (:instance lw-log-exp-point-inverse
                   (point (lw-log-signal-point value signal-error))
                   (exp-error (lw-log-signal-delta value signal-error))
                   (slack (lw-log-signal-delta value signal-error))))
           :in-theory (e/d (lw-log-signal-point lw-intervalp)
                           (lw-log-exp-point-inverse lw-log-signal-delta-valid
                            lw-log-signal-point-valid))
           :do-not-induct t)))

(local (defthm lw-lei-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-lei-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-lei-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(defun lw-log-signal-linear-precision (value error)
  (lw-signal-precision (lw-log-signal-point value error) 0 (/ (lw-log-signal-budget error) 2)))

(defun lw-log-signal-linear-value (value error)
  (let* ((point (lw-log-signal-point value error))
         (epsilon (lw-log-signal-linear-precision value error)))
    (+ (car (lw-smoothed-sum-bounds point (lw-signal-count point) epsilon))
       (- (* point value))
       (* point (+ 1 (car (lw-euler-bounds epsilon)))))))

(local (in-theory
        (disable lw-smoothed-sum-bounds lw-euler-bounds lw-signal-count
                 lw-signal-precision lw-log-signal-budget lw-log-signal-cap
                 lw-log-signal-lipschitz lw-log-signal-margin)))

(local (defthm lw-lei-linear-precision-positive
         (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
                  (and (rationalp (lw-log-signal-linear-precision value error))
                       (< 0 (lw-log-signal-linear-precision value error))))
         :hints (("Goal"
                  :use (lw-log-signal-budget-valid lw-log-signal-point-valid
                        (:instance lw-signal-precision-positive
                          (value (lw-log-signal-point value error)) (ceiling 0)
                          (error (/ (lw-log-signal-budget error) 2))))
                  :in-theory (disable lw-log-signal-budget-valid lw-log-signal-point-valid
                                      lw-signal-precision-positive)
                  :do-not-induct t))))

(defthm lw-log-signal-linear-value-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (rationalp (lw-log-signal-linear-value value error)))
  :hints (("Goal"
           :use (lw-log-signal-point-valid lw-lei-linear-precision-positive
                 (:instance lw-smoothed-sum-bounds-valid
                   (value (lw-log-signal-point value error))
                   (count (lw-signal-count (lw-log-signal-point value error)))
                   (epsilon (lw-log-signal-linear-precision value error)))
                 (:instance lw-euler-bounds-interval
                   (epsilon (lw-log-signal-linear-precision value error))))
           :in-theory (e/d (lw-intervalp)
                           (lw-log-signal-point-valid lw-lei-linear-precision-positive
                            lw-smoothed-sum-bounds-valid lw-euler-bounds-interval))
           :do-not-induct t)))

(local (defthm lw-lei-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lei-linear-scalar-budget
         (implies
          (and (rationalp point) (<= 1 point) (natp count)
               (rationalp budget) (< 0 budget)
               (rationalp slope) (<= (* 2 point) slope)
               (rationalp delta) (<= 0 delta) (<= (* slope delta) (* 1/4 budget)))
          (<= (+ (* point (+ (* 2 delta) (/ (* 1/2 budget) (+ 1 (* (+ count 2) point)))))
                 (* slope delta)) budget))
         :hints (("Goal"
                  :use ((:instance lw-lei-multiply-order (a (* 2 point)) (b slope) (factor delta))
                        (:instance lw-positive-division-bound
                          (numerator (* 1/2 point budget)) (divisor (+ 1 (* (+ count 2) point)))
                          (bound (* 1/2 budget))))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(defthm lw-log-signal-linearization-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<=
            (+ (* (lw-log-signal-point value error)
                  (+ (* 2 (lw-log-signal-delta value error))
                     (lw-log-signal-linear-precision value error)))
               (lw-log-signal-margin value error))
            error))
  :hints (("Goal"
           :use (lw-log-signal-point-valid lw-log-signal-cap-valid
                 lw-log-signal-budget-valid lw-log-signal-delta-valid
                 lw-log-signal-lipschitz-valid
                 (:instance lw-lei-linear-scalar-budget
                   (point (lw-log-signal-point value error))
                   (count (lw-signal-count (lw-log-signal-point value error)))
                   (budget (lw-log-signal-budget error))
                   (slope (lw-log-signal-lipschitz value))
                   (delta (lw-log-signal-delta value error))))
           :in-theory
           (e/d (lw-log-signal-lipschitz lw-signal-lipschitz-factor
                 lw-log-signal-margin lw-signal-precision lw-signal-error-factor)
                (lw-log-signal-point-valid lw-log-signal-cap-valid lw-log-signal-budget-valid
                 lw-log-signal-delta-valid lw-log-signal-lipschitz-valid))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-lei-scaled-log-error
         (implies (and (rationalp point) (<= 0 point) (rationalp value)
                       (rationalp logarithm) (rationalp radius) (<= 0 radius)
                       (<= (abs (- logarithm value)) radius)
                       (rationalp margin) (<= 0 margin))
                  (<= (abs (- (* point (- value logarithm)) margin))
                      (+ (* point radius) margin)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-log-signal-computed-linearization
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (abs (- (car (lw-log-signal-bounds value error))
                        (lw-log-signal-linear-value value error)))
               error))
  :hints (("Goal"
           :use (lw-log-signal-point-valid lw-log-signal-delta-valid
                 lw-log-signal-margin-valid lw-lei-linear-precision-positive
                 lw-log-signal-linearization-budget
                 (:instance lw-log-signal-point-log-error
                   (signal-error error) (log-error (lw-log-signal-linear-precision value error)))
                 (:instance lw-lei-log-data
                   (point (lw-log-signal-point value error))
                   (log-error (lw-log-signal-linear-precision value error)))
                 (:instance lw-smoothed-sum-bounds-valid
                   (value (lw-log-signal-point value error))
                   (count (lw-signal-count (lw-log-signal-point value error)))
                   (epsilon (lw-log-signal-linear-precision value error)))
                 (:instance lw-euler-bounds-interval
                   (epsilon (lw-log-signal-linear-precision value error)))
                 (:instance lw-lei-scaled-log-error
                   (point (lw-log-signal-point value error))
                   (logarithm (cdr (lw-log-bounds (lw-log-signal-point value error)
                                                 (lw-log-signal-linear-precision value error))))
                   (radius (+ (* 2 (lw-log-signal-delta value error))
                              (lw-log-signal-linear-precision value error)))
                   (margin (lw-log-signal-margin value error))))
           :in-theory
           (e/d (lw-log-signal-bounds lw-log-signal-base
                 lw-signal-bounds lw-signal-bounds-raw lw-gz-bounds-raw
                 lw-log-signal-linear-value lw-interval-add lw-interval-sub lw-interval-scale lw-intervalp)
                (lw-log-signal-point-valid lw-log-signal-delta-valid
                 lw-log-signal-margin-valid lw-lei-linear-precision-positive
                 lw-log-signal-linearization-budget lw-log-signal-point-log-error
                 lw-lei-log-data lw-smoothed-sum-bounds-valid lw-euler-bounds-interval))
           :do-not-induct t)))
