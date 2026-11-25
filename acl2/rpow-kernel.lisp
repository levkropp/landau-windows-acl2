(in-package "ACL2")

(include-book "exp-geometric")
(include-book "mellin-window")

; Rational-power decay shifts from finite Taylor products and polynomial
; root brackets. No real exponential or analytic rpow identity is assumed.
(local (in-theory
        (disable lw-exp-sum lw-exp-term lw-exp-index lw-exp-bounds lw-exp-band lw-exp-neg-bounds
                 lw-exp-index-adequate lw-exp-bounds-valid lw-exp-bounds-overlap lw-exp-sum-at-least-one
                 lw-exp-bounds-monotone-overlap lw-rpow-bounds-monotone-overlap
                 lw-exp-sum-integer-upper lw-exp-sum-integer-lower
                 lw-rational-power lw-rational-power-product lw-rational-power-add-exponents
                 lw-rational-power-monotone-base lw-rational-power-monotone-exponent lw-rational-power-nonnegative
                 lw-rpow-bounds lw-rpow-bounds-sound
                 lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-kernel-weight-scale-nonnegative lw-kernel-weight-bounds-valid
                 lw-log-signal-point lw-log-signal-point-valid lw-log-signal-point-exp-cap lw-log-signal-delta
                 lw-log-signal-delta-valid lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds))))

(local (defthm lw-rk-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-rk-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-rk-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-rk-zero-times (equal (* 0 a) 0)))
(local (defthm lw-rk-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-rk-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-rk-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-rk-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-rk-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-exp-sum-mixed-integer-powers
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
                (natp left-copies) (natp right-copies) (natp left-index) (natp right-index))
           (<= (* (lw-rational-power (lw-exp-sum left left-index) left-copies)
                  (lw-rational-power (lw-exp-sum right right-index) right-copies))
               (lw-exp-sum (+ (* left-copies left) (* right-copies right))
                           (+ (* left-copies left-index) (* right-copies right-index)))))
  :hints (("Goal" :use ((:instance lw-exp-sum-integer-lower (value left) (copies left-copies) (index left-index))
                        (:instance lw-exp-sum-integer-lower (value right) (copies right-copies) (index right-index))
                        (:instance lw-exp-sum-at-least-one (value left) (index left-index))
                        (:instance lw-exp-sum-at-least-one (value right) (index right-index))
                        (:instance lw-exp-sum-at-least-one (value (* left-copies left)) (index (* left-copies left-index)))
                        (:instance lw-rational-power-nonnegative (base (lw-exp-sum right right-index)) (exponent right-copies))
                        (:instance lw-exp-sum-product-upper
                          (left (* left-copies left)) (right (* right-copies right))
                          (left-index (* left-copies left-index)) (right-index (* right-copies right-index)))
                        (:instance lw-rk-multiply-order
                          (a (lw-rational-power (lw-exp-sum left left-index) left-copies))
                          (b (lw-exp-sum (* left-copies left) (* left-copies left-index)))
                          (factor (lw-rational-power (lw-exp-sum right right-index) right-copies)))
                        (:instance lw-rk-multiply-order
                          (a (lw-rational-power (lw-exp-sum right right-index) right-copies))
                          (b (lw-exp-sum (* right-copies right) (* right-copies right-index)))
                          (factor (lw-exp-sum (* left-copies left) (* left-copies left-index)))))
                  :nonlinearp t)))

(defthm lw-exp-sum-integer-upper-enclosure
  (implies (and (rationalp value) (<= 0 value) (natp copies) (natp index))
           (<= (lw-exp-sum (* copies value) index)
               (lw-rational-power (cdr (lw-exp-bounds value error)) copies)))
  :hints (("Goal" :use (lw-exp-sum-integer-upper lw-exp-sum-at-least-one (:instance lw-exp-bounds-valid (epsilon error))
                        (:instance lw-exp-partial-sum-upper)
                        (:instance lw-rational-power-monotone-base
                          (left (lw-exp-sum value index)) (right (cdr (lw-exp-bounds value error))) (exponent copies))))))

(local (in-theory (disable lw-exp-sum-mixed-integer-powers lw-exp-sum-integer-upper-enclosure)))

(defthm lw-exp-bounds-balanced-powers
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right) (rationalp total) (<= 0 total)
                (natp left-copies) (natp right-copies)
                (equal (+ (* left-copies left) (* right-copies right)) (* right-copies total)))
           (<= (* (lw-rational-power (car (lw-exp-bounds left left-error)) left-copies)
                  (lw-rational-power (car (lw-exp-bounds right right-error)) right-copies))
               (lw-rational-power (cdr (lw-exp-bounds total total-error)) right-copies)))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (value left) (epsilon left-error))
                        (:instance lw-exp-index-adequate (value right) (epsilon right-error))
                        (:instance lw-exp-sum-mixed-integer-powers
                          (left-index (lw-exp-index left left-error)) (right-index (lw-exp-index right right-error)))
                        (:instance lw-exp-sum-integer-upper-enclosure (value total) (copies right-copies)
                          (index (+ (* left-copies (lw-exp-index left left-error)) (* right-copies (lw-exp-index right right-error))))
                          (error total-error)))
                  :in-theory (enable lw-exp-bounds lw-exp-band))))

(local (defthm lw-rk-powered-product-comparison
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b) (rationalp c) (<= 0 c)
                       (rationalp moment) (<= 0 moment) (rationalp multiplier) (<= 0 multiplier) (posp degree)
                       (<= (lw-rational-power a degree) (* multiplier moment))
                       (<= (* moment (lw-rational-power b degree)) (lw-rational-power c degree))
                       (<= multiplier (lw-rational-power 2 degree)))
                  (<= (* a b) (* 2 c)))
         :hints (("Goal"
                  :use ((:instance lw-rational-power-product (left a) (right b) (exponent degree))
                        (:instance lw-rational-power-product (left 2) (right c) (exponent degree))
                        (:instance lw-rational-power-nonnegative (base b) (exponent degree))
                        (:instance lw-rational-power-nonnegative (base c) (exponent degree))
                        (:instance lw-rk-multiply-order (a (lw-rational-power a degree)) (b (* multiplier moment)) (factor (lw-rational-power b degree)))
                        (:instance lw-rk-multiply-order (a (* moment (lw-rational-power b degree))) (b (lw-rational-power c degree)) (factor multiplier))
                        (:instance lw-rk-multiply-order (a multiplier) (b (lw-rational-power 2 degree)) (factor (lw-rational-power c degree)))
                        (:instance lw-rational-power-reflects-order (left (* a b)) (right (* 2 c)) (exponent degree)))
                  :nonlinearp t))
         :rule-classes nil))

(local (in-theory (disable lw-exp-bounds-balanced-powers)))

(defthm lw-rpow-exp-balanced-bound
  (implies (and (rationalp point) (<= 1 point)
                (rationalp value) (<= 0 value) (rationalp remaining) (<= 0 remaining) (rationalp total) (<= 0 total)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp root-error) (< 0 root-error)
                (<= point (* 2 (car (lw-exp-bounds value signal-error))))
                (equal (+ (* numerator value) (* denominator remaining)) (* denominator total)))
           (<= (* (car (lw-rpow-bounds point numerator denominator root-error))
                  (car (lw-exp-bounds remaining remaining-error)))
               (* 2 (cdr (lw-exp-bounds total total-error)))))
  :hints (("Goal"
           :use ((:instance lw-rpow-bounds-sound (value point) (epsilon root-error))
                 (:instance lw-exp-bounds-valid (epsilon signal-error))
                 (:instance lw-exp-bounds-valid (value remaining) (epsilon remaining-error))
                 (:instance lw-exp-bounds-valid (value total) (epsilon total-error))
                 (:instance lw-rational-power-monotone-base
                   (left point) (right (* 2 (car (lw-exp-bounds value signal-error)))) (exponent numerator))
                 (:instance lw-rational-power-product (left 2) (right (car (lw-exp-bounds value signal-error))) (exponent numerator))
                 (:instance lw-rational-power-nonnegative (base (car (lw-exp-bounds value signal-error))) (exponent numerator))
                 (:instance lw-rational-power-nonnegative (base 2) (exponent numerator))
                 (:instance lw-rational-power-monotone-exponent (base 2) (small numerator) (large denominator))
                 (:instance lw-exp-bounds-balanced-powers (left value) (right remaining) (left-copies numerator) (right-copies denominator)
                   (left-error signal-error) (right-error remaining-error))
                 (:instance lw-rk-powered-product-comparison
                   (a (car (lw-rpow-bounds point numerator denominator root-error)))
                   (b (car (lw-exp-bounds remaining remaining-error))) (c (cdr (lw-exp-bounds total total-error)))
                   (moment (lw-rational-power (car (lw-exp-bounds value signal-error)) numerator))
                   (multiplier (lw-rational-power 2 numerator)) (degree denominator))))))

(local (defthm lw-rk-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-rk-left-commutes)))))

(local (defthm lw-rk-rate-balance
         (implies (and (rationalp value) (rationalp rate) (natp numerator) (posp denominator))
                  (equal (+ (* numerator value) (* denominator (- rate (/ numerator denominator)) value))
                         (* denominator rate value)))
         :hints (("Goal" :use ((:instance inverse-of-* (x denominator)))
                         :in-theory (disable inverse-of-*) :nonlinearp t))))

; This is the comparison needed before multiplying by the reciprocal
; exponential in the kernel. All three exponential precisions are free.
(defthm lw-rpow-exp-rate-bound
  (implies (and (rationalp point) (<= 1 point) (rationalp value) (<= 0 value)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp rate) (<= (/ numerator denominator) rate)
                (rationalp root-error) (< 0 root-error)
                (<= point (* 2 (car (lw-exp-bounds value signal-error)))))
           (<= (* (car (lw-rpow-bounds point numerator denominator root-error))
                  (car (lw-exp-bounds (* (- rate (/ numerator denominator)) value) remaining-error)))
               (* 2 (cdr (lw-exp-bounds (* rate value) total-error)))))
  :hints (("Goal" :use ((:instance lw-rpow-exp-balanced-bound
                          (remaining (* (- rate (/ numerator denominator)) value)) (total (* rate value)))
                        (:instance lw-positive-division-lower-bound (numerator numerator) (divisor denominator) (bound 0))
                        (:instance lw-rk-multiply-order (a (/ numerator denominator)) (b rate) (factor value))
                        (:instance lw-rk-multiply-order (a 0) (b rate) (factor value)))
                  :nonlinearp t)))

(local (defthm lw-rk-division-product
         (implies (and (rationalp a) (<= 0 a) (rationalp scale) (<= 0 scale)
                       (rationalp lower) (< 0 lower) (rationalp upper) (< 0 upper) (<= (* a lower) upper))
                  (<= (/ (* a scale) upper) (/ scale lower)))
         :hints (("Goal" :use ((:instance inverse-of-* (x lower))
                              (:instance lw-rk-multiply-order (a (* a lower)) (b upper) (factor (/ scale lower)))
                              (:instance lw-positive-division-bound (numerator (* a scale)) (divisor upper) (bound (/ scale lower))))
                         :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(local (in-theory (disable lw-rpow-exp-balanced-bound lw-rpow-exp-rate-bound)))

(defthm lw-rpow-kernel-shift-bound
  (implies (and (rationalp point) (<= 1 point) (rationalp value) (<= 0 value)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp rate) (<= (/ numerator denominator) rate) (rationalp step) (<= 0 step)
                (rationalp root-error) (< 0 root-error)
                (<= point (* 2 (car (lw-exp-bounds value signal-error)))))
           (<= (* (car (lw-rpow-bounds point numerator denominator root-error))
                  (car (lw-kernel-weight-bounds value rate index step kernel-error)))
               (* 2 (cdr (lw-kernel-weight-bounds value (- rate (/ numerator denominator)) index step shifted-error)))))
  :hints (("Goal"
           :use ((:instance lw-rpow-exp-rate-bound
                   (remaining-error (lw-kernel-weight-precision value index step shifted-error))
                   (total-error (lw-kernel-weight-precision value index step kernel-error)))
                 (:instance lw-positive-division-lower-bound (numerator numerator) (divisor denominator) (bound 0))
                 (:instance lw-rk-multiply-order (a (/ numerator denominator)) (b rate) (factor value))
                 (:instance lw-rk-multiply-order (a 0) (b rate) (factor value))
                 (:instance lw-rpow-bounds-sound (value point) (epsilon root-error))
                 (:instance lw-exp-bounds-valid (value (* (- rate (/ numerator denominator)) value))
                   (epsilon (lw-kernel-weight-precision value index step shifted-error)))
                 (:instance lw-exp-bounds-valid (value (* rate value))
                   (epsilon (lw-kernel-weight-precision value index step kernel-error)))
                 (:instance lw-kernel-weight-scale-nonnegative)
                 (:instance lw-rk-division-product
                   (a (/ (car (lw-rpow-bounds point numerator denominator root-error)) 2))
                   (scale (lw-kernel-weight-scale value index step))
                   (lower (car (lw-exp-bounds (* (- rate (/ numerator denominator)) value) (lw-kernel-weight-precision value index step shifted-error))))
                   (upper (cdr (lw-exp-bounds (* rate value) (lw-kernel-weight-precision value index step kernel-error))))))
           :in-theory (enable lw-kernel-weight-bounds lw-exp-neg-bounds) :nonlinearp t)))

(local (in-theory (disable lw-rpow-kernel-shift-bound)))

; The point used by the actual log-signal evaluator supplies the premise.
(defthm lw-log-signal-rpow-kernel-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp rate) (<= (/ numerator denominator) rate) (rationalp step) (<= 0 step)
                (rationalp root-error) (< 0 root-error))
           (<= (* (car (lw-rpow-bounds (lw-log-signal-point value signal-error) numerator denominator root-error))
                  (car (lw-kernel-weight-bounds value rate index step kernel-error)))
               (* 2 (cdr (lw-kernel-weight-bounds value (- rate (/ numerator denominator)) index step shifted-error)))))
  :hints (("Goal" :use ((:instance lw-log-signal-point-valid (error signal-error))
                        (:instance lw-log-signal-point-exp-cap (error signal-error))
                        (:instance lw-rpow-kernel-shift-bound
                          (point (lw-log-signal-point value signal-error))
                          (signal-error (lw-log-signal-delta value signal-error)))))))
