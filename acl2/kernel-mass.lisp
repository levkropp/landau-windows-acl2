(in-package "ACL2")

(include-book "negative-binomial")
(include-book "mellin-tail-bounds")
(include-book "mellin-integrand")

; Finite uniform-grid mass bounds for the actual factorial-normalized
; kernel weights. The negative-binomial potential replaces an assumed
; gamma integral in the arithmetic coefficient argument.
(local (in-theory
        (disable lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band
                 lw-rational-power lw-rational-power-add-exponents lw-exp-bounds-valid
                 lw-exp-term-multiplied lw-rising-binomial
                 lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-mellin-weight lw-mellin-kernel-error lw-mellin-signal-cap
                 lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds))))
(local (defthm lw-km-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-km-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-km-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-km-zero-times (equal (* 0 a) 0)))
(local (defthm lw-km-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-km-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-km-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-km-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-km-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-km-equal-times
         (implies (equal a b) (equal (* a factor) (* b factor))) :rule-classes nil))
(local (defthm lw-km-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-km-left-commutes)))))
(local (defun lw-km-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-km-countdown (- index 1)))))
(local (defthm lw-km-power-zero
         (implies (zp exponent) (equal (lw-rational-power base exponent) 1))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))
(local (defthm lw-km-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-km-sum-zero
         (implies (zp index) (equal (lw-exp-sum value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-sum)))))
(local (defthm lw-km-sum-first
         (implies (rationalp value) (equal (lw-exp-sum value 1) (+ 1 value)))
         :hints (("Goal" :in-theory (enable lw-exp-sum lw-exp-term)))))

(defthm lw-exp-linear-power-le-sum
  (implies (and (rationalp value) (<= 0 value) (natp index))
           (<= (lw-rational-power (+ 1 value) index) (lw-exp-sum (* index value) index)))
  :hints (("Goal" :induct (lw-km-countdown index))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-sum-product-upper (left (* (- index 1) value)) (right value)
                         (left-index (- index 1)) (right-index 1))
                       (:instance lw-km-multiply-order (a (lw-rational-power (+ 1 value) (- index 1)))
                         (b (lw-exp-sum (* (- index 1) value) (- index 1))) (factor (+ 1 value))))
                 :expand ((lw-rational-power (+ 1 value) index)) :do-not-induct t :nonlinearp t))))

(defthm lw-exp-linear-power-le-upper
  (implies (and (rationalp value) (<= 0 value) (natp index))
           (<= (lw-rational-power (+ 1 value) index) (cdr (lw-exp-bounds (* index value) error))))
  :hints (("Goal" :use (lw-exp-linear-power-le-sum (:instance lw-exp-partial-sum-upper (value (* index value))))
                  :in-theory (disable lw-exp-linear-power-le-sum))))

(defun lw-kernel-grid-ratio (rate step) (/ (+ 1 (* rate step))))

(defthm lw-kernel-grid-ratio-valid
  (implies (and (rationalp rate) (< 0 rate) (rationalp step) (< 0 step))
           (and (rationalp (lw-kernel-grid-ratio rate step)) (< 0 (lw-kernel-grid-ratio rate step))
                (< (lw-kernel-grid-ratio rate step) 1)))
  :hints (("Goal" :use ((:instance inverse-of-* (x (+ 1 (* rate step)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t)))

(local (defthm lw-km-divide-majorant
         (implies (and (rationalp term) (<= 0 term) (rationalp majorant) (<= 0 majorant) (<= term majorant)
                       (rationalp upper) (< 0 upper) (rationalp factor) (<= 0 factor) (<= 1 (* upper factor)))
                  (<= (/ term upper) (* majorant factor)))
         :hints (("Goal" :use ((:instance lw-km-multiply-order (a 1) (b (* upper factor)) (factor majorant))
                              (:instance lw-positive-division-bound (numerator term) (divisor upper) (bound (* majorant factor))))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-kernel-grid-geometric-majorant
  (implies (and (natp address) (natp index) (rationalp rate) (< 0 rate) (rationalp step) (< 0 step))
           (<= (car (lw-kernel-weight-bounds (* address step) rate index 1 error))
               (* (lw-rational-power step index) (lw-rising-binomial address index)
                  (lw-rational-power (lw-kernel-grid-ratio rate step) address))))
  :hints (("Goal"
           :use (lw-kernel-grid-ratio-valid
                 (:instance lw-exp-linear-power-le-upper (value (* rate step)) (index address)
                   (error (lw-kernel-weight-precision (* address step) index 1 error)))
                 (:instance lw-exp-bounds-valid (value (* rate address step))
                   (epsilon (lw-kernel-weight-precision (* address step) index 1 error)))
                 (:instance lw-rational-power-reciprocal-pair (value (+ 1 (* rate step))) (index address))
                 (:instance lw-rational-power-nonnegative (base (lw-kernel-grid-ratio rate step)) (exponent address))
                 (:instance lw-rational-power-nonnegative (base step) (exponent index))
                 (:instance lw-exp-term-scale-argument (value address) (factor step))
                 (:instance lw-rising-binomial-majorizes-taylor-term (value address))
                 (:instance lw-km-multiply-order (a (lw-exp-term address index)) (b (lw-rising-binomial address index))
                   (factor (lw-rational-power step index)))
                 (:instance lw-km-nonnegative-product (a (lw-rational-power step index)) (b (lw-rising-binomial address index)))
                 (:instance lw-km-multiply-order
                   (a (lw-rational-power (+ 1 (* rate step)) address))
                   (b (cdr (lw-exp-bounds (* rate address step) (lw-kernel-weight-precision (* address step) index 1 error))))
                   (factor (lw-rational-power (lw-kernel-grid-ratio rate step) address)))
                 (:instance lw-km-divide-majorant
                   (term (lw-exp-term (* address step) index))
                   (majorant (* (lw-rational-power step index) (lw-rising-binomial address index)))
                   (upper (cdr (lw-exp-bounds (* rate address step) (lw-kernel-weight-precision (* address step) index 1 error))))
                   (factor (lw-rational-power (lw-kernel-grid-ratio rate step) address))))
           :in-theory (e/d (lw-kernel-weight-bounds lw-kernel-weight-scale lw-exp-neg-bounds lw-kernel-grid-ratio)
                           (lw-exp-linear-power-le-upper lw-kernel-grid-ratio-valid lw-rising-binomial-majorizes-taylor-term
                            lw-exp-term-scale-argument lw-rational-power-reciprocal-pair lw-rational-power-nonnegative))
           :nonlinearp t)))

(local (defthm lw-km-power-successor
         (implies (natp exponent)
                  (equal (lw-rational-power base (+ 1 exponent)) (* base (lw-rational-power base exponent))))
         :hints (("Goal" :expand ((lw-rational-power base (+ 1 exponent)))))
         :rule-classes nil))

(defthm lw-kernel-grid-step-identity
  (implies (and (rationalp rate) (< 0 rate) (rationalp step) (< 0 step))
           (equal (* (- 1 (lw-kernel-grid-ratio rate step)) (+ (/ rate) step)) step))
  :hints (("Goal" :use ((:instance inverse-of-* (x rate)) (:instance inverse-of-* (x (+ 1 (* rate step))))
                        (:instance lw-km-equal-times (a (* (+ 1 (* rate step)) (/ (+ 1 (* rate step))))) (b 1) (factor (/ rate)))
                        (:instance lw-km-inverse-factor (divisor rate) (coefficient (* step (/ (+ 1 (* rate step)))))))
                  :in-theory (disable inverse-of-* lw-km-inverse-factor) :nonlinearp nil)))

(defthm lw-kernel-grid-rate-identity
  (implies (and (rationalp rate) (< 0 rate) (rationalp step) (< 0 step))
           (equal (/ step (- 1 (lw-kernel-grid-ratio rate step))) (+ (/ rate) step)))
  :hints (("Goal" :use (lw-kernel-grid-ratio-valid lw-kernel-grid-step-identity
                        (:instance lw-positive-division-bound (numerator step) (divisor (- 1 (lw-kernel-grid-ratio rate step))) (bound (+ (/ rate) step)))
                        (:instance lw-positive-division-lower-bound (numerator step) (divisor (- 1 (lw-kernel-grid-ratio rate step))) (bound (+ (/ rate) step))))
                  :in-theory (disable lw-kernel-grid-ratio lw-kernel-grid-ratio-valid lw-kernel-grid-step-identity))))

(defthm lw-kernel-grid-normalization
  (implies (and (rationalp rate) (< 0 rate) (rationalp step) (< 0 step) (natp index))
           (equal (* step (lw-rational-power step index)
                     (lw-rational-power (/ (- 1 (lw-kernel-grid-ratio rate step))) (+ 1 index)))
                  (lw-rational-power (+ (/ rate) step) (+ 1 index))))
  :hints (("Goal" :use (lw-kernel-grid-ratio-valid lw-kernel-grid-rate-identity
                        (:instance lw-km-power-successor (base step) (exponent index))
                        (:instance lw-rational-power-product (left step) (right (/ (- 1 (lw-kernel-grid-ratio rate step)))) (exponent (+ 1 index))))
                  :in-theory (disable lw-kernel-grid-ratio lw-kernel-grid-ratio-valid lw-kernel-grid-rate-identity lw-rational-power-product))))

(defun lw-mellin-grid-weight-sum (address count rate index step error)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (* step (lw-mellin-weight (* address step) rate index 1 error))
       (lw-mellin-grid-weight-sum (+ address 1) (- count 1) rate index step error))))

(local (in-theory
        (disable lw-kernel-grid-ratio lw-kernel-grid-ratio-valid lw-kernel-grid-geometric-majorant
                 lw-negative-binomial-sum lw-negative-binomial-mass-bound lw-kernel-grid-normalization)))

(local (defthm lw-km-binomial-sum-zero
         (implies (zp count) (equal (lw-negative-binomial-sum address count index ratio) 0))
         :hints (("Goal" :in-theory (enable lw-negative-binomial-sum)))))

(defthm lw-mellin-grid-weight-sum-rational
  (implies (and (natp address) (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (rationalp (lw-mellin-grid-weight-sum address count rate index step error)))
  :hints (("Goal" :induct (lw-mellin-grid-weight-sum address count rate index step error))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-weight-bounded (value (* address step)) (sigma rate) (step 1)))
                 :in-theory (disable lw-mellin-weight-bounded))))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-mellin-grid-weight-sum-majorant
  (implies (and (natp address) (natp count) (natp index) (rationalp rate) (< 0 rate)
                (rationalp step) (< 0 step) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum address count rate index step error)
               (* step (lw-rational-power step index) (lw-negative-binomial-sum address count index (lw-kernel-grid-ratio rate step)))))
  :hints (("Goal" :induct (lw-mellin-grid-weight-sum address count rate index step error))
          (and stable-under-simplificationp
               '(:use (lw-kernel-grid-ratio-valid
                       (:instance lw-mellin-weight-bounded (value (* address step)) (sigma rate) (step 1))
                       (:instance lw-kernel-grid-geometric-majorant
                         (error (lw-mellin-kernel-error (* address step) error)))
                       (:instance lw-km-multiply-order
                         (a (lw-mellin-weight (* address step) rate index 1 error))
                         (b (* (lw-rational-power step index) (lw-rising-binomial address index)
                               (lw-rational-power (lw-kernel-grid-ratio rate step) address))) (factor step)))
                 :expand ((lw-negative-binomial-sum address count index (lw-kernel-grid-ratio rate step)))
                 :in-theory (e/d (lw-mellin-weight) (lw-mellin-weight-bounded lw-mellin-kernel-cap))
                 :do-not-induct t))))

(defthm lw-mellin-grid-weight-mass
  (implies (and (natp count) (natp index) (rationalp rate) (< 0 rate)
                (rationalp step) (< 0 step) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum 0 count rate index step error)
               (lw-rational-power (+ (/ rate) step) (+ 1 index))))
  :hints (("Goal" :use (lw-kernel-grid-ratio-valid lw-kernel-grid-normalization
                        (:instance lw-mellin-grid-weight-sum-majorant (address 0))
                        (:instance lw-negative-binomial-mass-bound (ratio (lw-kernel-grid-ratio rate step)))
                        (:instance lw-km-nonnegative-product (a step) (b (lw-rational-power step index)))
                        (:instance lw-km-multiply-order
                          (a (lw-negative-binomial-sum 0 count index (lw-kernel-grid-ratio rate step)))
                          (b (lw-rational-power (/ (- 1 (lw-kernel-grid-ratio rate step))) (+ 1 index)))
                          (factor (* step (lw-rational-power step index)))))
                  :in-theory (disable lw-mellin-grid-weight-sum lw-mellin-grid-weight-sum-majorant)
                  :nonlinearp t)))

(local (defthm lw-km-step-coefficient
         (implies (and (natp exponent) (rationalp increment) (<= 0 increment))
                  (<= (* (- 1 (* exponent increment)) (+ 1 increment))
                      (- 1 (* (- exponent 1) increment))))
         :hints (("Goal" :use ((:instance lw-km-nonnegative-product (a increment) (b increment))
                              (:instance lw-km-nonnegative-product (a exponent) (b (* increment increment))))
                         :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-km-power-barrier
         (implies (and (natp exponent) (rationalp increment) (<= 0 increment) (<= (* 2 exponent increment) 1))
                  (<= (* (- 1 (* exponent increment)) (lw-rational-power (+ 1 increment) exponent)) 1))
         :hints (("Goal" :induct (lw-km-countdown exponent))
                 (and stable-under-simplificationp
                      '(:use (lw-km-step-coefficient
                              (:instance lw-rational-power-nonnegative (base (+ 1 increment)) (exponent (- exponent 1)))
                              (:instance lw-km-multiply-order
                                (a (* (- 1 (* exponent increment)) (+ 1 increment)))
                                (b (- 1 (* (- exponent 1) increment))) (factor (lw-rational-power (+ 1 increment) (- exponent 1)))))
                        :expand ((lw-rational-power (+ 1 increment) exponent))
                        :in-theory (disable lw-rational-power-nonnegative)
                        :do-not-induct t)))))

(defthm lw-rational-power-small-increment
  (implies (and (natp exponent) (rationalp increment) (<= 0 increment) (<= (* 2 exponent increment) 1))
           (<= (lw-rational-power (+ 1 increment) exponent) 2))
  :hints (("Goal" :use (lw-km-power-barrier
                        (:instance lw-rational-power-nonnegative (base (+ 1 increment))))
                  :in-theory (disable lw-km-power-barrier lw-rational-power-nonnegative) :nonlinearp t)))

(local (defthm lw-km-rate-scale
         (implies (and (rationalp rate) (< 0 rate) (rationalp step))
                  (equal (* (/ rate) (+ 1 (* rate step))) (+ (/ rate) step)))
         :hints (("Goal" :use ((:instance lw-km-inverse-factor (divisor rate) (coefficient step)))
                         :in-theory (disable lw-km-inverse-factor)))))

(defthm lw-mellin-grid-weight-mass-bound
  (implies (and (natp count) (natp index) (rationalp rate) (< 0 rate)
                (rationalp step) (< 0 step) (<= (* 2 rate step (+ 1 index)) 1)
                (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum 0 count rate index step error)
               (* 2 (lw-rational-power (/ rate) (+ 1 index)))))
  :hints (("Goal"
           :use (lw-mellin-grid-weight-mass
                 (:instance lw-rational-power-product (left (/ rate)) (right (+ 1 (* rate step))) (exponent (+ 1 index)))
                 (:instance lw-rational-power-small-increment (increment (* rate step)) (exponent (+ 1 index)))
                 (:instance lw-rational-power-nonnegative (base (/ rate)) (exponent (+ 1 index)))
                 (:instance lw-km-multiply-order
                   (a (lw-rational-power (+ 1 (* rate step)) (+ 1 index))) (b 2)
                   (factor (lw-rational-power (/ rate) (+ 1 index)))))
           :in-theory (disable lw-mellin-grid-weight-sum lw-mellin-grid-weight-mass
                               lw-rational-power-product lw-rational-power-small-increment lw-rational-power-nonnegative))))

(defthm lw-mellin-grid-weight-sum-nonnegative
  (implies (and (natp address) (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (<= 0 (lw-mellin-grid-weight-sum address count rate index step error)))
  :hints (("Goal" :induct (lw-mellin-grid-weight-sum address count rate index step error))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-weight-bounded (value (* address step)) (sigma rate) (step 1))
                       (:instance lw-km-nonnegative-product (a step) (b (lw-mellin-weight (* address step) rate index 1 error))))
                 :in-theory (disable lw-mellin-weight-bounded lw-mellin-kernel-cap) :do-not-induct t))))

(defun lw-kernel-grid-count (cap rate index mesh)
  (+ 1 (lw-ceiling-rational (+ (* 2 rate cap (+ 1 (nfix index))) (/ cap mesh)))))
(defun lw-kernel-grid-step (cap rate index mesh)
  (/ cap (lw-kernel-grid-count cap rate index mesh)))

(defthm lw-kernel-grid-count-adequate
  (implies (and (rationalp cap) (< 0 cap) (rationalp rate) (< 0 rate) (natp index) (rationalp mesh) (< 0 mesh))
           (and (natp (lw-kernel-grid-count cap rate index mesh)) (< 0 (lw-kernel-grid-count cap rate index mesh))
                (<= (* 2 rate cap (+ 1 index)) (lw-kernel-grid-count cap rate index mesh))
                (<= (/ cap mesh) (lw-kernel-grid-count cap rate index mesh))))
  :hints (("Goal" :use ((:instance lw-ceiling-rational-bracket (value (+ (* 2 rate cap (+ 1 index)) (/ cap mesh))))
                        (:instance lw-km-nonnegative-product (a rate) (b cap))
                        (:instance lw-km-nonnegative-product (a (* 2 rate cap)) (b (+ 1 index))))
                  :in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket) :nonlinearp t)))

(defthm lw-kernel-grid-step-valid
  (implies (and (rationalp cap) (< 0 cap) (rationalp rate) (< 0 rate) (natp index) (rationalp mesh) (< 0 mesh))
           (and (rationalp (lw-kernel-grid-step cap rate index mesh)) (< 0 (lw-kernel-grid-step cap rate index mesh))
                (<= (lw-kernel-grid-step cap rate index mesh) mesh)
                (<= (* 2 rate (lw-kernel-grid-step cap rate index mesh) (+ 1 index)) 1)
                (equal (* (lw-kernel-grid-count cap rate index mesh) (lw-kernel-grid-step cap rate index mesh)) cap)))
  :hints (("Goal" :use (lw-kernel-grid-count-adequate
                        (:instance lw-km-multiply-order (a (/ cap mesh)) (b (lw-kernel-grid-count cap rate index mesh)) (factor mesh))
                        (:instance lw-km-inverse-factor (divisor mesh) (coefficient cap))
                        (:instance lw-km-inverse-factor (divisor (lw-kernel-grid-count cap rate index mesh)) (coefficient cap))
                        (:instance lw-positive-division-bound (numerator cap) (divisor (lw-kernel-grid-count cap rate index mesh)) (bound mesh))
                        (:instance lw-positive-division-bound (numerator (* 2 rate cap (+ 1 index)))
                          (divisor (lw-kernel-grid-count cap rate index mesh)) (bound 1)))
                  :in-theory (disable lw-kernel-grid-count lw-kernel-grid-count-adequate lw-km-inverse-factor) :nonlinearp t)))

(defthm lw-mellin-computed-grid-weight-mass-bound
  (implies (and (rationalp cap) (< 0 cap) (rationalp rate) (< 0 rate) (natp index)
                (rationalp mesh) (< 0 mesh) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum 0 (lw-kernel-grid-count cap rate index mesh) rate index
                                          (lw-kernel-grid-step cap rate index mesh) error)
               (* 2 (lw-rational-power (/ rate) (+ 1 index)))))
  :hints (("Goal" :use (lw-kernel-grid-count-adequate lw-kernel-grid-step-valid
                        (:instance lw-mellin-grid-weight-mass-bound
                          (count (lw-kernel-grid-count cap rate index mesh)) (step (lw-kernel-grid-step cap rate index mesh))))
                  :in-theory (disable lw-mellin-grid-weight-sum lw-kernel-grid-count lw-kernel-grid-step
                                      lw-kernel-grid-count-adequate lw-kernel-grid-step-valid lw-mellin-grid-weight-mass-bound))))
