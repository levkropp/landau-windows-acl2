(in-package "ACL2")

(include-book "kernel-bounds")

; Across different moment indices, both kernel bands enclose the same
; negative exponential, multiplied by the exact Taylor factor u^j/j!.

(local (in-theory (disable lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                           lw-exp-neg-bounds lw-exp-bounds lw-exp-term lw-exp-sum
                           lw-kernel-weight-bounds-overlap)))

(local (defthm lw-km-zero-times (equal (* 0 a) 0)))

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
(local (defthm lw-km-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-km-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-km-term-zero
         (equal (lw-exp-term value 0) 1)
         :hints (("Goal" :in-theory (enable lw-exp-term)))))

(defthm lw-kernel-weight-zero-scale
  (implies (rationalp step) (equal (lw-kernel-weight-scale value 0 step) step))
  :hints (("Goal" :in-theory (enable lw-kernel-weight-scale))))

(defthm lw-kernel-moment-bands-overlap
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (natp index))
           (and
            (<= (car (lw-kernel-weight-bounds value sigma index step left-error))
                (* (lw-exp-term value index) (cdr (lw-kernel-weight-bounds value sigma 0 step right-error))))
            (<= (* (lw-exp-term value index) (car (lw-kernel-weight-bounds value sigma 0 step right-error)))
                (cdr (lw-kernel-weight-bounds value sigma index step left-error)))))
  :hints (("Goal" :use (lw-kernel-weight-scale-nonnegative
                        (:instance lw-exp-neg-bounds-overlap
                          (value (* sigma value))
                          (left-error (lw-kernel-weight-precision value index step left-error))
                          (right-error (lw-kernel-weight-precision value 0 step right-error)))
                        (:instance lw-exp-neg-bounds-overlap
                          (value (* sigma value))
                          (left-error (lw-kernel-weight-precision value 0 step right-error))
                          (right-error (lw-kernel-weight-precision value index step left-error)))
                        (:instance lw-exp-neg-bounds-valid
                          (value (* sigma value)) (epsilon (lw-kernel-weight-precision value index step left-error)))
                        (:instance lw-exp-neg-bounds-valid
                          (value (* sigma value)) (epsilon (lw-kernel-weight-precision value 0 step right-error)))
                        (:instance lw-km-multiply-order
                          (a (car (lw-exp-neg-bounds (* sigma value)
                                                    (lw-kernel-weight-precision value index step left-error))))
                          (b (cdr (lw-exp-neg-bounds (* sigma value)
                                                    (lw-kernel-weight-precision value 0 step right-error))))
                          (factor (lw-kernel-weight-scale value index step)))
                        (:instance lw-km-multiply-order
                          (a (car (lw-exp-neg-bounds (* sigma value)
                                                    (lw-kernel-weight-precision value 0 step right-error))))
                          (b (cdr (lw-exp-neg-bounds (* sigma value)
                                                    (lw-kernel-weight-precision value index step left-error))))
                          (factor (lw-kernel-weight-scale value index step))))
                  :in-theory (e/d (lw-kernel-weight-bounds lw-kernel-weight-scale)
                                  (lw-exp-neg-bounds-overlap lw-exp-neg-bounds-valid
                                   lw-kernel-weight-scale-nonnegative)))))

(local (defthm lw-km-scaled-lower-comparison
         (implies (and (rationalp lower) (rationalp upper) (<= lower upper)
                       (rationalp base-lower) (rationalp base-upper) (<= base-lower base-upper)
                       (rationalp factor) (<= 0 factor)
                       (rationalp error) (<= 0 error) (rationalp base-error) (<= 0 base-error)
                       (<= (- upper lower) error) (<= (- base-upper base-lower) base-error)
                       (<= lower (* factor base-upper)) (<= (* factor base-lower) upper))
                  (<= (abs (- lower (* factor base-lower))) (+ error (* factor base-error))))
         :hints (("Goal" :use ((:instance lw-km-multiply-order
                                 (a (- base-upper base-lower)) (b base-error)))
                         :cases ((<= (* factor base-lower) lower))))
         :rule-classes nil))

(defthm lw-kernel-moment-lower-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-kernel-weight-bounds value sigma index step left-error))
                       (* (lw-exp-term value index)
                          (car (lw-kernel-weight-bounds value sigma 0 step right-error)))))
               (+ left-error (* (lw-exp-term value index) right-error))))
  :hints (("Goal" :use (lw-kernel-moment-bands-overlap
                        (:instance lw-kernel-weight-bounds-valid (error left-error))
                        (:instance lw-kernel-weight-bounds-valid (index 0) (error right-error))
                        (:instance lw-kernel-weight-bounds-width (error left-error))
                        (:instance lw-kernel-weight-bounds-width (index 0) (error right-error))
                        (:instance lw-km-scaled-lower-comparison
                          (lower (car (lw-kernel-weight-bounds value sigma index step left-error)))
                          (upper (cdr (lw-kernel-weight-bounds value sigma index step left-error)))
                          (base-lower (car (lw-kernel-weight-bounds value sigma 0 step right-error)))
                          (base-upper (cdr (lw-kernel-weight-bounds value sigma 0 step right-error)))
                          (factor (lw-exp-term value index)) (error left-error) (base-error right-error)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-kernel-moment-bands-overlap lw-kernel-weight-bounds-valid
                                   lw-kernel-weight-bounds-width)))))

(defthm lw-kernel-moment-lower-bounds
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (natp index))
           (and
            (rationalp (car (lw-kernel-weight-bounds value sigma index step left-error)))
            (<= 0 (car (lw-kernel-weight-bounds value sigma index step left-error)))
            (<= (car (lw-kernel-weight-bounds value sigma index step left-error)) (* step (lw-exp-term value index)))
            (rationalp (* (lw-exp-term value index) (car (lw-kernel-weight-bounds value sigma 0 step right-error))))
            (<= 0 (* (lw-exp-term value index) (car (lw-kernel-weight-bounds value sigma 0 step right-error))))
            (<= (* (lw-exp-term value index) (car (lw-kernel-weight-bounds value sigma 0 step right-error)))
                (* step (lw-exp-term value index)))))
  :hints (("Goal" :use ((:instance lw-kernel-weight-bounds-valid (error left-error))
                        (:instance lw-kernel-weight-bounds-valid (index 0) (error right-error))
                        (:instance lw-km-multiply-order
                          (a 0) (b (car (lw-kernel-weight-bounds value sigma 0 step right-error)))
                          (factor (lw-exp-term value index)))
                        (:instance lw-km-multiply-order
                          (a (car (lw-kernel-weight-bounds value sigma 0 step right-error))) (b step)
                          (factor (lw-exp-term value index))))
                  :in-theory (e/d (lw-intervalp lw-kernel-weight-scale)
                                  (lw-kernel-weight-bounds-valid)))))

(assert-event
 (and (equal (lw-kernel-weight-scale 2 3 1/10) 2/15)
      (equal (lw-kernel-weight-scale 2 0 1/10) 1/10)
      (<= (abs (- (car (lw-kernel-weight-bounds 2 3 3 1/10 1/100))
                   (* 4/3 (car (lw-kernel-weight-bounds 2 3 0 1/10 1/200)))))
          (+ 1/100 (* 4/3 1/200)))))
