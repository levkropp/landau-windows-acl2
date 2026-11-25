(in-package "ACL2")

(include-book "kernel-mass")

; Finite Taylor sums compare integer exponential multiples and geometric
; powers in both directions. These estimates will discharge the tilt
; factors at the checked window index without analytic exponential input.
(local (in-theory
        (disable lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-index lw-exp-band lw-rational-power
                 lw-rational-power-add-exponents lw-rational-power-product
                 lw-rising-binomial lw-rising-binomial-symmetric lw-rising-binomial-majorizes-taylor-term
                 lw-negative-binomial-sum lw-negative-binomial-sum-last lw-negative-binomial-mass-bound lw-negative-binomial-interval-mass-bound
                 lw-exp-term-scale-argument lw-exp-bounds-valid)))
(local (defthm lw-eg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-eg-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-eg-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-eg-zero-times (equal (* 0 a) 0)))
(local (defthm lw-eg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-eg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-eg-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-eg-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-eg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defun lw-eg-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-eg-countdown (- index 1)))))
(local (defthm lw-eg-power-zero
         (implies (zp exponent) (equal (lw-rational-power base exponent) 1))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))
(local (defthm lw-eg-term-zero-index
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-eg-sum-zero-index
         (implies (zp index) (equal (lw-exp-sum value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-sum)))))
(local (defthm lw-eg-term-zero-value
         (implies (posp index) (equal (lw-exp-term 0 index) 0))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-eg-sum-zero-value
         (equal (lw-exp-sum 0 index) 1)
         :hints (("Goal" :induct (lw-exp-sum 0 index) :in-theory (enable lw-exp-sum)))))
(local (defthm lw-eg-binomial-sum-zero
         (implies (zp count) (equal (lw-negative-binomial-sum address count index ratio) 0))
         :hints (("Goal" :expand ((lw-negative-binomial-sum address count index ratio))))))
(local (defthm lw-eg-binomial-sum-one
         (implies (and (rationalp address) (rationalp ratio))
                  (equal (lw-negative-binomial-sum address 1 index ratio)
                         (* (lw-rational-power ratio address) (lw-rising-binomial address index))))
         :hints (("Goal" :expand ((lw-negative-binomial-sum address 1 index ratio)
                                   (lw-negative-binomial-sum (+ address 1) 0 index ratio))))))

(defthm lw-exp-sum-integer-upper
  (implies (and (rationalp value) (<= 0 value) (natp copies) (natp index))
           (<= (lw-exp-sum (* copies value) index) (lw-rational-power (lw-exp-sum value index) copies)))
  :hints (("Goal" :induct (lw-eg-countdown copies))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-sum-addition-upper (left (* (- copies 1) value)) (right value))
                       (:instance lw-exp-sum-at-least-one)
                       (:instance lw-eg-multiply-order (a (lw-exp-sum (* (- copies 1) value) index))
                         (b (lw-rational-power (lw-exp-sum value index) (- copies 1))) (factor (lw-exp-sum value index))))
                 :expand ((lw-rational-power (lw-exp-sum value index) copies))
                 :in-theory (disable lw-exp-sum-at-least-one) :do-not-induct t :nonlinearp t))))

(defthm lw-exp-sum-integer-lower
  (implies (and (rationalp value) (<= 0 value) (natp copies) (natp index))
           (<= (lw-rational-power (lw-exp-sum value index) copies) (lw-exp-sum (* copies value) (* copies index))))
  :hints (("Goal" :induct (lw-eg-countdown copies))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-sum-product-upper (left (* (- copies 1) value)) (right value)
                         (left-index (* (- copies 1) index)) (right-index index))
                       (:instance lw-exp-sum-at-least-one)
                       (:instance lw-eg-multiply-order (a (lw-rational-power (lw-exp-sum value index) (- copies 1)))
                         (b (lw-exp-sum (* (- copies 1) value) (* (- copies 1) index))) (factor (lw-exp-sum value index))))
                 :expand ((lw-rational-power (lw-exp-sum value index) copies))
                 :in-theory (disable lw-exp-sum-at-least-one) :do-not-induct t :nonlinearp t))))

(defthm lw-exp-sum-geometric-majorant
  (implies (and (natp copies) (natp index) (rationalp ratio) (<= 0 ratio))
           (<= (lw-exp-sum (* copies ratio) index) (lw-negative-binomial-sum 0 (+ 1 index) copies ratio)))
  :hints (("Goal" :induct (lw-eg-countdown index))
          (and stable-under-simplificationp
               '(:use ((:instance lw-negative-binomial-sum-last (start 0) (count index) (index copies))
                       (:instance lw-exp-term-scale-argument (value copies) (factor ratio))
                       (:instance lw-rising-binomial-majorizes-taylor-term (value copies))
                       (:instance lw-rising-binomial-symmetric (value copies))
                       (:instance lw-rational-power-nonnegative (base ratio) (exponent index))
                       (:instance lw-eg-multiply-order (a (lw-exp-term copies index)) (b (lw-rising-binomial copies index))
                         (factor (lw-rational-power ratio index))))
                 :expand ((lw-exp-sum (* copies ratio) index))
                 :in-theory (disable lw-rational-power-nonnegative) :do-not-induct t))))

(defthm lw-exp-sum-euler-upper
  (implies (and (natp copies) (natp index) (rationalp ratio) (<= 0 ratio) (< ratio 1))
           (<= (lw-exp-sum (* copies ratio) index) (lw-rational-power (/ (- 1 ratio)) (+ 1 copies))))
  :hints (("Goal" :use (lw-exp-sum-geometric-majorant
                        (:instance lw-negative-binomial-mass-bound (count (+ 1 index)) (index copies)))
                  :in-theory (disable lw-exp-sum-geometric-majorant))))

(local (in-theory
        (disable lw-exp-sum-integer-upper lw-exp-sum-integer-lower lw-exp-sum-geometric-majorant lw-exp-sum-euler-upper
                 lw-exp-linear-power-le-sum lw-exp-sum-monotone-argument lw-exp-sum-at-least-one lw-rational-power-monotone-base)))

(local (defthm lw-eg-left-constant
         (<= (cdr (lw-exp-bounds 1/6 1/1000)) 237/200)))
(local (defthm lw-eg-right-constant
         (<= 100/79 (lw-exp-sum 237/1000 4))))

(defthm lw-geometric-left-decay
  (implies (and (natp cutoff) (natp index) (rationalp increment) (<= 0 increment) (<= (* cutoff increment) (/ index 6)))
           (<= (lw-rational-power (+ 1 increment) cutoff) (lw-rational-power 237/200 index)))
  :hints (("Goal"
           :use ((:instance lw-exp-linear-power-le-sum (value increment) (index cutoff))
                 (:instance lw-exp-sum-monotone-argument (left (* cutoff increment)) (right (/ index 6)) (index cutoff))
                 (:instance lw-exp-sum-integer-upper (value 1/6) (copies index) (index cutoff))
                 (:instance lw-exp-partial-sum-upper (value 1/6) (index cutoff) (error 1/1000))
                 lw-eg-left-constant
                 (:instance lw-exp-sum-at-least-one (value 1/6) (index cutoff))
                 (:instance lw-rational-power-monotone-base (left (lw-exp-sum 1/6 cutoff)) (right 237/200) (exponent index)))
           :nonlinearp t)))

(local (defthm lw-eg-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-eg-equal-times
         (implies (equal a b) (equal (* a factor) (* b factor))) :rule-classes nil))
(local (defthm lw-eg-reciprocal-pair-order
         (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d) (<= 0 a) (<= 0 c)
                       (equal (* a b) 1) (equal (* c d) 1) (<= d b))
                  (<= a c))
         :hints (("Goal" :use ((:instance lw-eg-nonnegative-product (b c))
                              (:instance lw-eg-multiply-order (a d) (b b) (factor (* a c)))
                              (:instance lw-eg-equal-times (a (* a b)) (b 1) (factor c))
                              (:instance lw-eg-equal-times (a (* c d)) (b 1) (factor a)))
                         :nonlinearp t))
         :rule-classes nil))
(local (defthm lw-eg-power-successor
         (implies (natp exponent)
                  (equal (lw-rational-power base (+ 1 exponent)) (* base (lw-rational-power base exponent))))
         :hints (("Goal" :expand ((lw-rational-power base (+ 1 exponent)))))
         :rule-classes nil))

(defthm lw-geometric-right-decay
  (implies (and (natp cutoff) (natp index) (rationalp ratio) (<= 1/2 ratio) (<= ratio 1)
                (<= (* 237/1000 index) (* cutoff (- 1 ratio))))
           (<= (lw-rational-power ratio cutoff) (* 2 (lw-rational-power 79/100 index))))
  :hints (("Goal"
           :use (lw-eg-right-constant
                 (:instance lw-exp-sum-integer-lower (value 237/1000) (copies index) (index 4))
                 (:instance lw-exp-sum-monotone-argument (left (* index 237/1000)) (right (* cutoff (- 1 ratio))) (index (* 4 index)))
                 (:instance lw-exp-sum-euler-upper (copies cutoff) (ratio (- 1 ratio)) (index (* 4 index)))
                 (:instance lw-rational-power-monotone-base (left 100/79) (right (lw-exp-sum 237/1000 4)) (exponent index))
                 (:instance lw-rational-power-reciprocal-pair (value ratio) (index (+ 1 cutoff)))
                 (:instance lw-rational-power-reciprocal-pair (value 79/100))
                 (:instance lw-rational-power-nonnegative (base ratio) (exponent (+ 1 cutoff)))
                 (:instance lw-rational-power-nonnegative (base ratio) (exponent cutoff))
                 (:instance lw-rational-power-nonnegative (base 79/100) (exponent index))
                 (:instance lw-eg-reciprocal-pair-order
                   (a (lw-rational-power ratio (+ 1 cutoff))) (b (lw-rational-power (/ ratio) (+ 1 cutoff)))
                   (c (lw-rational-power 79/100 index)) (d (lw-rational-power 100/79 index)))
                 (:instance lw-eg-power-successor (base ratio) (exponent cutoff))
                 (:instance lw-eg-multiply-order (a 1/2) (b ratio) (factor (lw-rational-power ratio cutoff))))
           :in-theory (disable lw-rational-power-reciprocal-pair lw-rational-power-nonnegative)
           :nonlinearp t)))
