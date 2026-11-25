(in-package "ACL2")

(include-book "kernel-mass")

; Finite geometric tilts for the two tails. Their factors remain exact
; rationals until the checked derivative band bounds them geometrically.
(local (in-theory
        (disable lw-rational-power lw-rational-power-add-exponents lw-rational-power-product
                 lw-rising-binomial (:definition lw-negative-binomial-sum)
                 lw-negative-binomial-interval-mass-bound lw-kernel-grid-ratio lw-kernel-grid-ratio-valid
                 lw-mellin-grid-weight-sum lw-mellin-grid-weight-sum-majorant lw-kernel-grid-normalization)))
(local (defthm lw-kt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-kt-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kt-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-kt-zero-times (equal (* 0 a) 0)))
(local (defthm lw-kt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-kt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-kt-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-kt-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-kt-equal-times
         (implies (equal a b) (equal (* a factor) (* b factor))) :rule-classes nil))
(local (defthm lw-kt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-kt-left-commutes)))))
(local (defthm lw-kt-binomial-sum-zero
         (implies (zp count) (equal (lw-negative-binomial-sum address count index ratio) 0))
         :hints (("Goal" :in-theory (enable lw-negative-binomial-sum)))))

(defthm lw-rational-power-contractive-exponent
  (implies (and (rationalp base) (<= 0 base) (<= base 1) (natp small) (natp large) (<= small large))
           (<= (lw-rational-power base large) (lw-rational-power base small)))
  :hints (("Goal" :use ((:instance lw-rational-power-add-exponents (left small) (right (- large small)))
                        (:instance lw-rational-power-monotone-base (left base) (right 1) (exponent (- large small)))
                        (:instance lw-rational-power-nonnegative (exponent small))
                        (:instance lw-kt-multiply-order (a (lw-rational-power base (- large small))) (b 1)
                          (factor (lw-rational-power base small))))
                  :in-theory (disable lw-rational-power-monotone-base lw-rational-power-nonnegative))))

(defthm lw-rational-power-quotient-factor
  (implies (and (rationalp ratio) (rationalp tilted-ratio) (< 0 tilted-ratio) (natp address))
           (equal (lw-rational-power ratio address)
                  (* (lw-rational-power (/ ratio tilted-ratio) address) (lw-rational-power tilted-ratio address))))
  :hints (("Goal" :use ((:instance lw-rational-power-product (left (/ ratio tilted-ratio)) (right tilted-ratio) (exponent address))
                        (:instance lw-kt-inverse-factor (divisor tilted-ratio) (coefficient ratio)))
                  :in-theory (disable lw-kt-inverse-factor)))
  :rule-classes nil)

(local (defthm lw-kt-quotient-parameters
         (implies (and (rationalp ratio) (< 0 ratio) (rationalp tilted-ratio) (< 0 tilted-ratio))
                  (and (rationalp (/ ratio tilted-ratio)) (< 0 (/ ratio tilted-ratio))
                       (implies (<= tilted-ratio ratio) (<= 1 (/ ratio tilted-ratio)))
                       (implies (<= ratio tilted-ratio) (<= (/ ratio tilted-ratio) 1))))
         :hints (("Goal" :use ((:instance lw-positive-division-bound (numerator ratio) (divisor tilted-ratio) (bound 1))
                              (:instance lw-positive-division-lower-bound (numerator ratio) (divisor tilted-ratio) (bound 1)))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-negative-binomial-left-tilt
  (implies (and (natp address) (natp count) (natp cutoff) (<= (+ address count) cutoff) (natp index)
                (rationalp tilted-ratio) (< 0 tilted-ratio) (rationalp ratio) (<= tilted-ratio ratio) (< ratio 1))
           (<= (lw-negative-binomial-sum address count index ratio)
               (* (lw-rational-power (/ ratio tilted-ratio) cutoff) (lw-negative-binomial-sum address count index tilted-ratio))))
  :hints (("Goal" :induct (lw-negative-binomial-sum address count index ratio))
          (and stable-under-simplificationp
               '(:use (lw-kt-quotient-parameters
                       lw-rational-power-quotient-factor
                       (:instance lw-rational-power-monotone-exponent (base (/ ratio tilted-ratio)) (small address) (large cutoff))
                       (:instance lw-rational-power-nonnegative (base tilted-ratio) (exponent address))
                       (:instance lw-rising-binomial-nonnegative (value address))
                       (:instance lw-kt-nonnegative-product
                         (a (lw-rational-power tilted-ratio address)) (b (lw-rising-binomial address index)))
                       (:instance lw-kt-multiply-order
                         (a (lw-rational-power (/ ratio tilted-ratio) address)) (b (lw-rational-power (/ ratio tilted-ratio) cutoff))
                         (factor (* (lw-rational-power tilted-ratio address) (lw-rising-binomial address index)))))
                 :expand ((lw-negative-binomial-sum address count index ratio)
                          (lw-negative-binomial-sum address count index tilted-ratio))
                 :in-theory (disable lw-rational-power-monotone-exponent lw-rational-power-nonnegative lw-rising-binomial-nonnegative)
                 :do-not-induct t))))

(defthm lw-negative-binomial-right-tilt
  (implies (and (natp address) (natp count) (natp cutoff) (<= cutoff address) (natp index)
                (rationalp ratio) (< 0 ratio) (rationalp tilted-ratio) (<= ratio tilted-ratio) (< tilted-ratio 1))
           (<= (lw-negative-binomial-sum address count index ratio)
               (* (lw-rational-power (/ ratio tilted-ratio) cutoff) (lw-negative-binomial-sum address count index tilted-ratio))))
  :hints (("Goal" :induct (lw-negative-binomial-sum address count index ratio))
          (and stable-under-simplificationp
               '(:use (lw-kt-quotient-parameters
                       lw-rational-power-quotient-factor
                       (:instance lw-rational-power-contractive-exponent (base (/ ratio tilted-ratio)) (small cutoff) (large address))
                       (:instance lw-rational-power-nonnegative (base tilted-ratio) (exponent address))
                       (:instance lw-rising-binomial-nonnegative (value address))
                       (:instance lw-kt-nonnegative-product
                         (a (lw-rational-power tilted-ratio address)) (b (lw-rising-binomial address index)))
                       (:instance lw-kt-multiply-order
                         (a (lw-rational-power (/ ratio tilted-ratio) address)) (b (lw-rational-power (/ ratio tilted-ratio) cutoff))
                         (factor (* (lw-rational-power tilted-ratio address) (lw-rising-binomial address index)))))
                 :expand ((lw-negative-binomial-sum address count index ratio)
                          (lw-negative-binomial-sum address count index tilted-ratio))
                 :in-theory (disable lw-rational-power-contractive-exponent lw-rational-power-nonnegative lw-rising-binomial-nonnegative)
                 :do-not-induct t))))

(local (in-theory (disable lw-negative-binomial-left-tilt lw-negative-binomial-right-tilt)))

(defthm lw-negative-binomial-left-mass
  (implies (and (natp address) (natp count) (natp cutoff) (<= (+ address count) cutoff) (natp index)
                (rationalp tilted-ratio) (< 0 tilted-ratio) (rationalp ratio) (<= tilted-ratio ratio) (< ratio 1))
           (<= (lw-negative-binomial-sum address count index ratio)
               (* (lw-rational-power (/ ratio tilted-ratio) cutoff) (lw-rational-power (/ (- 1 tilted-ratio)) (+ 1 index)))))
  :hints (("Goal" :use (lw-negative-binomial-left-tilt lw-kt-quotient-parameters
                        (:instance lw-negative-binomial-interval-mass-bound (start address) (ratio tilted-ratio))
                        (:instance lw-rational-power-nonnegative (base (/ ratio tilted-ratio)) (exponent cutoff))
                        (:instance lw-kt-multiply-order
                          (a (lw-negative-binomial-sum address count index tilted-ratio))
                          (b (lw-rational-power (/ (- 1 tilted-ratio)) (+ 1 index)))
                          (factor (lw-rational-power (/ ratio tilted-ratio) cutoff))))
                  :in-theory (disable lw-rational-power-nonnegative))))

(defthm lw-negative-binomial-right-mass
  (implies (and (natp address) (natp count) (natp cutoff) (<= cutoff address) (natp index)
                (rationalp ratio) (< 0 ratio) (rationalp tilted-ratio) (<= ratio tilted-ratio) (< tilted-ratio 1))
           (<= (lw-negative-binomial-sum address count index ratio)
               (* (lw-rational-power (/ ratio tilted-ratio) cutoff) (lw-rational-power (/ (- 1 tilted-ratio)) (+ 1 index)))))
  :hints (("Goal" :use (lw-negative-binomial-right-tilt lw-kt-quotient-parameters
                        (:instance lw-negative-binomial-interval-mass-bound (start address) (ratio tilted-ratio))
                        (:instance lw-rational-power-nonnegative (base (/ ratio tilted-ratio)) (exponent cutoff))
                        (:instance lw-kt-multiply-order
                          (a (lw-negative-binomial-sum address count index tilted-ratio))
                          (b (lw-rational-power (/ (- 1 tilted-ratio)) (+ 1 index)))
                          (factor (lw-rational-power (/ ratio tilted-ratio) cutoff))))
                  :in-theory (disable lw-rational-power-nonnegative))))

(defthm lw-kernel-grid-ratio-antitone
  (implies (and (rationalp rate) (< 0 rate) (rationalp tilted-rate) (<= rate tilted-rate) (rationalp step) (< 0 step))
           (<= (lw-kernel-grid-ratio tilted-rate step) (lw-kernel-grid-ratio rate step)))
  :hints (("Goal" :use ((:instance lw-kt-multiply-order (a rate) (b tilted-rate) (factor step))
                        (:instance lw-reciprocal-antitone (left (+ 1 (* rate step))) (right (+ 1 (* tilted-rate step)))))
                  :in-theory (e/d (lw-kernel-grid-ratio) (lw-reciprocal-antitone)))))

(local (in-theory (disable lw-negative-binomial-left-mass lw-negative-binomial-right-mass lw-kernel-grid-ratio-antitone)))

(defthm lw-mellin-grid-weight-left-tail
  (implies (and (natp address) (natp count) (natp cutoff) (<= (+ address count) cutoff) (natp index)
                (rationalp rate) (< 0 rate) (rationalp tilted-rate) (<= rate tilted-rate)
                (rationalp step) (< 0 step) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum address count rate index step error)
               (* (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff)
                  (lw-rational-power (+ (/ tilted-rate) step) (+ 1 index)))))
  :hints (("Goal"
           :use (lw-kernel-grid-ratio-valid (:instance lw-kernel-grid-ratio-valid (rate tilted-rate))
                 lw-kernel-grid-ratio-antitone lw-mellin-grid-weight-sum-majorant
                 (:instance lw-negative-binomial-left-mass
                   (ratio (lw-kernel-grid-ratio rate step)) (tilted-ratio (lw-kernel-grid-ratio tilted-rate step)))
                 (:instance lw-kernel-grid-normalization (rate tilted-rate))
                 (:instance lw-kt-nonnegative-product (a step) (b (lw-rational-power step index)))
                 (:instance lw-kt-multiply-order
                   (a (lw-negative-binomial-sum address count index (lw-kernel-grid-ratio rate step)))
                   (b (* (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff)
                         (lw-rational-power (/ (- 1 (lw-kernel-grid-ratio tilted-rate step))) (+ 1 index))))
                   (factor (* step (lw-rational-power step index))))
                 (:instance lw-kt-equal-times
                   (a (* step (lw-rational-power step index) (lw-rational-power (/ (- 1 (lw-kernel-grid-ratio tilted-rate step))) (+ 1 index))))
                   (b (lw-rational-power (+ (/ tilted-rate) step) (+ 1 index)))
                   (factor (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff))))
           :nonlinearp t)))

(defthm lw-mellin-grid-weight-right-tail
  (implies (and (natp address) (natp count) (natp cutoff) (<= cutoff address) (natp index)
                (rationalp tilted-rate) (< 0 tilted-rate) (rationalp rate) (<= tilted-rate rate)
                (rationalp step) (< 0 step) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum address count rate index step error)
               (* (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff)
                  (lw-rational-power (+ (/ tilted-rate) step) (+ 1 index)))))
  :hints (("Goal"
           :use (lw-kernel-grid-ratio-valid (:instance lw-kernel-grid-ratio-valid (rate tilted-rate))
                 (:instance lw-kernel-grid-ratio-antitone (rate tilted-rate) (tilted-rate rate))
                 lw-mellin-grid-weight-sum-majorant
                 (:instance lw-negative-binomial-right-mass
                   (ratio (lw-kernel-grid-ratio rate step)) (tilted-ratio (lw-kernel-grid-ratio tilted-rate step)))
                 (:instance lw-kernel-grid-normalization (rate tilted-rate))
                 (:instance lw-kt-nonnegative-product (a step) (b (lw-rational-power step index)))
                 (:instance lw-kt-multiply-order
                   (a (lw-negative-binomial-sum address count index (lw-kernel-grid-ratio rate step)))
                   (b (* (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff)
                         (lw-rational-power (/ (- 1 (lw-kernel-grid-ratio tilted-rate step))) (+ 1 index))))
                   (factor (* step (lw-rational-power step index))))
                 (:instance lw-kt-equal-times
                   (a (* step (lw-rational-power step index) (lw-rational-power (/ (- 1 (lw-kernel-grid-ratio tilted-rate step))) (+ 1 index))))
                   (b (lw-rational-power (+ (/ tilted-rate) step) (+ 1 index)))
                   (factor (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff))))
           :nonlinearp t)))

(local (defthm lw-kt-rate-scale
         (implies (and (rationalp rate) (< 0 rate) (rationalp step))
                  (equal (* (/ rate) (+ 1 (* rate step))) (+ (/ rate) step)))
         :hints (("Goal" :use ((:instance lw-kt-inverse-factor (divisor rate) (coefficient step)))
                         :in-theory (disable lw-kt-inverse-factor)))))

(local (defthm lw-kt-normalized-mass
         (implies (and (rationalp rate) (< 0 rate) (rationalp step) (< 0 step) (natp index) (<= (* 2 rate step (+ 1 index)) 1))
                  (<= (lw-rational-power (+ (/ rate) step) (+ 1 index)) (* 2 (lw-rational-power (/ rate) (+ 1 index)))))
         :hints (("Goal" :use ((:instance lw-rational-power-product (left (/ rate)) (right (+ 1 (* rate step))) (exponent (+ 1 index)))
                              (:instance lw-rational-power-small-increment (increment (* rate step)) (exponent (+ 1 index)))
                              (:instance lw-rational-power-nonnegative (base (/ rate)) (exponent (+ 1 index)))
                              (:instance lw-kt-multiply-order (a (lw-rational-power (+ 1 (* rate step)) (+ 1 index))) (b 2)
                                (factor (lw-rational-power (/ rate) (+ 1 index)))))
                         :in-theory (disable lw-rational-power-small-increment lw-rational-power-nonnegative)))
         :rule-classes nil))

(local (in-theory (disable lw-mellin-grid-weight-left-tail lw-mellin-grid-weight-right-tail)))

(defthm lw-mellin-grid-weight-left-tail-normalized
  (implies (and (natp address) (natp count) (natp cutoff) (<= (+ address count) cutoff) (natp index)
                (rationalp rate) (< 0 rate) (rationalp tilted-rate) (<= rate tilted-rate)
                (rationalp step) (< 0 step) (<= (* 2 tilted-rate step (+ 1 index)) 1) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum address count rate index step error)
               (* 2 (lw-rational-power (/ tilted-rate) (+ 1 index))
                  (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff))))
  :hints (("Goal" :use (lw-mellin-grid-weight-left-tail
                        lw-kernel-grid-ratio-valid (:instance lw-kernel-grid-ratio-valid (rate tilted-rate))
                        (:instance lw-kt-normalized-mass (rate tilted-rate))
                        (:instance lw-rational-power-nonnegative
                          (base (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step))) (exponent cutoff))
                        (:instance lw-kt-multiply-order
                          (a (lw-rational-power (+ (/ tilted-rate) step) (+ 1 index)))
                          (b (* 2 (lw-rational-power (/ tilted-rate) (+ 1 index))))
                          (factor (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff))))
                  :in-theory (disable lw-rational-power-nonnegative))))

(defthm lw-mellin-grid-weight-right-tail-normalized
  (implies (and (natp address) (natp count) (natp cutoff) (<= cutoff address) (natp index)
                (rationalp tilted-rate) (< 0 tilted-rate) (rationalp rate) (<= tilted-rate rate)
                (rationalp step) (< 0 step) (<= (* 2 tilted-rate step (+ 1 index)) 1) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum address count rate index step error)
               (* 2 (lw-rational-power (/ tilted-rate) (+ 1 index))
                  (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff))))
  :hints (("Goal" :use (lw-mellin-grid-weight-right-tail
                        lw-kernel-grid-ratio-valid (:instance lw-kernel-grid-ratio-valid (rate tilted-rate))
                        (:instance lw-kt-normalized-mass (rate tilted-rate))
                        (:instance lw-rational-power-nonnegative
                          (base (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step))) (exponent cutoff))
                        (:instance lw-kt-multiply-order
                          (a (lw-rational-power (+ (/ tilted-rate) step) (+ 1 index)))
                          (b (* 2 (lw-rational-power (/ tilted-rate) (+ 1 index))))
                          (factor (lw-rational-power (/ (lw-kernel-grid-ratio rate step) (lw-kernel-grid-ratio tilted-rate step)) cutoff))))
                  :in-theory (disable lw-rational-power-nonnegative))))
