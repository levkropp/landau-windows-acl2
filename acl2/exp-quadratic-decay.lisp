(in-package "ACL2")

(include-book "exp-continuity")

; A coarse polynomial decay bound, uniform in the requested precision.
; Dyadic logarithmic blocks only need reciprocal-square decay.

(local (in-theory (disable lw-exp-bounds lw-exp-neg-bounds lw-exp-index
 lw-exp-start-index lw-exp-band lw-exp-sum lw-exp-term
 lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap)))

(local (defthm lw-eqd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eqd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eqd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eqd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eqd-times-negative (a b) (b a)))
                 :in-theory (disable lw-eqd-times-negative)))))

(local (defthm lw-eqd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eqd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eqd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eqd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eqd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eqd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eqd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eqd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eqd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eqd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eqd-left-commutes)))))

(local (defthm lw-eqd-taylor-two
 (implies (rationalp value)
  (equal (lw-exp-sum value 2) (+ 1 value (* 1/2 value value))))
 :hints (("Goal" :expand ((lw-exp-sum value 2) (lw-exp-sum value 1)
                         (lw-exp-sum value 0) (lw-exp-term value 2)
                         (lw-exp-term value 1) (lw-exp-term value 0))
                 :in-theory (disable lw-exp-sum lw-exp-term)))))

(local (defthm lw-eqd-native-lower
 (equal (car (lw-exp-bounds value epsilon))
        (lw-exp-sum value (lw-exp-index value epsilon)))
 :hints (("Goal" :in-theory (enable lw-exp-bounds lw-exp-band)))
 :rule-classes nil))

(defthm lw-exp-bounds-quadratic-growth
 (implies (and (rationalp value) (<= 0 value))
  (<= (* 1/2 value value) (cdr (lw-exp-bounds value epsilon))))
 :hints (("Goal"
  :cases ((<= value 1))
  :use (lw-exp-bounds-valid lw-exp-index-adequate lw-eqd-native-lower
        (:instance lw-exp-sum-monotone-index (small 2) (large (lw-exp-index value epsilon))))
  :in-theory (e/d (lw-intervalp)
    (lw-exp-bounds-valid lw-exp-index-adequate))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-eqd-cancel-equality
 (implies (and (rationalp factor) (< 0 factor) (rationalp a) (rationalp b)
               (equal (* factor a) (* factor b)))
  (equal a b))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eqd-quadratic-inverse
 (implies (and (rationalp value) (< 0 value))
  (equal (/ (* 1/2 value value)) (* 2 (/ value) (/ value))))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x value))
        (:instance inverse-of-* (x (* 1/2 value value)))
        (:instance lw-eqd-cancel-equality
         (factor (* 1/2 value value)) (a (/ (* 1/2 value value))) (b (* 2 (/ value) (/ value)))))
  :in-theory (disable inverse-of-*) :nonlinearp t))
 :rule-classes nil))

(defthm lw-exp-neg-bounds-quadratic-decay
 (implies (and (rationalp value) (< 0 value))
  (<= (car (lw-exp-neg-bounds value epsilon)) (* 2 (/ value) (/ value))))
 :hints (("Goal"
  :use (lw-exp-bounds-quadratic-growth lw-exp-bounds-valid lw-eqd-quadratic-inverse
        (:instance lw-reciprocal-antitone
          (left (* 1/2 value value)) (right (cdr (lw-exp-bounds value epsilon))))
        (:instance lw-eqd-inverse-factor (divisor value) (coefficient (/ value))))
  :in-theory (e/d (lw-exp-neg-bounds lw-intervalp)
   (lw-exp-bounds-quadratic-growth lw-exp-bounds-valid lw-reciprocal-antitone))
  :nonlinearp t :do-not-induct t)))

