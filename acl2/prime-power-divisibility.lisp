(in-package "ACL2")

(include-book "bezout-gcd")

; Prime divisors of powers and uniqueness of the actual prime-power
; search result. Every divisibility statement uses the proved bridge
; to the trial-division primality predicate.

(local (in-theory
 (disable lw-primep lw-no-divisor lw-divides lw-bezout-data lw-integer-gcd
          lw-prime-power-data lw-prime-power-search lw-power-exponent lw-rational-power)))

(local (defthm lw-ppd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppd-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppd-times-negative)))))

(local (defthm lw-ppd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppd-left-commutes)))))

(local (defthm lw-ppd-integer-product
 (implies (and (integerp a) (integerp b)) (integerp (* a b)))
 :rule-classes nil))

(local (defthm lw-ppd-power-integer
 (implies (integerp base) (integerp (lw-rational-power base exponent)))
 :hints (("Goal" :induct (lw-rational-power base exponent)
                 :in-theory (enable lw-rational-power)))))

(defthm lw-rational-power-natural
 (implies (and (natp base) (natp exponent)) (natp (lw-rational-power base exponent)))
 :hints (("Goal" :use (lw-ppd-power-integer lw-rational-power-nonnegative)
                 :in-theory (disable lw-ppd-power-integer lw-rational-power-nonnegative)
                 :do-not-induct t)))

(defthm lw-divides-multiple
 (implies (and (lw-divides divisor value) (integerp factor))
  (lw-divides divisor (* factor value)))
 :hints (("Goal"
  :use ((:instance lw-ppd-integer-product (a factor) (b (* value (/ divisor)))))
  :in-theory (enable lw-divides)
  :do-not-induct t)))

(defthm lw-divides-positive-power
 (implies (and (lw-divides divisor base) (natp base) (posp exponent))
  (lw-divides divisor (lw-rational-power base exponent)))
 :hints (("Goal"
  :use ((:instance lw-rational-power-natural (exponent (- exponent 1)))
        (:instance lw-divides-multiple (value base) (factor (lw-rational-power base (- exponent 1)))))
  :expand ((lw-rational-power base exponent))
  :in-theory (disable lw-divides-multiple lw-rational-power-natural)
  :do-not-induct t)))

(local (defthm lw-ppd-prime-not-divides-one
 (implies (lw-primep prime) (not (lw-divides prime 1)))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value prime))
        (:instance lw-divides-positive-bound (divisor prime) (value 1)))
  :in-theory (disable lw-primep-lower-bound lw-divides-positive-bound)
  :do-not-induct t))))

(defthm lw-prime-divides-power
 (implies (and (lw-primep prime) (natp base) (natp exponent)
               (lw-divides prime (lw-rational-power base exponent)))
  (lw-divides prime base))
 :hints (("Goal"
  :induct (lw-rational-power base exponent)
  :in-theory (enable (:induction lw-rational-power) (:definition lw-rational-power)))
  (and stable-under-simplificationp
   '(:use ((:instance lw-rational-power-natural (exponent (- exponent 1)))
           (:instance lw-prime-divides-product (x base) (y (lw-rational-power base (- exponent 1)))))
     :in-theory (disable lw-rational-power lw-rational-power-natural lw-prime-divides-product)
     :do-not-induct t))))

(defthm lw-prime-power-base-unique
 (implies (and (lw-primep left-prime) (lw-primep right-prime)
               (posp left-exponent) (posp right-exponent)
               (equal (lw-rational-power left-prime left-exponent)
                      (lw-rational-power right-prime right-exponent)))
  (equal left-prime right-prime))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value left-prime))
        (:instance lw-primep-lower-bound (value right-prime))
        (:instance lw-divides-self (divisor left-prime))
        (:instance lw-divides-positive-power (divisor left-prime) (base left-prime) (exponent left-exponent))
        (:instance lw-prime-divides-power (prime left-prime) (base right-prime) (exponent right-exponent))
        (:instance lw-prime-divisor-one-or-self (prime right-prime) (divisor left-prime)))
  :in-theory (disable lw-primep-lower-bound lw-divides-self lw-divides-positive-power
                      lw-prime-divides-power lw-prime-divisor-one-or-self)
  :do-not-induct t)))

(defthm lw-rational-power-strict-exponent
 (implies (and (rationalp base) (< 1 base) (natp left) (natp right) (< left right))
  (< (lw-rational-power base left) (lw-rational-power base right)))
 :hints (("Goal"
  :use ((:instance lw-rational-power-at-least-one (exponent left))
        (:instance lw-rational-power-monotone-exponent (small (+ 1 left)) (large right)))
  :expand ((lw-rational-power base (+ 1 left)))
  :in-theory (disable lw-rational-power-at-least-one lw-rational-power-monotone-exponent)
  :nonlinearp t :do-not-induct t)))

(defthm lw-rational-power-exponent-injective
 (implies (and (rationalp base) (< 1 base) (natp left) (natp right)
               (equal (lw-rational-power base left) (lw-rational-power base right)))
  (equal left right))
 :rule-classes nil
 :hints (("Goal"
  :use (lw-rational-power-strict-exponent
        (:instance lw-rational-power-strict-exponent (left right) (right left)))
  :in-theory (disable lw-rational-power-strict-exponent)
  :do-not-induct t)))

(defthm lw-prime-power-data-exact
 (implies (and (lw-primep base) (posp exponent))
  (equal (lw-prime-power-data (lw-rational-power base exponent)) (cons base exponent)))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value base))
        lw-rational-power-natural
        (:instance lw-prime-power-data-complete (value (lw-rational-power base exponent)))
        (:instance lw-prime-power-data-sound (value (lw-rational-power base exponent)))
        (:instance lw-prime-power-base-unique
         (left-prime base) (left-exponent exponent)
         (right-prime (car (lw-prime-power-data (lw-rational-power base exponent))))
         (right-exponent (cdr (lw-prime-power-data (lw-rational-power base exponent)))))
        (:instance lw-rational-power-exponent-injective
         (left exponent) (right (cdr (lw-prime-power-data (lw-rational-power base exponent))))))
  :in-theory (disable lw-primep-lower-bound lw-rational-power-natural
                      lw-prime-power-data-complete lw-prime-power-data-sound)
  :do-not-induct t)))

(defthm lw-rational-power-add-exponents
 (implies (and (rationalp base) (natp left) (natp right))
  (equal (lw-rational-power base (+ left right))
         (* (lw-rational-power base left) (lw-rational-power base right))))
 :hints (("Goal" :induct (lw-rational-power base left)
                 :in-theory (enable lw-rational-power))))

(defthm lw-divides-powers-same-base
 (implies (and (integerp base) (< 1 base) (natp left) (natp right))
  (equal (lw-divides (lw-rational-power base left) (lw-rational-power base right))
         (<= left right)))
 :hints (("Goal"
  :cases ((<= left right))
  :use ((:instance lw-rational-power-natural (exponent left))
        (:instance lw-rational-power-natural (exponent right))
        (:instance lw-rational-power-natural (exponent (- right left)))
        (:instance lw-rational-power-at-least-one (exponent left))
        (:instance lw-rational-power-at-least-one (exponent right))
        (:instance lw-rational-power-strict-exponent (left right) (right left))
        (:instance lw-divides-positive-bound
         (divisor (lw-rational-power base left)) (value (lw-rational-power base right)))
        (:instance lw-rational-power-add-exponents (right (- right left)))
        (:instance lw-divides-self (divisor (lw-rational-power base left)))
        (:instance lw-divides-multiple
         (divisor (lw-rational-power base left)) (value (lw-rational-power base left))
         (factor (lw-rational-power base (- right left)))))
  :in-theory (disable lw-rational-power-natural lw-rational-power-at-least-one
                      lw-rational-power-strict-exponent lw-divides-positive-bound
                      lw-rational-power-add-exponents lw-divides-self lw-divides-multiple)
  :do-not-induct t)))

(defthm lw-prime-power-divisor-base
 (implies (and (lw-primep left-prime) (lw-primep right-prime)
               (posp left-exponent) (natp right-exponent)
               (lw-divides (lw-rational-power left-prime left-exponent)
                           (lw-rational-power right-prime right-exponent)))
  (equal left-prime right-prime))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value left-prime))
        (:instance lw-primep-lower-bound (value right-prime))
        (:instance lw-divides-self (divisor left-prime))
        (:instance lw-divides-positive-power (divisor left-prime) (base left-prime) (exponent left-exponent))
        (:instance lw-divides-transitive
         (a left-prime) (b (lw-rational-power left-prime left-exponent))
         (c (lw-rational-power right-prime right-exponent)))
        (:instance lw-prime-divides-power (prime left-prime) (base right-prime) (exponent right-exponent))
        (:instance lw-prime-divisor-one-or-self (prime right-prime) (divisor left-prime)))
  :in-theory (disable lw-primep-lower-bound lw-divides-self lw-divides-positive-power
                      lw-divides-transitive lw-prime-divides-power lw-prime-divisor-one-or-self)
  :do-not-induct t)))


