(in-package "ACL2")

(include-book "prime-factorization")

; Multiplicities of primes in the computed factor list characterize
; divisibility by every power. This is the counting bridge required by
; the finite von Mangoldt divisor sum.

(local (in-theory (disable lw-primep lw-no-divisor lw-divides
                          lw-prime-factors lw-rational-power lw-factor-product
                          lw-bezout-data lw-integer-gcd)))

(local (defthm lw-pvl-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                      (:instance associativity-of-* (x b) (y a) (z c))
                      (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pvl-cancel-equality
 (implies (and (rationalp factor) (< 0 factor) (rationalp a) (rationalp b)
               (equal (* factor a) (* factor b))) (equal a b))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pvl-inverse-product
 (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
  (equal (/ (* a b)) (* (/ a) (/ b))))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
        (:instance inverse-of-* (x (* a b)))
        (:instance lw-pvl-cancel-equality
         (factor (* a b)) (a (/ (* a b))) (b (* (/ a) (/ b)))))
  :in-theory (disable inverse-of-*) :nonlinearp t))))

(local (defthm lw-pvl-inverse-factor
 (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
 :hints (("Goal"
  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
        (:instance inverse-of-* (x divisor)))
  :in-theory (disable associativity-of-* commutativity-of-* lw-pvl-left-commutes)))))

(defthm lw-divides-cancel-common-factor
 (implies (and (posp factor) (posp divisor) (integerp value))
  (equal (lw-divides (* factor divisor) (* factor value))
         (lw-divides divisor value)))
 :hints (("Goal"
  :use ((:instance lw-pvl-inverse-factor (divisor factor) (coefficient (* value (/ divisor)))))
  :in-theory (e/d (lw-divides) (lw-pvl-inverse-factor))
  :nonlinearp t :do-not-induct t)))

(defthm lw-prime-power-remove-distinct-factor
 (implies (and (lw-primep prime) (lw-primep other) (not (equal prime other))
               (natp exponent) (natp value))
  (equal (lw-divides (lw-rational-power prime exponent) (* other value))
         (lw-divides (lw-rational-power prime exponent) value)))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value prime))
        (:instance lw-primep-lower-bound (value other))
        (:instance lw-prime-divisor-one-or-self (divisor other))
        (:instance lw-rational-power-natural (base prime))
        (:instance lw-rational-power-at-least-one (base prime))
        (:instance lw-prime-divides-power (prime other) (base prime))
        (:instance lw-prime-gcd-one (prime other) (x (lw-rational-power prime exponent)))
        (:instance lw-coprime-divides-product
         (divisor (lw-rational-power prime exponent)) (x other) (y value))
        (:instance lw-divides-multiple
         (divisor (lw-rational-power prime exponent)) (factor other)))
  :in-theory (disable lw-primep-lower-bound lw-prime-divisor-one-or-self
                      lw-rational-power-natural lw-rational-power-at-least-one
                      lw-prime-divides-power lw-prime-gcd-one
                      lw-coprime-divides-product lw-divides-multiple)
  :do-not-induct t)))

(defun lw-factor-count (prime items)
 (if (consp items)
     (+ (if (equal prime (car items)) 1 0) (lw-factor-count prime (cdr items)))
   0))

(defthm lw-factor-count-natural
 (natp (lw-factor-count prime items))
 :rule-classes (:rewrite :type-prescription))

(local (defun lw-pvl-induct (prime exponent items)
 (if (or (zp exponent) (not (consp items))) nil
   (if (equal prime (car items))
       (lw-pvl-induct prime (- exponent 1) (cdr items))
     (lw-pvl-induct prime exponent (cdr items))))))

(local (defthm lw-pvl-product-natural
 (implies (lw-prime-listp items) (natp (lw-factor-product items)))
 :hints (("Goal" :use (lw-prime-list-product-positive)
                 :in-theory (disable lw-prime-list-product-positive)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pvl-power-zero
 (equal (lw-rational-power prime 0) 1)
 :hints (("Goal" :expand ((lw-rational-power prime 0))))))

(local (defthm lw-pvl-divides-one
 (implies (integerp value) (lw-divides 1 value))
 :hints (("Goal" :in-theory (enable lw-divides)))))

(local (defthm lw-pvl-powers-empty
 (implies (and (lw-primep prime) (natp exponent))
  (equal (lw-divides (lw-rational-power prime exponent) 1) (equal exponent 0)))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value prime))
        (:instance lw-divides-powers-same-base (base prime) (left exponent) (right 0)))
  :in-theory (disable lw-primep-lower-bound lw-divides-powers-same-base)
  :do-not-induct t))))

(local (defthm lw-pvl-powers-matching-factor
 (implies (and (lw-primep prime) (posp exponent) (integerp value))
  (equal (lw-divides (lw-rational-power prime exponent) (* prime value))
         (lw-divides (lw-rational-power prime (- exponent 1)) value)))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value prime))
        (:instance lw-rational-power-natural (base prime) (exponent (- exponent 1)))
        (:instance lw-rational-power-at-least-one (base prime) (exponent (- exponent 1)))
        (:instance lw-divides-cancel-common-factor
         (factor prime) (divisor (lw-rational-power prime (- exponent 1)))))
  :expand ((lw-rational-power prime exponent))
  :in-theory (disable lw-primep-lower-bound lw-rational-power-natural
                      lw-rational-power-at-least-one lw-divides-cancel-common-factor)
  :do-not-induct t))))

(defthm lw-prime-power-list-divisor
 (implies (and (lw-primep prime) (natp exponent) (lw-prime-listp items))
  (equal (lw-divides (lw-rational-power prime exponent) (lw-factor-product items))
         (<= exponent (lw-factor-count prime items))))
 :hints (("Goal" :induct (lw-pvl-induct prime exponent items)
                 :in-theory (e/d (lw-factor-product)
                                 (lw-divides-multiple lw-prime-divides-product-iff)))))

(defun lw-prime-valuation (prime value)
 (lw-factor-count prime (lw-prime-factors value)))

(defthm lw-prime-valuation-natural
 (natp (lw-prime-valuation prime value))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-prime-power-divisor-valuation
 (implies (and (lw-primep prime) (posp value) (natp exponent))
  (equal (lw-divides (lw-rational-power prime exponent) value)
         (<= exponent (lw-prime-valuation prime value))))
 :hints (("Goal"
  :use ((:instance lw-prime-power-list-divisor (items (lw-prime-factors value))))
  :in-theory (disable lw-prime-power-list-divisor lw-factor-product)
  :do-not-induct t)))

