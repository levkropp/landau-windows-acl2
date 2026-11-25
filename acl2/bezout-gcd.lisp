(in-package "ACL2")

(include-book "integer-divisibility")

; Subtractive Euclid with explicit integer Bezout coefficients.
; The gcd and its two multipliers are computed together by a natural
; measure. No factorization or coprimality witness is supplied as input.

(local (in-theory (disable lw-divides mod floor nonnegative-integer-quotient lw-primep lw-no-divisor)))

(local (defthm lw-bzg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-bzg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-bzg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-bzg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-bzg-times-negative (a b) (b a)))
                 :in-theory (disable lw-bzg-times-negative)))))

(local (defthm lw-bzg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-bzg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-bzg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-bzg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-bzg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-bzg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-bzg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-bzg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-bzg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-bzg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-bzg-left-commutes)))))

(local (defthm lw-bzg-integer-sum
 (implies (and (integerp a) (integerp b)) (integerp (+ a b)))
 :rule-classes nil))

(local (defthm lw-bzg-integer-subtract-iff
 (implies (and (rationalp a) (rationalp b) (integerp a))
  (equal (integerp (- b a)) (integerp b)))
 :hints (("Goal"
  :cases ((integerp b))
  :use ((:instance lw-bzg-integer-sum (a (- b a)) (b a)))
  :do-not-induct t))))

(defun lw-bezout-data (x y)
 (declare (xargs :measure (+ (nfix x) (nfix y))))
 (cond ((or (not (natp x)) (not (natp y))) (list 0 0 0))
       ((equal x 0) (list y 0 1))
       ((equal y 0) (list x 1 0))
       ((<= x y)
        (let ((data (lw-bezout-data x (- y x))))
         (list (car data) (- (cadr data) (caddr data)) (caddr data))))
       (t
        (let ((data (lw-bezout-data (- x y) y)))
         (list (car data) (cadr data) (- (caddr data) (cadr data)))))))

(defthm lw-bezout-data-integers
 (and (integerp (car (lw-bezout-data x y))) (<= 0 (car (lw-bezout-data x y)))
      (integerp (cadr (lw-bezout-data x y))) (integerp (caddr (lw-bezout-data x y))))
 :hints (("Goal" :induct (lw-bezout-data x y)))
 :rule-classes (:rewrite (:forward-chaining :trigger-terms ((lw-bezout-data x y)))))

(defun lw-integer-gcd (x y) (car (lw-bezout-data x y)))

(defthm lw-integer-gcd-natural
 (natp (lw-integer-gcd x y))
 :hints (("Goal" :in-theory (enable lw-integer-gcd)))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-integer-gcd-positive
 (implies (and (natp x) (natp y) (or (< 0 x) (< 0 y)))
  (posp (lw-integer-gcd x y)))
 :hints (("Goal" :induct (lw-bezout-data x y) :in-theory (enable lw-integer-gcd))))

(defthm lw-bezout-identity
 (implies (and (natp x) (natp y))
  (equal (lw-integer-gcd x y)
         (+ (* (cadr (lw-bezout-data x y)) x) (* (caddr (lw-bezout-data x y)) y))))
 :hints (("Goal" :induct (lw-bezout-data x y) :in-theory (enable lw-integer-gcd))))

(local (defthm lw-bzg-self-quotient-integer
 (implies (rationalp value) (integerp (* value (/ value))))
 :hints (("Goal" :cases ((equal value 0))
                 :use ((:instance inverse-of-* (x value)))
                 :in-theory (disable inverse-of-*)
                 :do-not-induct t))))

(defthm lw-bezout-data-integer-quotients
 (implies (and (natp x) (natp y))
  (and (integerp (* x (/ (lw-integer-gcd x y))))
       (integerp (* y (/ (lw-integer-gcd x y))))))
 :hints (("Goal" :induct (lw-bezout-data x y) :in-theory (enable lw-integer-gcd))))

(local (in-theory (disable lw-integer-gcd lw-bezout-data)))

(defthm lw-integer-gcd-common-divisor
 (implies (and (natp x) (natp y) (or (< 0 x) (< 0 y)))
  (and (lw-divides (lw-integer-gcd x y) x)
       (lw-divides (lw-integer-gcd x y) y)))
 :hints (("Goal"
  :use (lw-integer-gcd-positive lw-bezout-data-integer-quotients)
  :in-theory (e/d (lw-divides) (lw-integer-gcd-positive lw-bezout-data-integer-quotients))
  :do-not-induct t)))

(defthm lw-prime-gcd-one
 (implies (and (lw-primep prime) (natp x) (not (lw-divides prime x)))
  (equal (lw-integer-gcd x prime) 1))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value prime))
        (:instance lw-integer-gcd-positive (y prime))
        (:instance lw-integer-gcd-common-divisor (y prime))
        (:instance lw-prime-divisor-one-or-self (divisor (lw-integer-gcd x prime))))
  :in-theory (disable lw-primep-lower-bound lw-integer-gcd-positive
                      lw-integer-gcd-common-divisor lw-prime-divisor-one-or-self)
  :do-not-induct t)))

(local (defthm lw-bzg-integer-product
 (implies (and (integerp a) (integerp b)) (integerp (* a b)))
 :rule-classes nil))


(local (defthm lw-bzg-factor-identity
 (implies (and (rationalp prime) (< 0 prime) (rationalp a) (rationalp b)
               (rationalp x) (rationalp y))
  (equal (+ (* a x y (/ prime)) (* b y))
         (* (+ (* a x) (* b prime)) (* y (/ prime)))))
 :hints (("Goal"
  :use ((:instance lw-bzg-inverse-factor (divisor prime) (coefficient (* b y))))
  :in-theory (disable lw-bzg-inverse-factor)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-bzg-recover-factor
 (implies (and (posp prime) (integerp a) (integerp b) (integerp x) (integerp y)
               (equal (+ (* a x) (* b prime)) 1)
               (integerp (* x y (/ prime))))
  (integerp (* y (/ prime))))
 :hints (("Goal"
  :use (lw-bzg-factor-identity
        (:instance lw-bzg-integer-product (a a) (b (* x y (/ prime))))
        (:instance lw-bzg-integer-product (a b) (b y))
        (:instance lw-bzg-integer-sum (a (* a x y (/ prime))) (b (* b y))))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-prime-divides-product
 (implies (and (lw-primep prime) (natp x) (natp y) (lw-divides prime (* x y)))
  (or (lw-divides prime x) (lw-divides prime y)))
 :hints (("Goal"
  :cases ((lw-divides prime x))
  :use ((:instance lw-primep-lower-bound (value prime))
        lw-prime-gcd-one
        (:instance lw-bezout-identity (y prime))
        (:instance lw-bezout-data-integers (y prime))
        (:instance lw-bzg-recover-factor (a (cadr (lw-bezout-data x prime))) (b (caddr (lw-bezout-data x prime)))))
  :in-theory (e/d (lw-divides)
    (lw-primep-lower-bound lw-prime-gcd-one lw-bezout-identity lw-bezout-data-integers))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-coprime-divides-product
 (implies (and (posp divisor) (natp x) (natp y)
               (equal (lw-integer-gcd divisor x) 1)
               (lw-divides divisor (* x y)))
  (lw-divides divisor y))
 :hints (("Goal"
  :use ((:instance lw-bezout-identity (x divisor) (y x))
        (:instance lw-bezout-data-integers (x divisor) (y x))
        (:instance lw-bzg-recover-factor (prime divisor)
         (a (caddr (lw-bezout-data divisor x))) (b (cadr (lw-bezout-data divisor x)))))
  :in-theory (e/d (lw-divides) (lw-bezout-identity lw-bezout-data-integers))
  :nonlinearp nil :do-not-induct t)))



