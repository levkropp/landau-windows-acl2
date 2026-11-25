(in-package "ACL2")

(include-book "prime-powers")

; Positive-divisor arithmetic for the repository's trial-division
; primality predicate. Divisibility uses an integer rational quotient;
; the equivalence with the existing MOD tests is proved below.

(local (in-theory (disable mod floor nonnegative-integer-quotient lw-primep lw-no-divisor)))

(local (defthm lw-idv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-idv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-idv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-idv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-idv-times-negative (a b) (b a)))
                 :in-theory (disable lw-idv-times-negative)))))

(local (defthm lw-idv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-idv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-idv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-idv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-idv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-idv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-idv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-idv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-idv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-idv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-idv-left-commutes)))))

(local (defthm lw-idv-integer-sum
 (implies (and (integerp a) (integerp b)) (integerp (+ a b)))
 :rule-classes nil))

(local (defthm lw-idv-integer-product
 (implies (and (integerp a) (integerp b)) (integerp (* a b)))
 :rule-classes nil))

(local (defthm lw-idv-floor-integer
 (integerp (floor value divisor))
 :hints (("Goal" :in-theory (enable floor)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-idv-integer-ratio-data
 (implies (integerp value)
  (and (equal (denominator value) 1) (equal (numerator value) value)))
 :hints (("Goal"
  :use ((:instance rational-implies1 (x value))
        (:instance lw-rational-cross-multiply)
        (:instance lowest-terms (x value) (n (denominator value)) (r value) (q 1)))
  :in-theory (disable lw-rational-cross-multiply)
  :do-not-induct t))))

(local (defthm lw-idv-floor-integer-quotient
 (implies (and (rationalp value) (rationalp divisor) (not (equal divisor 0))
               (integerp (* value (/ divisor))))
  (equal (floor value divisor) (* value (/ divisor))))
 :hints (("Goal"
  :use ((:instance lw-idv-integer-ratio-data (value (* value (/ divisor)))))
  :in-theory (enable floor)))
 :rule-classes nil))

(local (defthm lw-idv-cancel-equality
 (implies (and (rationalp factor) (< 0 factor) (rationalp a) (rationalp b)
               (equal (* factor a) (* factor b)))
  (equal a b))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-divides (divisor value)
 (and (posp divisor) (integerp value) (integerp (* value (/ divisor)))))

(local (in-theory (disable lw-divides)))

(defthm lw-divides-mod
 (implies (and (posp divisor) (integerp value))
  (equal (equal (mod value divisor) 0) (lw-divides divisor value)))
 :hints (("Goal"
  :cases ((integerp (* value (/ divisor))))
  :use ((:instance lw-idv-floor-integer-quotient)
        (:instance lw-idv-floor-integer)
        (:instance lw-idv-inverse-factor (coefficient value))
        (:instance lw-idv-cancel-equality
         (factor divisor) (a (* value (/ divisor))) (b (floor value divisor))))
  :in-theory (e/d (mod lw-divides) (lw-idv-inverse-factor))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-divides-self
 (implies (posp divisor) (lw-divides divisor divisor))
 :hints (("Goal" :in-theory (enable lw-divides))))

(defthm lw-divides-zero
 (implies (posp divisor) (lw-divides divisor 0))
 :hints (("Goal" :in-theory (enable lw-divides))))

(local (defthm lw-idv-ratio-chain
 (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b) (rationalp c))
  (equal (* (* b (/ a)) (* c (/ b))) (* c (/ a))))
 :hints (("Goal"
  :use ((:instance lw-idv-inverse-factor (divisor b) (coefficient (* c (/ a)))))
  :in-theory (disable lw-idv-inverse-factor)
  :nonlinearp nil :do-not-induct t))))

(defthm lw-divides-transitive
 (implies (and (lw-divides a b) (lw-divides b c))
  (lw-divides a c))
 :hints (("Goal"
  :use ((:instance lw-idv-integer-product (a (* b (/ a))) (b (* c (/ b)))))
  :in-theory (enable lw-divides)
  :do-not-induct t)))

(defthm lw-divides-linear-combination
 (implies (and (lw-divides divisor a) (lw-divides divisor b) (integerp x) (integerp y))
  (lw-divides divisor (+ (* x a) (* y b))))
 :hints (("Goal"
  :use ((:instance lw-idv-integer-product (a x) (b (* a (/ divisor))))
        (:instance lw-idv-integer-product (a y) (b (* b (/ divisor))))
        (:instance lw-idv-integer-sum (a (* x a (/ divisor))) (b (* y b (/ divisor)))))
  :in-theory (enable lw-divides)
  :do-not-induct t)))

(defthm lw-divides-positive-bound
 (implies (and (posp value) (lw-divides divisor value))
  (<= divisor value))
 :hints (("Goal"
  :use ((:instance lw-idv-positive-product (a value) (b (/ divisor)))
        (:instance lw-idv-multiply-order (a 1) (b (* value (/ divisor))) (factor divisor)))
  :in-theory (enable lw-divides)
  :nonlinearp t :do-not-induct t)))

(defthm lw-prime-divisor-one-or-self
 (implies (and (lw-primep prime) (lw-divides divisor prime))
  (or (equal divisor 1) (equal divisor prime)))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value prime))
        (:instance lw-divides-positive-bound (value prime))
        (:instance lw-divides-mod (value prime))
        (:instance lw-primep-no-proper-divisor (value prime)))
  :in-theory (e/d (lw-divides)
                  (lw-divides-positive-bound lw-divides-mod lw-primep-no-proper-divisor))
  :do-not-induct t)))

