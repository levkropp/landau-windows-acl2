(in-package "ACL2")

(include-book "least-prime-divisor")

; Prime factorization is computed by repeated division by the proved
; least prime divisor. The product and prime-divisor membership are
; certified against the same primality and divisibility predicates.

(local (in-theory (disable lw-primep lw-no-divisor lw-divides
                          lw-least-prime-divisor lw-rational-power)))

(local (defthm lw-pfc-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                      (:instance associativity-of-* (x b) (y a) (z c))
                      (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(defthm lw-prime-divides-product-iff
 (implies (and (lw-primep prime) (natp x) (natp y))
  (equal (lw-divides prime (* x y))
         (or (lw-divides prime x) (lw-divides prime y))))
 :hints (("Goal"
  :use (lw-prime-divides-product
        (:instance lw-divides-multiple (divisor prime) (value x) (factor y))
        (:instance lw-divides-multiple (divisor prime) (value y) (factor x)))
  :in-theory (disable lw-prime-divides-product lw-divides-multiple)
  :do-not-induct t)))

(local (defthm lw-pfc-prime-divides-prime
 (implies (and (lw-primep prime) (lw-primep value))
  (equal (lw-divides prime value) (equal prime value)))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value prime))
        lw-primep-lower-bound
        (:instance lw-divides-self (divisor prime))
        (:instance lw-prime-divisor-one-or-self (prime value) (divisor prime)))
  :in-theory (disable lw-primep-lower-bound lw-divides-self lw-prime-divisor-one-or-self)
  :do-not-induct t))))

(local (defthm lw-pfc-prime-not-divides-one
 (implies (lw-primep prime) (not (lw-divides prime 1)))
 :hints (("Goal" :use ((:instance lw-primep-lower-bound (value prime))
                      (:instance lw-divides-positive-bound (divisor prime) (value 1)))
                 :in-theory (disable lw-primep-lower-bound lw-divides-positive-bound)))))

(defun lw-prime-listp (items)
 (if (consp items) (and (lw-primep (car items)) (lw-prime-listp (cdr items)))
   (equal items nil)))

(defun lw-factor-product (items)
 (if (consp items) (* (car items) (lw-factor-product (cdr items))) 1))

(defthm lw-prime-list-product-positive
 (implies (lw-prime-listp items) (posp (lw-factor-product items)))
 :hints (("Goal" :induct (lw-factor-product items) :nonlinearp t)
  (and stable-under-simplificationp
   '(:use ((:instance lw-primep-lower-bound (value (car items))))
     :in-theory (disable lw-primep-lower-bound)
     :nonlinearp t :do-not-induct t))))

(defthm lw-prime-list-product-divisor
 (implies (and (lw-prime-listp items) (lw-primep prime))
  (equal (lw-divides prime (lw-factor-product items))
         (if (member-equal prime items) t nil)))
 :hints (("Goal" :induct (lw-factor-product items)
                 :in-theory (enable member-equal))
  (and stable-under-simplificationp
   '(:use ((:instance lw-primep-lower-bound (value (car items)))
           (:instance lw-prime-list-product-positive (items (cdr items)))
           (:instance lw-prime-divides-product-iff
            (x (car items)) (y (lw-factor-product (cdr items)))))
     :in-theory (disable lw-primep-lower-bound lw-prime-divides-product-iff
                         lw-prime-list-product-positive lw-factor-product)
     :do-not-induct t))))

(defun lw-prime-factors (value)
 (declare (xargs :measure (nfix value)
  :hints (("Goal" :use (lw-least-prime-divisor-quotient)
                  :in-theory (disable lw-least-prime-divisor-quotient)))))
 (if (or (not (integerp value)) (< value 2))
     nil
   (cons (lw-least-prime-divisor value)
         (lw-prime-factors (* value (/ (lw-least-prime-divisor value)))))))

(defthm lw-prime-factors-prime
 (lw-prime-listp (lw-prime-factors value))
 :hints (("Goal" :induct (lw-prime-factors value))
  (and stable-under-simplificationp
   '(:use (lw-least-prime-divisor-sound)
     :in-theory (disable lw-least-prime-divisor-sound lw-prime-factors)
     :do-not-induct t))))

(defthm lw-prime-factors-product
 (implies (posp value) (equal (lw-factor-product (lw-prime-factors value)) value))
 :hints (("Goal" :induct (lw-prime-factors value))
  (and stable-under-simplificationp
   '(:use (lw-least-prime-divisor-quotient)
     :in-theory (disable lw-least-prime-divisor-quotient lw-prime-factors)
     :do-not-induct t))))

(defthm lw-prime-factors-divisor
 (implies (and (posp value) (lw-primep prime))
  (equal (lw-divides prime value) (if (member-equal prime (lw-prime-factors value)) t nil)))
 :hints (("Goal"
  :use ((:instance lw-prime-list-product-divisor (items (lw-prime-factors value))))
  :in-theory (disable lw-prime-list-product-divisor lw-prime-factors lw-factor-product)
  :do-not-induct t)))

