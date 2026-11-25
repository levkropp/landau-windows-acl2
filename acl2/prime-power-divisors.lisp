(in-package "ACL2")

(include-book "prime-valuations")

; One prime power per occurrence in the factor list. Repeated occurrences
; of p generate p^v, p^(v-1), ..., p, each exactly once.

(local (in-theory (disable lw-primep lw-divides lw-prime-factors lw-rational-power
                          lw-prime-power-data lw-prime-power-search)))

(local (defthm lw-pfd-powers-equal
 (implies (and (lw-primep left-prime) (lw-primep right-prime)
               (posp left-exponent) (posp right-exponent))
  (equal (equal (lw-rational-power left-prime left-exponent)
                (lw-rational-power right-prime right-exponent))
         (and (equal left-prime right-prime) (equal left-exponent right-exponent))))
 :hints (("Goal"
  :use ((:instance lw-primep-lower-bound (value left-prime))
        lw-prime-power-base-unique
        (:instance lw-rational-power-exponent-injective
         (base left-prime) (left left-exponent) (right right-exponent)))
  :in-theory (disable lw-primep-lower-bound)
  :do-not-induct t))))

(defun lw-prime-power-factors (items)
 (if (consp items)
     (cons (lw-rational-power (car items) (+ 1 (lw-factor-count (car items) (cdr items))))
           (lw-prime-power-factors (cdr items)))
   nil))

(defthm lw-prime-power-factors-true-list
 (true-listp (lw-prime-power-factors items))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-prime-power-factors-member
 (implies (and (lw-prime-listp items) (lw-primep prime) (posp exponent))
  (iff (member-equal (lw-rational-power prime exponent) (lw-prime-power-factors items))
       (<= exponent (lw-factor-count prime items))))
 :hints (("Goal" :induct (lw-prime-power-factors items))))

(defthm lw-prime-power-factors-data
 (implies (and (lw-prime-listp items) (member-equal value (lw-prime-power-factors items)))
  (and (posp value) (lw-prime-power-data value)))
 :hints (("Goal" :induct (lw-prime-power-factors items))
  (and stable-under-simplificationp
   '(:use ((:instance lw-primep-lower-bound (value (car items)))
           (:instance lw-rational-power-natural
            (base (car items)) (exponent (+ 1 (lw-factor-count (car items) (cdr items)))))
           (:instance lw-rational-power-at-least-one
            (base (car items)) (exponent (+ 1 (lw-factor-count (car items) (cdr items)))))
           (:instance lw-prime-power-data-exact
            (base (car items)) (exponent (+ 1 (lw-factor-count (car items) (cdr items))))))
     :in-theory (disable lw-prime-power-factors lw-primep-lower-bound
                         lw-rational-power-natural lw-rational-power-at-least-one lw-prime-power-data-exact)
     :do-not-induct t))))

(defthm lw-prime-power-factors-no-duplicates
 (implies (lw-prime-listp items) (no-duplicatesp-equal (lw-prime-power-factors items)))
 :hints (("Goal" :induct (lw-prime-power-factors items))
  (and stable-under-simplificationp
   '(:use ((:instance lw-prime-power-factors-member
            (items (cdr items)) (prime (car items))
            (exponent (+ 1 (lw-factor-count (car items) (cdr items))))))
     :in-theory (disable lw-prime-power-factors lw-prime-power-factors-member)
     :do-not-induct t))))

(defun lw-prime-power-divisors (value)
 (lw-prime-power-factors (lw-prime-factors value)))

(defthm lw-prime-power-divisors-domain
 (implies (posp value)
  (iff (member-equal divisor (lw-prime-power-divisors value))
       (and (posp divisor) (lw-prime-power-data divisor) (lw-divides divisor value))))
 :hints (("Goal"
  :use ((:instance lw-prime-power-factors-data (items (lw-prime-factors value)) (value divisor))
        (:instance lw-prime-power-data-sound (value divisor))
        (:instance lw-prime-power-factors-member
         (items (lw-prime-factors value))
         (prime (car (lw-prime-power-data divisor))) (exponent (cdr (lw-prime-power-data divisor))))
        (:instance lw-prime-power-divisor-valuation
         (prime (car (lw-prime-power-data divisor))) (exponent (cdr (lw-prime-power-data divisor)))))
  :in-theory (e/d (lw-prime-valuation)
   (lw-prime-power-factors lw-prime-power-factors-data lw-prime-power-factors-member
    lw-prime-power-data-sound lw-prime-power-divisor-valuation))
  :do-not-induct t)))

(defthm lw-prime-power-divisors-no-duplicates
 (no-duplicatesp-equal (lw-prime-power-divisors value))
 :hints (("Goal" :in-theory (disable lw-prime-power-factors))))

