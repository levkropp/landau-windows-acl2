(in-package "ACL2")

(include-book "prime-power-divisors")

; Reindex the actual bounded von Mangoldt divisor sum by occurrences
; in the computed prime factorization. Every summand uses the existing
; rational lower-bound evaluator at the same requested precision.

(local (in-theory (disable lw-primep lw-divides lw-prime-factors lw-rational-power
                          lw-prime-power-data lw-prime-power-divisors
                          lw-prime-power-factors lw-mangoldt-bounds lw-log-bounds)))

(defun lw-mangoldt-list-sum (items error)
 (if (consp items)
     (+ (car (lw-mangoldt-bounds (car items) error))
        (lw-mangoldt-list-sum (cdr items) error))
   0))

(defun lw-factor-log-sum (items error)
 (if (consp items)
     (+ (car (lw-log-bounds (car items) error))
        (lw-factor-log-sum (cdr items) error))
   0))

(local (defthm lw-mds-weight-rational
 (implies (and (rationalp error) (< 0 error))
  (rationalp (car (lw-mangoldt-bounds value error))))
 :hints (("Goal" :use ((:instance lw-mangoldt-bounds-interval (epsilon error)))
                 :in-theory (e/d (lw-intervalp) (lw-mangoldt-bounds-interval))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-mds-sum-rational
 (implies (and (rationalp error) (< 0 error))
  (rationalp (lw-mangoldt-list-sum items error)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-mds-sum-atom
 (implies (not (consp items)) (equal (lw-mangoldt-list-sum items error) 0))))

(local (defthm lw-mds-member-remove
 (iff (member-equal value (remove-equal removed items))
      (and (not (equal value removed)) (member-equal value items)))
 :hints (("Goal" :induct (remove-equal removed items)))))

(local (defthm lw-mds-remove-no-duplicates
 (implies (no-duplicatesp-equal items) (no-duplicatesp-equal (remove-equal value items)))
 :hints (("Goal" :induct (remove-equal value items)))))

(local (defthm lw-mds-sum-remove
 (implies (and (no-duplicatesp-equal items) (rationalp error) (< 0 error))
  (equal (lw-mangoldt-list-sum (remove-equal value items) error)
         (- (lw-mangoldt-list-sum items error)
            (if (member-equal value items) (car (lw-mangoldt-bounds value error)) 0))))
 :hints (("Goal" :induct (remove-equal value items)))))

(defun lw-positive-bounded-listp (items limit)
 (if (consp items)
     (and (posp (car items)) (<= (car items) limit)
          (lw-positive-bounded-listp (cdr items) limit))
   t))

(local (defthm lw-mds-remove-bounded
 (implies (and (natp limit) (< 0 limit) (lw-positive-bounded-listp items limit))
  (lw-positive-bounded-listp (remove-equal limit items) (- limit 1)))
 :hints (("Goal" :induct (remove-equal limit items)))))

(local (defun lw-mds-bad-bound (items limit)
 (if (consp items)
     (if (and (posp (car items)) (<= (car items) limit))
         (lw-mds-bad-bound (cdr items) limit)
       (car items))
   nil)))

(local (defthm lw-mds-bad-bound-witness
 (implies (not (lw-positive-bounded-listp items limit))
  (and (member-equal (lw-mds-bad-bound items limit) items)
       (not (and (posp (lw-mds-bad-bound items limit))
                 (<= (lw-mds-bad-bound items limit) limit)))))
 :hints (("Goal" :induct (lw-mds-bad-bound items limit)))))

(defthm lw-prime-power-divisors-bounded
 (implies (posp value) (lw-positive-bounded-listp (lw-prime-power-divisors value) value))
 :hints (("Goal"
  :use ((:instance lw-mds-bad-bound-witness (items (lw-prime-power-divisors value)) (limit value))
        (:instance lw-prime-power-divisors-domain
         (divisor (lw-mds-bad-bound (lw-prime-power-divisors value) value)))
        (:instance lw-divides-positive-bound
         (divisor (lw-mds-bad-bound (lw-prime-power-divisors value) value))))
  :in-theory (disable lw-positive-bounded-listp lw-mds-bad-bound lw-mds-bad-bound-witness
                      lw-prime-power-divisors-domain lw-divides-positive-bound)
  :do-not-induct t)))

(local (defun lw-mds-list-prefix (items limit error)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) 0
   (+ (if (member-equal limit items) (car (lw-mangoldt-bounds limit error)) 0)
      (lw-mds-list-prefix items (- limit 1) error)))))

(local (defthm lw-mds-prefix-remove-above
 (implies (and (natp limit) (integerp removed) (< limit removed))
  (equal (lw-mds-list-prefix (remove-equal removed items) limit error)
         (lw-mds-list-prefix items limit error)))
 :hints (("Goal" :induct (lw-mds-list-prefix items limit error)))))

(local (defun lw-mds-prefix-induct (items limit)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) items
   (lw-mds-prefix-induct (remove-equal limit items) (- limit 1)))))

(local (defthm lw-mds-prefix-sum
 (implies (and (no-duplicatesp-equal items) (natp limit)
               (lw-positive-bounded-listp items limit) (rationalp error) (< 0 error))
  (equal (lw-mds-list-prefix items limit error) (lw-mangoldt-list-sum items error)))
 :hints (("Goal" :induct (lw-mds-prefix-induct items limit)
                 :do-not '(generalize eliminate-destructors)
                 :in-theory (disable lw-mangoldt-list-sum))
  (and stable-under-simplificationp
   '(:use ((:instance lw-mds-sum-remove (value limit))
           (:instance lw-mds-prefix-remove-above (removed limit) (limit (- limit 1))))
     :in-theory (e/d (lw-positive-bounded-listp)
                     (lw-mds-sum-remove lw-mds-prefix-remove-above lw-mds-list-prefix
                      lw-mangoldt-list-sum))
     :do-not-induct t)))))

(defun lw-mangoldt-divisor-sum (value limit error)
 (declare (xargs :measure (nfix limit)))
 (if (zp limit) 0
   (+ (if (lw-divides limit value) (car (lw-mangoldt-bounds limit error)) 0)
      (lw-mangoldt-divisor-sum value (- limit 1) error))))

(local (defthm lw-mds-zero-weight
 (implies (not (lw-prime-power-data value)) (equal (car (lw-mangoldt-bounds value error)) 0))
 :hints (("Goal" :in-theory (enable lw-mangoldt-bounds)))))

(local (defthm lw-mds-prefix-divisors
 (implies (and (posp value) (natp limit))
  (equal (lw-mds-list-prefix (lw-prime-power-divisors value) limit error)
         (lw-mangoldt-divisor-sum value limit error)))
 :hints (("Goal" :induct (lw-mangoldt-divisor-sum value limit error))
  (and stable-under-simplificationp
   '(:cases ((lw-prime-power-data limit))
     :use ((:instance lw-prime-power-divisors-domain (divisor limit)))
     :in-theory (disable lw-mds-list-prefix lw-mangoldt-divisor-sum lw-prime-power-divisors-domain)
     :do-not-induct t)))))

(defthm lw-mangoldt-list-prime-powers
 (implies (lw-prime-listp items)
  (equal (lw-mangoldt-list-sum (lw-prime-power-factors items) error)
         (lw-factor-log-sum items error)))
 :hints (("Goal" :induct (lw-prime-power-factors items)
                 :in-theory (enable lw-prime-power-factors lw-mangoldt-bounds))))

(defthm lw-mangoldt-divisor-factor-sum
 (implies (and (posp value) (rationalp error) (< 0 error))
  (equal (lw-mangoldt-divisor-sum value value error)
         (lw-factor-log-sum (lw-prime-factors value) error)))
 :hints (("Goal"
  :use ((:instance lw-mds-prefix-sum (items (lw-prime-power-divisors value)) (limit value))
        (:instance lw-mds-prefix-divisors (limit value))
        lw-prime-power-divisors-bounded
        (:instance lw-prime-power-divisors-no-duplicates)
        (:instance lw-mangoldt-list-prime-powers (items (lw-prime-factors value))))
  :in-theory (e/d (lw-prime-power-divisors)
   (lw-mds-prefix-sum lw-mds-prefix-divisors lw-prime-power-divisors-bounded
    lw-prime-power-divisors-no-duplicates lw-mangoldt-list-prime-powers
    lw-mds-list-prefix lw-mangoldt-divisor-sum lw-mangoldt-list-sum lw-factor-log-sum))
  :do-not-induct t)))

