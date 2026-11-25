(in-package "ACL2")

(include-book "prime-power-divisibility")

; A bounded least-divisor search, and its use as an actual prime-divisor
; constructor. There is no supplied factorization or primality oracle.

(local (in-theory (disable lw-divides lw-primep lw-no-divisor mod
                          lw-prime-power-data lw-rational-power)))

(defun lw-least-divisor-search (value trial)
 (declare (xargs :measure (nfix trial)))
 (if (or (not (natp trial)) (< trial 2))
     nil
   (let ((earlier (lw-least-divisor-search value (- trial 1))))
    (if earlier earlier
      (if (lw-divides trial value) trial nil)))))

(defthm lw-least-divisor-search-sound
 (implies (lw-least-divisor-search value trial)
  (let ((found (lw-least-divisor-search value trial)))
   (and (integerp found) (<= 2 found) (<= found trial)
        (lw-divides found value))))
 :hints (("Goal" :induct (lw-least-divisor-search value trial))))

(local (defthm lw-lpd-search-upper
 (implies (lw-least-divisor-search value trial)
  (<= (lw-least-divisor-search value trial) trial))
 :hints (("Goal" :use (lw-least-divisor-search-sound)
                 :in-theory (disable lw-least-divisor-search lw-least-divisor-search-sound)))
 :rule-classes :linear))

(defthm lw-least-divisor-search-minimal
 (implies (and (natp trial) (posp divisor) (<= 2 divisor) (<= divisor trial)
               (lw-divides divisor value))
  (and (lw-least-divisor-search value trial)
       (<= (lw-least-divisor-search value trial) divisor)))
 :hints (("Goal" :induct (lw-least-divisor-search value trial))))

(local (in-theory (disable lw-least-divisor-search)))

(local (defthm lw-lpd-no-proper-divisor
 (implies (and (natp limit) (lw-least-divisor-search value limit)
               (natp trial) (< trial (lw-least-divisor-search value limit)))
  (lw-no-divisor (lw-least-divisor-search value limit) trial))
 :hints (("Goal"
  :induct (lw-no-divisor (lw-least-divisor-search value limit) trial)
  :in-theory (enable lw-no-divisor))
  (and stable-under-simplificationp
   '(:use ((:instance lw-least-divisor-search-sound (trial limit))
           (:instance lw-divides-mod (divisor trial)
            (value (lw-least-divisor-search value limit)))
           (:instance lw-divides-transitive
            (a trial) (b (lw-least-divisor-search value limit)) (c value))
           (:instance lw-least-divisor-search-minimal (trial limit) (divisor trial)))
     :in-theory (disable lw-no-divisor lw-least-divisor-search-sound
                         lw-divides-mod lw-divides-transitive lw-least-divisor-search-minimal)
     :do-not-induct t)))))

(defun lw-least-prime-divisor (value)
 (lw-least-divisor-search value (nfix value)))

(defthm lw-least-prime-divisor-sound
 (implies (and (integerp value) (<= 2 value))
  (let ((found (lw-least-prime-divisor value)))
   (and (lw-primep found) (integerp found) (<= 2 found) (<= found value)
        (lw-divides found value))))
 :hints (("Goal"
  :use ((:instance lw-divides-self (divisor value))
        (:instance lw-least-divisor-search-minimal (trial value) (divisor value))
        (:instance lw-least-divisor-search-sound (trial value))
        (:instance lw-lpd-no-proper-divisor (limit value)
         (trial (- (lw-least-divisor-search value value) 1))))
  :in-theory (e/d (lw-least-prime-divisor lw-primep)
                  (lw-divides-self lw-least-divisor-search-minimal lw-least-divisor-search-sound
                   lw-lpd-no-proper-divisor))
  :do-not-induct t)))

(local (in-theory (disable lw-least-prime-divisor)))

(local (defthm lw-lpd-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                      (:instance associativity-of-* (x b) (y a) (z c))
                      (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lpd-inverse-factor
 (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
 :hints (("Goal"
  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
        (:instance inverse-of-* (x divisor)))
  :in-theory (disable associativity-of-* commutativity-of-* lw-lpd-left-commutes)))))

(defthm lw-least-prime-divisor-quotient
 (implies (and (integerp value) (<= 2 value))
  (let* ((prime (lw-least-prime-divisor value))
         (quotient (* value (/ prime))))
   (and (posp quotient) (< quotient value) (equal (* prime quotient) value))))
 :hints (("Goal"
  :use (lw-least-prime-divisor-sound
        (:instance lw-lpd-inverse-factor (divisor (lw-least-prime-divisor value)) (coefficient value)))
  :in-theory (e/d (lw-divides) (lw-least-prime-divisor-sound lw-lpd-inverse-factor))
  :nonlinearp t :do-not-induct t)))

