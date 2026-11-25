(in-package "ACL2")

(include-book "mobius-sieve-coefficients")
(include-book "prime-valuations")

; Divisor sums implement the finite multiplication by each sieve factor.

(local (defthm lw-msds-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-msds-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-msds-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-msds-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-msds-times-negative (a b) (b a)))
                 :in-theory (disable lw-msds-times-negative)))))

(local (defthm lw-msds-zero-times (equal (* 0 a) 0)))

(local (defthm lw-msds-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-msds-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-msds-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-msds-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-msds-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-msds-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-msds-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msds-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msds-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-msds-left-commutes)))))

(local (deftheory lw-msds-arithmetic (union-theories
            '(fold-consts-in-+
              lw-msds-left-commutes lw-msds-left-distributes lw-msds-fold-constants
              lw-msds-times-negative lw-msds-negative-times lw-msds-zero-times
              lw-msds-minus-one lw-msds-double-negative lw-msds-add-cancel lw-msds-double lw-msds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defthm lw-mobius-sieve-divisor-step-no-prime
  (implies
   (and (consp primes) (lw-prime-listp primes) (no-duplicatesp-equal primes) (posp value)
       (natp limit) (natp count) (<= count limit) (not (lw-divides (car primes) value)))
   (equal (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table primes limit)) (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table (cdr primes) limit))))
  :hints (("Goal"
           :induct (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table primes limit))
           :in-theory (union-theories '(lw-divisor-coefficient-sum) (theory 'lw-msds-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mobius-sieve-table-coefficient (value count))
                       (:instance lw-mobius-sieve-table-coefficient (primes (cdr primes)) (value count))
                       (:instance lw-mobius-sieve-convolution-step (value count))
                       (:instance lw-divides-transitive (a (car primes)) (b count) (c value)))
                 :do-not-induct t)))
  :rule-classes nil)

(local
 (defthm lw-msds-multiple-remainder
   (implies (and (posp prime) (natp quotient) (natp remainder) (< remainder prime))
            (iff (lw-divides prime (+ (* prime quotient) remainder)) (equal remainder 0)))
   :hints (("Goal"
            :use ((:instance lw-divides-positive-product (divisor prime) (value quotient))
                  (:instance lw-divides-zero (divisor prime))
                  (:instance lw-divides-linear-combination
                    (divisor prime) (a (+ (* prime quotient) remainder)) (b (* prime quotient)) (x 1) (y -1))
                  (:instance lw-divides-positive-bound (divisor prime) (value remainder)))
            :in-theory (theory 'lw-msds-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defun lw-msds-multiple-divisor-sum (primes prime value count)
   (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
   (if (zp count) 0
     (+ (if (and (lw-divides prime count) (lw-divides count value))
             (lw-mobius-sieve-coefficient primes (* count (/ prime))) 0)
        (lw-msds-multiple-divisor-sum primes prime value (- count 1))))))

(local
 (defthm lw-msds-multiple-divisor-sum-rational
   (rationalp (lw-msds-multiple-divisor-sum primes prime value count))
   :hints (("Goal"
            :induct (lw-msds-multiple-divisor-sum primes prime value count)
            :in-theory (union-theories '(lw-msds-multiple-divisor-sum) (theory 'lw-msds-arithmetic)))
           (and stable-under-simplificationp
                '(:use ((:instance lw-mobius-sieve-coefficient-range (value (* count (/ prime)))))
                  :do-not-induct t)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-msds-split-sieve-sum
   (implies (and (consp primes) (lw-prime-listp primes) (no-duplicatesp-equal primes) (posp value)
       (natp limit) (natp count) (<= count limit))
            (equal (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table primes limit))
                   (- (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table (cdr primes) limit)) (lw-msds-multiple-divisor-sum (cdr primes) (car primes) value count))))
   :hints (("Goal"
            :induct (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table primes limit))
            :in-theory (union-theories '(lw-divisor-coefficient-sum lw-msds-multiple-divisor-sum lw-msds-multiple-divisor-sum-rational
               lw-divisor-coefficient-sum-rational) (theory 'lw-msds-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-mobius-sieve-convolution-step (value count))
                        (:instance lw-mobius-sieve-table-coefficient (value count))
                        (:instance lw-mobius-sieve-table-coefficient (primes (cdr primes)) (value count))
                        (:instance lw-mobius-sieve-coefficient-range (primes (cdr primes)) (value count))
                        (:instance lw-mobius-sieve-coefficient-range (primes (cdr primes)) (value (* count (/ (car primes))))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-msds-multiple-sum-step
   (implies (posp count)
            (equal (lw-msds-multiple-divisor-sum primes prime value count)
                   (+ (if (and (lw-divides prime count) (lw-divides count value))
                           (lw-mobius-sieve-coefficient primes (* count (/ prime))) 0)
                      (lw-msds-multiple-divisor-sum primes prime value (- count 1)))))
   :hints (("Goal" :in-theory (union-theories '(lw-msds-multiple-divisor-sum) (theory 'lw-msds-arithmetic))))
   :rule-classes nil))

(local
 (defun lw-msds-countdown (count)
   (declare (xargs :measure (nfix count)))
   (if (zp count) 0 (lw-msds-countdown (- count 1)))))

(local
 (defthm lw-msds-ignore-remainder
   (implies (and (posp prime) (natp quotient) (natp remainder) (< remainder prime))
            (equal (lw-msds-multiple-divisor-sum primes prime value (+ (* prime quotient) remainder)) (lw-msds-multiple-divisor-sum primes prime value (* prime quotient))))
   :hints (("Goal"
            :induct (lw-msds-countdown remainder)
            :in-theory (union-theories '((:induction lw-msds-countdown) lw-msds-multiple-divisor-sum-rational lw-divisor-coefficient-sum-rational) (theory 'lw-msds-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-msds-multiple-remainder
                        (:instance lw-msds-multiple-sum-step (count (+ (* prime quotient) remainder))))
                  :nonlinearp t :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-msds-exact-multiple-step
   (implies (and (posp prime) (posp value) (lw-divides prime value) (posp quotient))
            (equal (lw-msds-multiple-divisor-sum primes prime value (* prime quotient))
                   (+ (if (lw-divides quotient (* value (/ prime))) (lw-mobius-sieve-coefficient primes quotient) 0)
                      (lw-msds-multiple-divisor-sum primes prime value (* prime (- quotient 1))))))
   :hints (("Goal"
            :use ((:instance lw-msds-ignore-remainder (quotient (- quotient 1)) (remainder (- prime 1)))
                  (:instance lw-divides-positive-quotient (divisor prime))
                  (:instance lw-divides-positive-product (divisor prime) (value quotient))
                  (:instance lw-divides-product-quotient (divisor prime) (value quotient))
                  (:instance lw-divides-cancel-common-factor (factor prime) (divisor quotient) (value (* value (/ prime))))
                  (:instance lw-msds-multiple-sum-step (count (* prime quotient))))
            :in-theory (union-theories '(lw-msds-multiple-divisor-sum-rational) (theory 'lw-msds-arithmetic))
            :nonlinearp t
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-msds-divisor-sum-step
   (implies (posp count)
            (equal (lw-divisor-coefficient-sum value count weights)
                   (+ (if (lw-divides count value) (lw-dirichlet-coefficient weights count) 0)
                      (lw-divisor-coefficient-sum value (- count 1) weights))))
   :hints (("Goal" :in-theory (union-theories '(lw-divisor-coefficient-sum) (theory 'lw-msds-arithmetic))))
   :rule-classes nil))

(local
 (defthm lw-msds-divisor-sum-zero
   (equal (lw-divisor-coefficient-sum value 0 weights) 0)
   :hints (("Goal" :expand ((lw-divisor-coefficient-sum value 0 weights))
                   :in-theory (theory 'ground-zero)))))

(local
 (defthm lw-msds-reindex-multiples
   (implies (and (posp prime) (posp value) (lw-divides prime value)
                 (natp quotient) (natp limit) (<= quotient limit))
            (equal (lw-msds-multiple-divisor-sum primes prime value (* prime quotient)) (lw-divisor-coefficient-sum (* value (/ prime)) quotient (lw-mobius-sieve-table primes limit))))
   :hints (("Goal"
            :induct (lw-msds-countdown quotient)
            :in-theory (union-theories '((:induction lw-msds-countdown) lw-msds-multiple-divisor-sum-rational lw-divisor-coefficient-sum-rational lw-msds-divisor-sum-zero) (theory 'lw-msds-arithmetic))
            :expand ((lw-divisor-coefficient-sum (* value (/ prime)) quotient (lw-mobius-sieve-table primes limit)) (lw-msds-multiple-divisor-sum primes prime value 0))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-msds-exact-multiple-step
                        (:instance lw-msds-divisor-sum-step (value (* value (/ prime))) (count quotient)
                          (weights (lw-mobius-sieve-table primes limit)))
                        (:instance lw-mobius-sieve-table-coefficient (value quotient)))
                  :expand ((lw-divisor-coefficient-sum (* value (/ prime)) 0 (lw-mobius-sieve-table primes limit))
                           (lw-msds-multiple-divisor-sum primes prime value 0))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-mobius-sieve-divisor-step-prime
  (implies
   (and (consp primes) (lw-prime-listp primes) (no-duplicatesp-equal primes)
        (posp value) (lw-divides (car primes) value) (natp limit) (<= value limit))
   (equal (lw-divisor-coefficient-sum value value (lw-mobius-sieve-table primes limit))
          (- (lw-divisor-coefficient-sum value value (lw-mobius-sieve-table (cdr primes) limit)) (lw-divisor-coefficient-sum (* value (/ (car primes))) (* value (/ (car primes))) (lw-mobius-sieve-table (cdr primes) limit)))))
  :hints (("Goal"
           :use ((:instance lw-primep-lower-bound (value (car primes)))
                 (:instance lw-divides-positive-quotient (divisor (car primes)))
                 (:instance lw-msds-split-sieve-sum (count value))
                 (:instance lw-msds-reindex-multiples (primes (cdr primes)) (prime (car primes)) (quotient (* value (/ (car primes))))))
           :in-theory (union-theories '(lw-prime-listp) (theory 'lw-msds-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
