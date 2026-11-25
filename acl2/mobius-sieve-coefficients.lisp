(in-package "ACL2")

(include-book "prime-factorization")
(include-book "finite-dirichlet-convolution")

; Each listed prime can occur at most once in a nonzero coefficient.

(local (defthm lw-msc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-msc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-msc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-msc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-msc-times-negative (a b) (b a)))
                 :in-theory (disable lw-msc-times-negative)))))

(local (defthm lw-msc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-msc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-msc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-msc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-msc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-msc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-msc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-msc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-msc-left-commutes)))))

(local (deftheory lw-msc-arithmetic (union-theories
            '(fold-consts-in-+
              lw-msc-left-commutes lw-msc-left-distributes lw-msc-fold-constants
              lw-msc-times-negative lw-msc-negative-times lw-msc-zero-times
              lw-msc-minus-one lw-msc-double-negative lw-msc-add-cancel lw-msc-double lw-msc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-mobius-sieve-coefficient (primes value)
  (declare (xargs :measure (acl2-count primes)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp primes)
      (if (equal value 1) 1 0)
    (if (lw-divides (car primes) value)
        (- (lw-mobius-sieve-coefficient (cdr primes) (* value (/ (car primes)))))
      (lw-mobius-sieve-coefficient (cdr primes) value))))

(defthm lw-mobius-sieve-coefficient-range
  (or (equal (lw-mobius-sieve-coefficient primes value) -1)
      (equal (lw-mobius-sieve-coefficient primes value) 0)
      (equal (lw-mobius-sieve-coefficient primes value) 1))
  :hints (("Goal"
           :induct (lw-mobius-sieve-coefficient primes value)
           :in-theory (union-theories '(lw-mobius-sieve-coefficient endp) (theory 'lw-msc-arithmetic))))
  :rule-classes nil)

(local
 (defthm lw-msc-prime-persists
   (implies (and (posp value) (lw-primep divisor) (lw-primep prime)
                 (not (equal divisor prime))
                 (lw-divides divisor value) (lw-divides prime value))
            (lw-divides prime (* value (/ divisor))))
   :hints (("Goal"
            :use ((:instance lw-primep-lower-bound (value divisor))
                  (:instance lw-primep-lower-bound (value prime))
                  lw-divides-positive-quotient
                  (:instance lw-prime-divisor-one-or-self (prime divisor) (divisor prime))
                  (:instance lw-prime-divides-product-iff (x divisor) (y (* value (/ divisor)))))
            :in-theory (theory 'lw-msc-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-mobius-sieve-excludes-prime
  (implies (and (lw-prime-listp primes) (posp value) (lw-primep prime)
                (not (member-equal prime primes)) (lw-divides prime value))
           (equal (lw-mobius-sieve-coefficient primes value) 0))
  :hints (("Goal"
           :induct (lw-mobius-sieve-coefficient primes value)
           :in-theory (union-theories '(lw-mobius-sieve-coefficient lw-prime-listp member-equal endp) (theory 'lw-msc-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-primep-lower-bound (value (car primes)))
                       (:instance lw-primep-lower-bound (value prime))
                       (:instance lw-divides-positive-bound (divisor prime))
                       (:instance lw-divides-positive-bound (divisor prime) (value 1))
                       (:instance lw-divides-positive-quotient (divisor (car primes)))
                       (:instance lw-msc-prime-persists (divisor (car primes))))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-mobius-sieve-convolution-step
  (implies (and (consp primes) (lw-prime-listp primes) (no-duplicatesp-equal primes) (posp value))
           (equal (lw-mobius-sieve-coefficient primes value)
                  (- (lw-mobius-sieve-coefficient (cdr primes) value)
                     (if (lw-divides (car primes) value) (lw-mobius-sieve-coefficient (cdr primes) (* value (/ (car primes)))) 0))))
  :hints (("Goal"
           :use ((:instance lw-mobius-sieve-excludes-prime (primes (cdr primes)) (prime (car primes)))
                 (:instance lw-mobius-sieve-coefficient-range (primes (cdr primes)))
                 (:instance lw-mobius-sieve-coefficient-range (primes (cdr primes)) (value (* value (/ (car primes))))))
           :expand ((lw-mobius-sieve-coefficient primes value))
           :in-theory (union-theories '(lw-prime-listp no-duplicatesp-equal endp) (theory 'lw-msc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-mobius-sieve-one
  (implies (lw-prime-listp primes)
           (equal (lw-mobius-sieve-coefficient primes 1) 1))
  :hints (("Goal"
           :induct (lw-prime-listp primes)
           :in-theory (union-theories '(lw-mobius-sieve-coefficient lw-prime-listp endp) (theory 'lw-msc-arithmetic)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-primep-lower-bound (value (car primes)))
                       (:instance lw-divides-positive-bound (divisor (car primes)) (value 1)))
                 :do-not-induct t)))
  :rule-classes nil)

(defun lw-mobius-sieve-table (primes limit)
  (declare (xargs :measure (nfix limit) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp limit) nil
    (cons (cons limit (lw-mobius-sieve-coefficient primes limit))
          (lw-mobius-sieve-table primes (- limit 1)))))

(defthm lw-mobius-sieve-table-coefficient
  (implies (and (natp limit) (posp value) (<= value limit))
           (equal (lw-dirichlet-coefficient (lw-mobius-sieve-table primes limit) value)
                  (lw-mobius-sieve-coefficient primes value)))
  :hints (("Goal"
           :induct (lw-mobius-sieve-table primes limit)
           :in-theory (union-theories '(lw-mobius-sieve-table lw-dirichlet-coefficient assoc-equal endp rfix) (theory 'lw-msc-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mobius-sieve-coefficient-range (value limit))) :do-not-induct t)))
  :rule-classes nil)
