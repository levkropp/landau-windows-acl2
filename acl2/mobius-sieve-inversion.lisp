(in-package "ACL2")

(include-book "mobius-sieve-divisor-sums")

; The finite sieve gives the inverse of the ordinary divisor sum up to the cutoff.

(local (defthm lw-msi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-msi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-msi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-msi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-msi-times-negative (a b) (b a)))
                 :in-theory (disable lw-msi-times-negative)))))

(local (defthm lw-msi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-msi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-msi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-msi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-msi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-msi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-msi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-msi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-msi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-msi-left-commutes)))))

(local (deftheory lw-msi-arithmetic (union-theories
            '(fold-consts-in-+
              lw-msi-left-commutes lw-msi-left-distributes lw-msi-fold-constants
              lw-msi-times-negative lw-msi-negative-times lw-msi-zero-times
              lw-msi-minus-one lw-msi-double-negative lw-msi-add-cancel lw-msi-double lw-msi-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-primes-through (limit)
  (declare (xargs :measure (nfix limit) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp limit) nil
    (let ((tail (lw-primes-through (- limit 1))))
      (if (lw-primep limit) (cons limit tail) tail))))

(defthm lw-primes-through-member
  (implies (natp limit)
           (iff (member-equal prime (lw-primes-through limit))
                (and (lw-primep prime) (<= prime limit))))
  :hints (("Goal"
           :induct (lw-primes-through limit)
           :in-theory (union-theories '(lw-primes-through member-equal endp) (theory 'lw-msi-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-primep-lower-bound (value prime))
                       (:instance lw-primep-lower-bound (value limit)))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-primes-through-data
  (implies (natp limit) (and (lw-prime-listp (lw-primes-through limit)) (no-duplicatesp-equal (lw-primes-through limit))))
  :hints (("Goal"
           :induct (lw-primes-through limit)
           :in-theory (union-theories '(lw-primes-through lw-prime-listp no-duplicatesp-equal endp) (theory 'lw-msi-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-primes-through-member (limit (- limit 1)) (prime limit)))
                 :do-not-induct t)))
  :rule-classes nil)

(local
 (defun lw-msi-listed-divisor-p (primes value)
   (if (endp primes) nil
     (or (lw-divides (car primes) value) (lw-msi-listed-divisor-p (cdr primes) value)))))

(local
 (defthm lw-msi-listed-divisor-from-member
   (implies (and (member-equal prime primes) (lw-divides prime value))
            (lw-msi-listed-divisor-p primes value))
   :hints (("Goal"
            :induct (lw-msi-listed-divisor-p primes value)
            :in-theory (union-theories '(lw-msi-listed-divisor-p member-equal endp) (theory 'lw-msi-arithmetic))))
   :rule-classes nil))

(local
 (defthm lw-msi-divisor-quotient
   (implies (and (lw-prime-listp primes) (lw-primep removed) (not (member-equal removed primes))
                 (posp value) (lw-divides removed value))
            (iff (lw-msi-listed-divisor-p primes value) (lw-msi-listed-divisor-p primes (* value (/ removed)))))
   :hints (("Goal"
            :induct (lw-msi-listed-divisor-p primes value)
            :in-theory (union-theories '(lw-msi-listed-divisor-p lw-prime-listp member-equal endp) (theory 'lw-msi-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-primep-lower-bound (value removed))
                        (:instance lw-primep-lower-bound (value (car primes)))
                        (:instance lw-divides-positive-quotient (divisor removed))
                        (:instance lw-prime-divisor-one-or-self (prime removed) (divisor (car primes)))
                        (:instance lw-prime-divides-product-iff (prime (car primes)) (x removed) (y (* value (/ removed)))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-msi-empty-sieve
   (implies (and (posp value) (natp count) (natp limit) (<= count limit))
            (equal (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table nil limit)) (if (zp count) 0 1)))
   :hints (("Goal"
            :induct (lw-divisor-coefficient-sum value count (lw-mobius-sieve-table nil limit))
            :in-theory (union-theories '(lw-divisor-coefficient-sum lw-mobius-sieve-coefficient endp) (theory 'lw-msi-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-mobius-sieve-table-coefficient (primes nil) (value count))
                        (:instance lw-mobius-sieve-table-coefficient (primes nil) (value 1))
                        (:instance lw-divides-positive-product (divisor 1)))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defun lw-msi-divisor-induct (primes value)
   (declare (xargs :measure (acl2-count primes) :hints (("Goal" :in-theory (theory 'ground-zero)))))
   (if (endp primes) 0
     (if (lw-divides (car primes) value)
         (+ (lw-msi-divisor-induct (cdr primes) value)
            (lw-msi-divisor-induct (cdr primes) (* value (/ (car primes)))))
       (lw-msi-divisor-induct (cdr primes) value)))))

(local
 (defthm lw-msi-divisor-sum
   (implies (and (lw-prime-listp primes) (no-duplicatesp-equal primes)
                 (posp value) (natp limit) (<= value limit))
            (equal (lw-divisor-coefficient-sum value value (lw-mobius-sieve-table primes limit))
                   (if (lw-msi-listed-divisor-p primes value) 0 1)))
   :hints (("Goal"
            :induct (lw-msi-divisor-induct primes value)
            :in-theory (union-theories '((:induction lw-msi-divisor-induct) lw-msi-listed-divisor-p
               lw-prime-listp no-duplicatesp-equal endp lw-divisor-coefficient-sum-rational) (theory 'lw-msi-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-msi-empty-sieve (count value))
                        (:instance lw-primep-lower-bound (value (car primes)))
                        (:instance lw-divides-positive-quotient (divisor (car primes)))
                        (:instance lw-msi-divisor-quotient (removed (car primes)) (primes (cdr primes)))
                        (:instance lw-mobius-sieve-divisor-step-no-prime (count value))
                        lw-mobius-sieve-divisor-step-prime)
                  :do-not-induct t)))
   :rule-classes nil))

(defun lw-mobius-prefix-table (limit)
  (lw-mobius-sieve-table (lw-primes-through limit) limit))

(defthm lw-mobius-prefix-table-coefficient-bound
  (implies (and (natp limit) (posp value) (<= value limit))
           (<= (abs (lw-dirichlet-coefficient (lw-mobius-prefix-table limit) value)) 1))
  :hints (("Goal"
           :use ((:instance lw-mobius-sieve-table-coefficient (primes (lw-primes-through limit)))
                 (:instance lw-mobius-sieve-coefficient-range (primes (lw-primes-through limit))))
           :in-theory (union-theories '(lw-mobius-prefix-table abs) (theory 'lw-msi-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-msi-prefix-at-one
   (implies (posp limit)
            (equal (lw-divisor-coefficient-sum 1 1 (lw-mobius-prefix-table limit)) 1))
   :hints (("Goal"
            :use (lw-primes-through-data
                  (:instance lw-mobius-sieve-table-coefficient (value 1) (primes (lw-primes-through limit)))
                  (:instance lw-mobius-sieve-one (primes (lw-primes-through limit)))
                  (:instance lw-divides-positive-product (divisor 1) (value 1)))
            :in-theory (union-theories '(lw-mobius-prefix-table lw-divisor-coefficient-sum) (theory 'lw-msi-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-msi-prefix-above-one
   (implies (and (natp limit) (posp value) (< 1 value) (<= value limit))
            (equal (lw-divisor-coefficient-sum value value (lw-mobius-prefix-table limit)) 0))
   :hints (("Goal"
            :use (lw-primes-through-data lw-least-prime-divisor-sound
                  (:instance lw-primes-through-member (prime (lw-least-prime-divisor value)))
                  (:instance lw-msi-listed-divisor-from-member (primes (lw-primes-through limit)) (prime (lw-least-prime-divisor value)))
                  (:instance lw-msi-divisor-sum (primes (lw-primes-through limit))))
            :in-theory (union-theories '(lw-mobius-prefix-table) (theory 'lw-msi-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-mobius-prefix-table-divisor-identity
  (implies (and (natp limit) (posp value) (<= value limit))
           (equal (lw-divisor-coefficient-sum value value (lw-mobius-prefix-table limit))
                  (if (equal value 1) 1 0)))
  :hints (("Goal"
           :use (lw-msi-prefix-at-one lw-msi-prefix-above-one)
           :in-theory (theory 'lw-msi-arithmetic)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-msi-zero-weight
   (equal (lw-complex-scale 0 point) (cons 0 0))
   :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local
 (defthm lw-msi-transform
   (implies (and (posp count) (natp limit) (<= count limit))
            (equal (lw-dirichlet-divisor-transform count (lw-mobius-prefix-table limit) nodes)
                   (lw-dirichlet-node nodes 1)))
   :hints (("Goal"
            :induct (lw-dirichlet-divisor-transform count (lw-mobius-prefix-table limit) nodes)
            :in-theory (union-theories '(lw-dirichlet-divisor-transform lw-complex-add-zero lw-complex-scale-one lw-msi-zero-weight
                lw-dirichlet-node-rational lw-dirichlet-divisor-transform-rational (:executable-counterpart lw-complexp)) (theory 'lw-msi-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-mobius-prefix-table-divisor-identity (value count))
                        (:instance lw-mobius-prefix-table-divisor-identity (value 1)))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-mobius-prefix-table-hyperbola-identity
  (implies (posp limit)
           (equal (lw-dirichlet-hyperbola-sum limit limit limit (lw-mobius-prefix-table limit) nodes)
                  (lw-dirichlet-node nodes 1)))
  :hints (("Goal"
           :use ((:instance lw-msi-transform (count limit))
                 (:instance lw-dirichlet-full-hyperbola-divisors (weights (lw-mobius-prefix-table limit))))
           :in-theory (theory 'lw-msi-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
