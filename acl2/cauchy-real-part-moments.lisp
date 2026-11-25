(in-package "ACL2")

(include-book "cauchy-nonnegative-real-sum")
(include-book "polynomial-divided-difference")

; The weighted real part separates into an ordinary Cauchy sum and a
; conjugated sum with every exponent shifted upwards.

(local (defthm lw-crpm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crpm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crpm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crpm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crpm-times-negative (a b) (b a)))
                 :in-theory (disable lw-crpm-times-negative)))))

(local (defthm lw-crpm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crpm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crpm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crpm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crpm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crpm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crpm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crpm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crpm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-crpm-two-real
   (implies (and (lw-complexp value) (lw-complexp weight))
            (equal (lw-complex-scale (* 2 (car value)) (lw-complex-conjugate weight))
                   (lw-complex-add (lw-complex-mul value (lw-complex-conjugate weight))
                    (lw-complex-conjugate (lw-complex-mul weight value)))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale lw-complex-conjugate
              lw-complex-mul lw-complex-add
              lw-crpm-left-commutes lw-crpm-left-distributes lw-crpm-fold-constants
              lw-crpm-times-negative lw-crpm-negative-times lw-crpm-zero-times
              lw-crpm-minus-one lw-crpm-double-negative lw-crpm-add-cancel lw-crpm-double lw-crpm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crpm-zero-power
   (equal (lw-complex-power point 0) (cons 1 0))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-power
              lw-crpm-left-commutes lw-crpm-left-distributes lw-crpm-fold-constants
              lw-crpm-times-negative lw-crpm-negative-times lw-crpm-zero-times
              lw-crpm-minus-one lw-crpm-double-negative lw-crpm-add-cancel lw-crpm-double lw-crpm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-crpm-offset-evaluation
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp offset))
            (equal (lw-complex-polynomial coefficients point offset)
                   (lw-complex-mul (lw-complex-power point offset) (lw-complex-polynomial coefficients point 0))))
   :hints (("Goal"
            :induct (lw-complex-power point offset)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-power)
              lw-crpm-zero-power lw-complex-mul-one lw-complex-power-rational lw-complex-polynomial-rational
              lw-crpm-left-commutes lw-crpm-left-distributes lw-crpm-fold-constants
              lw-crpm-times-negative lw-crpm-negative-times lw-crpm-zero-times
              lw-crpm-minus-one lw-crpm-double-negative lw-crpm-add-cancel lw-crpm-double lw-crpm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-polynomial-offset-step (offset (- offset 1)))
                        (:instance lw-complex-mul-associative
                          (left point) (middle (lw-complex-power point (- offset 1))) (right (lw-complex-polynomial coefficients point 0))))
                  :expand ((lw-complex-power point offset))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-crpm-interleave
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
            (equal (lw-complex-add (lw-complex-add a b) (lw-complex-add c d))
                   (lw-complex-add (lw-complex-add a c) (lw-complex-add b d))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add
              lw-crpm-left-commutes lw-crpm-left-distributes lw-crpm-fold-constants
              lw-crpm-times-negative lw-crpm-negative-times lw-crpm-zero-times
              lw-crpm-minus-one lw-crpm-double-negative lw-crpm-add-cancel lw-crpm-double lw-crpm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-crpm-combine-sums
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
                 (equal head (lw-complex-add a b))
                 (equal tail (lw-complex-add c d)))
            (equal (lw-complex-add head tail)
                   (lw-complex-add (lw-complex-add a c) (lw-complex-add b d))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-crpm-interleave
              lw-crpm-left-commutes lw-crpm-left-distributes lw-crpm-fold-constants
              lw-crpm-times-negative lw-crpm-negative-times lw-crpm-zero-times
              lw-crpm-minus-one lw-crpm-double-negative lw-crpm-add-cancel lw-crpm-double lw-crpm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(defthm lw-cauchy-real-part-sum-identity
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
                (natp target) (natp samples))
           (equal (lw-cauchy-real-part-sum coefficients point target samples)
                  (lw-complex-add (lw-cauchy-evaluation-sum coefficients point target 0 samples)
                                  (lw-complex-conjugate (lw-cauchy-evaluation-sum coefficients point 0 target samples)))))
  :hints (("Goal"
           :induct (lw-cauchy-real-part-sum coefficients point target samples)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-cauchy-real-part-sum) lw-cauchy-real-part-sum
              lw-crpm-zero-power lw-complex-mul-one lw-complex-add-zero
              (:executable-counterpart lw-complex-conjugate) (:executable-counterpart lw-complex-add)
              lw-complex-conjugate-add lw-complex-conjugate-rational lw-crpm-interleave
              lw-complex-ring-rational lw-complex-power-rational lw-complex-polynomial-rational
              lw-cauchy-evaluation-sum-rational
              lw-crpm-left-commutes lw-crpm-left-distributes lw-crpm-fold-constants
              lw-crpm-times-negative lw-crpm-negative-times lw-crpm-zero-times
              lw-crpm-minus-one lw-crpm-double-negative lw-crpm-add-cancel lw-crpm-double lw-crpm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-crpm-two-real (value (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)) (weight (lw-complex-power (lw-complex-power point (- samples 1)) target)))
                       (:instance lw-crpm-offset-evaluation (point (lw-complex-power point (- samples 1))) (offset target))
                       (:instance lw-crpm-combine-sums
                         (a (lw-complex-mul (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0) (lw-complex-conjugate (lw-complex-power (lw-complex-power point (- samples 1)) target))))
                         (b (lw-complex-conjugate (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) target)))
                         (c (lw-cauchy-evaluation-sum coefficients point target 0 (- samples 1)))
                         (d (lw-complex-conjugate (lw-cauchy-evaluation-sum coefficients point 0 target (- samples 1))))
                         (head (lw-complex-scale (* 2 (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0))) (lw-complex-conjugate (lw-complex-power (lw-complex-power point (- samples 1)) target))))
                         (tail (lw-cauchy-real-part-sum coefficients point target (- samples 1)))))
                 :expand ((lw-cauchy-evaluation-sum coefficients point target 0 samples) (lw-cauchy-evaluation-sum coefficients point 0 target samples)
                           (lw-cauchy-evaluation-sum coefficients point target 0 0) (lw-cauchy-evaluation-sum coefficients point 0 target 0))
                 :do-not-induct t)))
  :rule-classes nil)
