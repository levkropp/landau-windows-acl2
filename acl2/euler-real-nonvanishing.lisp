(in-package "ACL2")

(include-book "euler-real-eta-budget")

; Away from one, the first eta pair gives a positive floor for the Euler value.

(local (defthm lw-ernv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ernv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ernv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ernv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ernv-times-negative (a b) (b a)))
                 :in-theory (disable lw-ernv-times-negative)))))

(local (defthm lw-ernv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ernv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ernv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ernv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ernv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ernv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ernv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ernv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ernv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ernv-left-commutes)))))

(local (deftheory lw-ernv-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ernv-left-commutes lw-ernv-left-distributes lw-ernv-fold-constants
              lw-ernv-times-negative lw-ernv-negative-times lw-ernv-zero-times
              lw-ernv-minus-one lw-ernv-double-negative lw-ernv-add-cancel lw-ernv-double lw-ernv-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(local
 (defthm lw-ernv-computed-eta-lower
   (implies (and (rationalp rate) (< 0 rate) (not (equal rate 1)))
            (and (lw-complexp (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate)) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))
                 (<= (* 1/2 (lw-real-dirichlet-first-gap rate)) (car (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate)) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate)))))))
   :hints (("Goal"
            :use (lw-real-euler-eta-proof-block-data lw-real-dirichlet-first-gap-positive
                  (:instance lw-real-euler-eta-prefix-count-data (block (lw-real-euler-eta-proof-block rate)))
                  (:instance lw-real-euler-eta-proof-request-data (block (lw-real-euler-eta-proof-block rate)))
                  (:instance lw-real-dirichlet-eta-odd-prefix-lower
                    (count (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate))) (limit (+ 1 (* 2 (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate))))) (error (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))
                  (:instance lw-real-dirichlet-eta-pairs-rational (count (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate))) (error (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))
                  (:instance lw-dirichlet-sample-rational
                    (height 0) (index (+ 1 (* 2 (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate))))) (log-error (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))) (node-error (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))
                  (:instance lw-complex-ring-rational
                    (left (lw-dirichlet-sample rate 0 (+ 1 (* 2 (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate)))) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate)) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))
                    (right (lw-real-dirichlet-eta-pairs rate (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate)) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))))
            :in-theory (union-theories '(lw-real-dirichlet-eta-odd-prefix) (theory 'lw-ernv-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernv-computed-native-comparison
   (implies (and (rationalp rate) (< 0 rate) (not (equal rate 1)) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/64 (lw-real-euler-eta-lower-strength rate))))
            (and (lw-complex-diskp (lw-complex-sub (cons 1 0) (lw-real-euler-eta-multiplier rate (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate)))) 5)
                 (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-real-euler-eta-multiplier rate (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate)))) (lw-complex-euler-continuation-value rate 0 value-error)) (lw-complex-scale (- rate 1) (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate)) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))) (* 1/8 (lw-real-euler-eta-lower-strength rate)))))
   :hints (("Goal"
            :use (lw-real-euler-eta-proof-block-data lw-real-euler-eta-lower-strength-data
                  (:instance lw-real-euler-eta-proof-request-data (block (lw-real-euler-eta-proof-block rate)))
                  (:instance lw-real-euler-eta-cancellation-cost-data (count (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate))))
                  (:instance lw-real-euler-eta-prefix-count-data (block (lw-real-euler-eta-proof-block rate)))
                  (:instance lw-real-euler-eta-multiplier-cap (error (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))
                  (:instance lw-real-euler-eta-continuation-comparison
                    (block (lw-real-euler-eta-proof-block rate)) (error (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))) (target-error (* 1/64 (lw-real-euler-eta-lower-strength rate))))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-real-euler-eta-multiplier rate (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate)))) (lw-complex-euler-continuation-value rate 0 value-error)) (lw-complex-scale (- rate 1) (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate)) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))))
                    (radius (+ (* (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate))) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))) (+ (* 1/4 value-error) (* 1/64 (lw-real-euler-eta-lower-strength rate))) (* 4 (+ (* 1/4 value-error) (* 1/64 (lw-real-euler-eta-lower-strength rate))))))
                    (cap (* 1/8 (lw-real-euler-eta-lower-strength rate)))))
            :in-theory (theory 'lw-ernv-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ernv-floor-conflict
   (implies
    (and (rationalp rate) (< 0 rate) (not (equal rate 1))
         (lw-complexp eta) (<= (* 1/2 (lw-real-dirichlet-first-gap rate)) (car eta))
         (lw-complex-diskp multiplier 5)
         (lw-complex-diskp (lw-complex-sub (lw-complex-mul multiplier native)
                                           (lw-complex-scale (- rate 1) eta))
                           (* 1/8 (lw-real-euler-eta-lower-strength rate))))
    (not (lw-complex-diskp native (* 1/32 (lw-real-euler-eta-lower-strength rate)))))
   :hints (("Goal"
            :use (lw-real-euler-eta-lower-strength-data lw-real-dirichlet-first-gap-positive
                  (:instance lw-complex-mul-disk (left multiplier) (right native)
                    (radius 5) (other-radius (* 1/32 (lw-real-euler-eta-lower-strength rate))))
                  (:instance lw-complex-disk-data (point (lw-complex-mul multiplier native)) (radius (* 5/32 (lw-real-euler-eta-lower-strength rate))))
                  (:instance lw-complex-disk-coordinates (point (lw-complex-mul multiplier native)) (radius (* 5/32 (lw-real-euler-eta-lower-strength rate))))
                  (:instance lw-complex-disk-coordinates
                    (point (lw-complex-sub (lw-complex-mul multiplier native) (lw-complex-scale (- rate 1) eta)))
                    (radius (* 1/8 (lw-real-euler-eta-lower-strength rate))))
                  (:instance lw-ernv-multiply-order (a (* 1/2 (lw-real-dirichlet-first-gap rate))) (b (car eta)) (factor (abs (- rate 1)))))
            :in-theory (union-theories '(lw-real-euler-eta-lower-strength lw-complex-sub lw-complex-scale lw-complexp abs) (theory 'lw-ernv-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-euler-real-nonvanishing-away-from-one
  (implies
   (and (rationalp rate) (< 0 rate) (not (equal rate 1)) (rationalp value-error) (< 0 value-error) (<= value-error (* 1/64 (lw-real-euler-eta-lower-strength rate))))
   (and (rationalp (* 1/32 (lw-real-euler-eta-lower-strength rate))) (< 0 (* 1/32 (lw-real-euler-eta-lower-strength rate)))
        (< (* (* 1/32 (lw-real-euler-eta-lower-strength rate)) (* 1/32 (lw-real-euler-eta-lower-strength rate))) (lw-complex-norm-square (lw-complex-euler-continuation-value rate 0 value-error)))))
  :hints (("Goal"
           :use (lw-ernv-computed-eta-lower lw-ernv-computed-native-comparison lw-real-euler-eta-lower-strength-data
                 (:instance lw-ernv-floor-conflict (eta (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count (lw-real-euler-eta-proof-block rate)) (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate)))) (multiplier (lw-complex-sub (cons 1 0) (lw-real-euler-eta-multiplier rate (lw-real-euler-eta-proof-request rate (lw-real-euler-eta-proof-block rate))))) (native (lw-complex-euler-continuation-value rate 0 value-error)))
                 (:instance lw-complex-euler-continuation-value-rational (height 0) (error value-error))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-euler-continuation-value rate 0 value-error)) (radius (* 1/32 (lw-real-euler-eta-lower-strength rate)))))
           :in-theory (theory 'lw-ernv-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
