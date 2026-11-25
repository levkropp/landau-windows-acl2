(in-package "ACL2")

(include-book "euler-real-eta-cancellation")
(include-book "euler-fixed-truncation")

; Compare the finite eta subtraction with the native continuation value.

(local (defthm lw-eret-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eret-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eret-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eret-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eret-times-negative (a b) (b a)))
                 :in-theory (disable lw-eret-times-negative)))))

(local (defthm lw-eret-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eret-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eret-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eret-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eret-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eret-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eret-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eret-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eret-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eret-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eret-left-commutes)))))

(local (deftheory lw-eret-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-eret-left-commutes lw-eret-left-distributes lw-eret-fold-constants
              lw-eret-times-negative lw-eret-negative-times lw-eret-zero-times
              lw-eret-minus-one lw-eret-double-negative lw-eret-add-cancel lw-eret-double lw-eret-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-real-euler-eta-prefix-count (block)
  (- (lw-rational-power 2 block) 1))

(defthm lw-real-euler-eta-prefix-count-data
  (implies (and (natp block) (<= 2 block))
           (and (posp (lw-real-euler-eta-prefix-count block))
                (equal (lw-real-euler-eta-prefix-count (+ 1 block)) (+ 1 (* 2 (lw-real-euler-eta-prefix-count block))))))
  :hints (("Goal"
           :use ((:instance lw-rational-power-natural (base 2) (exponent block))
                 (:instance lw-rational-power-monotone-exponent (base 2) (small 2) (large block)))
           :expand ((lw-rational-power 2 (+ 1 block)))
           :in-theory (union-theories '(lw-real-euler-eta-prefix-count (:executable-counterpart lw-rational-power)) (theory 'lw-eret-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-eret-scaled-eta-rational
   (implies (and (rationalp rate) (rationalp error) (< 0 error))
            (lw-complexp (lw-complex-scale (- rate 1)
                           (lw-real-dirichlet-eta-odd-prefix rate count error))))
   :hints (("Goal"
            :use (lw-real-dirichlet-eta-pairs-rational
                  (:instance lw-dirichlet-sample-rational (height 0) (index (+ 1 (* 2 count))) (log-error error) (node-error error))
                  (:instance lw-complex-ring-rational (left (lw-dirichlet-sample rate 0 (+ 1 (* 2 count)) error error))
                    (right (lw-real-dirichlet-eta-pairs rate count error)))
                  (:instance lw-complex-scale-rational (factor (- rate 1)) (point (lw-real-dirichlet-eta-odd-prefix rate count error))))
            :in-theory (union-theories '(lw-real-dirichlet-eta-odd-prefix) (theory 'lw-eret-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eret-continuation-algebra
   (implies (and (lw-complexp native) (lw-complexp short) (lw-complexp long)
                 (lw-complexp multiplier) (lw-complexp eta))
            (equal
              (lw-complex-sub (lw-complex-mul (lw-complex-sub (cons 1 0) multiplier) native) eta)
              (lw-complex-add
                (lw-complex-sub (lw-complex-sub long (lw-complex-mul multiplier short)) eta)
                (lw-complex-sub (lw-complex-sub native long)
                                (lw-complex-mul multiplier (lw-complex-sub native short))))))
   :hints (("Goal" :in-theory (union-theories '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul cons-equal) (theory 'lw-eret-arithmetic))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eret-continuation-identity
   (implies
    (and (rationalp rate) (< 0 rate) (natp block) (<= 2 block)
         (rationalp error) (< 0 error) (<= error 1)
         (rationalp value-error) (< 0 value-error))
    (equal (lw-complex-sub (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-real-euler-eta-multiplier rate error)) (lw-complex-euler-continuation-value rate 0 value-error)) (lw-complex-scale (- rate 1) (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count block) error))) (lw-complex-add (lw-real-euler-eta-cancellation-residual rate (lw-real-euler-eta-prefix-count block) error) (lw-complex-sub (lw-complex-sub (lw-complex-euler-continuation-value rate 0 value-error) (lw-complex-euler-dyadic-prefix rate 0 (+ 1 block) error)) (lw-complex-mul (lw-real-euler-eta-multiplier rate error) (lw-complex-sub (lw-complex-euler-continuation-value rate 0 value-error) (lw-complex-euler-dyadic-prefix rate 0 block error)))))))
   :hints (("Goal"
            :use (lw-real-euler-eta-prefix-count-data lw-real-euler-eta-multiplier-cap
                  (:instance lw-complex-euler-dyadic-prefix-rational (height 0) (count block))
                  (:instance lw-complex-euler-dyadic-prefix-rational (height 0) (count (+ 1 block)))
                  (:instance lw-complex-euler-continuation-value-rational (height 0) (error value-error))
                  (:instance lw-eret-scaled-eta-rational (count (lw-real-euler-eta-prefix-count block)))
                  (:instance lw-eret-continuation-algebra (native (lw-complex-euler-continuation-value rate 0 value-error)) (short (lw-complex-euler-dyadic-prefix rate 0 block error)) (long (lw-complex-euler-dyadic-prefix rate 0 (+ 1 block) error))
                    (multiplier (lw-real-euler-eta-multiplier rate error)) (eta (lw-complex-scale (- rate 1) (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count block) error)))))
            :in-theory (union-theories '(lw-real-euler-eta-prefix-count lw-complex-euler-dyadic-prefix lw-real-euler-eta-cancellation-residual) (theory 'lw-eret-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-euler-eta-continuation-comparison
  (implies
   (and (rationalp rate) (< 0 rate) (natp block) (<= 2 block)
       (rationalp target-error) (< 0 target-error)
       (<= (lw-euler-continuation-block-cutoff rate 0 target-error) block)
       (rationalp error) (< 0 error) (<= error 1)
       (rationalp value-error) (< 0 value-error) (<= error (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate 0 block) target-error))
       (<= error (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate 0 (+ 1 block)) target-error)))
   (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-real-euler-eta-multiplier rate error)) (lw-complex-euler-continuation-value rate 0 value-error)) (lw-complex-scale (- rate 1) (lw-real-dirichlet-eta-odd-prefix rate (lw-real-euler-eta-prefix-count block) error))) (+ (* (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count block)) error) (+ (* 1/4 value-error) target-error) (* 4 (+ (* 1/4 value-error) target-error)))))
  :hints (("Goal"
           :use (lw-real-euler-eta-prefix-count-data lw-real-euler-eta-multiplier-cap lw-eret-continuation-identity
                 (:instance lw-real-euler-eta-cancellation-error (count (lw-real-euler-eta-prefix-count block)))
                 (:instance lw-real-euler-eta-cancellation-cost-data (count (lw-real-euler-eta-prefix-count block)))
                 (:instance lw-complex-euler-fixed-truncation-computed
                   (height 0) (error value-error) (request error))
                 (:instance lw-complex-euler-fixed-truncation-computed
                   (height 0) (block (+ 1 block)) (error value-error) (request error))
                 (:instance lw-complex-mul-disk (left (lw-real-euler-eta-multiplier rate error)) (right (lw-complex-sub (lw-complex-euler-continuation-value rate 0 value-error) (lw-complex-euler-dyadic-prefix rate 0 block error))) (radius 4) (other-radius (+ (* 1/4 value-error) target-error)))
                 (:instance lw-complex-sub-disk (left (lw-complex-sub (lw-complex-euler-continuation-value rate 0 value-error) (lw-complex-euler-dyadic-prefix rate 0 (+ 1 block) error))) (right (lw-complex-mul (lw-real-euler-eta-multiplier rate error) (lw-complex-sub (lw-complex-euler-continuation-value rate 0 value-error) (lw-complex-euler-dyadic-prefix rate 0 block error))))
                   (radius (+ (* 1/4 value-error) target-error)) (other-radius (* 4 (+ (* 1/4 value-error) target-error))))
                 (:instance lw-complex-add-disk (left (lw-real-euler-eta-cancellation-residual rate (lw-real-euler-eta-prefix-count block) error)) (right (lw-complex-sub (lw-complex-sub (lw-complex-euler-continuation-value rate 0 value-error) (lw-complex-euler-dyadic-prefix rate 0 (+ 1 block) error)) (lw-complex-mul (lw-real-euler-eta-multiplier rate error) (lw-complex-sub (lw-complex-euler-continuation-value rate 0 value-error) (lw-complex-euler-dyadic-prefix rate 0 block error)))))
                   (radius (* (lw-real-euler-eta-cancellation-cost rate (lw-real-euler-eta-prefix-count block)) error)) (other-radius (+ (+ (* 1/4 value-error) target-error) (* 4 (+ (* 1/4 value-error) target-error))))))
           :in-theory (theory 'lw-eret-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
