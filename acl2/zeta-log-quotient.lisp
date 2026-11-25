(in-package "ACL2")

(include-book "zeta-series-clearance")
(include-book "complex-quotients")

; A Cauchy name for the ratio of the explicit log-weighted and ordinary
; zeta series. Its identification with the Mangoldt series and with a
; logarithmic derivative remains a separate convolution obligation.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-zlq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zlq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zlq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zlq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zlq-times-negative (a b) (b a)))
                 :in-theory (disable lw-zlq-times-negative)))))

(local (defthm lw-zlq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zlq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zlq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zlq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zlq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zlq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zlq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zlq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zlq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zlq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zlq-left-commutes)))))

(local (in-theory
 (disable lw-complex-zeta-series-value lw-complex-quotient
          lw-complex-zeta-series-clearance lw-complex-zeta-series-log-cap)))

(defun lw-zeta-log-quotient-precision (error)
 (min 1/4 (* 1/104 error)))

(defthm lw-zeta-log-quotient-precision-valid
 (implies (and (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-log-quotient-precision error)) (< 0 (lw-zeta-log-quotient-precision error))
       (<= (lw-zeta-log-quotient-precision error) 1/4) (<= (* 52 (lw-zeta-log-quotient-precision error)) (* 1/2 error)))))

(local (in-theory (disable lw-zeta-log-quotient-precision lw-zeta-log-quotient-precision-valid)))

(defun lw-complex-zeta-log-quotient-value (rate height error)
 (lw-complex-quotient (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision error)) (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision error))))

(local (in-theory (disable lw-complex-zeta-log-quotient-value)))

(defthm lw-complex-zeta-log-quotient-value-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-log-quotient-value rate height error)))
 :hints (("Goal"
  :use (lw-zeta-log-quotient-precision-valid
        (:instance lw-complex-zeta-series-value-rational (logp t) (error (lw-zeta-log-quotient-precision error)))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error (lw-zeta-log-quotient-precision error)))
        (:instance lw-complex-quotient-rational (numerator (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision error))) (denominator (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision error)))))
  :in-theory (e/d (lw-complex-zeta-log-quotient-value)
                  (lw-complex-zeta-series-value-rational lw-complex-quotient-rational))
  :do-not-induct t)))

(defthm lw-complex-zeta-log-quotient-value-cauchy
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-log-quotient-value rate height left-error) (lw-complex-zeta-log-quotient-value rate height right-error))
                   (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-zeta-log-quotient-precision-valid (error left-error))
        (:instance lw-zeta-log-quotient-precision-valid (error right-error))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error (lw-zeta-log-quotient-precision left-error)))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error (lw-zeta-log-quotient-precision left-error)))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error (lw-zeta-log-quotient-precision right-error)))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error (lw-zeta-log-quotient-precision right-error)))
        (:instance lw-complex-zeta-series-clearance (error (lw-zeta-log-quotient-precision left-error)))
        (:instance lw-complex-zeta-series-clearance (error (lw-zeta-log-quotient-precision right-error)))
        (:instance lw-complex-zeta-series-log-cap (error (lw-zeta-log-quotient-precision right-error)))
        (:instance lw-complex-zeta-series-value-cauchy
         (logp nil) (left-error (lw-zeta-log-quotient-precision left-error)) (right-error (lw-zeta-log-quotient-precision right-error)))
        (:instance lw-complex-zeta-series-value-cauchy
         (logp t) (left-error (lw-zeta-log-quotient-precision left-error)) (right-error (lw-zeta-log-quotient-precision right-error)))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision left-error))) (denominator (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision left-error)))
         (approximate-numerator (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision right-error))) (approximate-denominator (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision right-error)))
         (left-clearance 1/4) (right-clearance 1/4) (numerator-cap 3)
         (numerator-error (+ (lw-zeta-log-quotient-precision left-error) (lw-zeta-log-quotient-precision right-error))) (denominator-error (+ (lw-zeta-log-quotient-precision left-error) (lw-zeta-log-quotient-precision right-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-log-quotient-value rate height left-error) (lw-complex-zeta-log-quotient-value rate height right-error)))
         (radius (+ (* 4 (+ (lw-zeta-log-quotient-precision left-error) (lw-zeta-log-quotient-precision right-error))) (* 48 (+ (lw-zeta-log-quotient-precision left-error) (lw-zeta-log-quotient-precision right-error))))) (cap (+ left-error right-error))))
  :in-theory (e/d (lw-complex-zeta-log-quotient-value)
    (lw-complex-zeta-series-value-rational lw-complex-zeta-series-value-cauchy
     lw-complex-quotient-difference-bound))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-zlq-product-cancel
 (implies (and (lw-complexp numerator) (lw-complexp denominator)
               (not (equal denominator (cons 0 0))))
  (equal (lw-complex-mul (lw-complex-quotient numerator denominator) denominator) numerator))
 :hints (("Goal"
  :use ((:instance lw-complex-reciprocal-inverse (point denominator))
        (:instance lw-complex-mul-associative
         (left numerator) (middle (lw-complex-reciprocal denominator)) (right denominator)))
  :in-theory (e/d (lw-complex-quotient) (lw-complex-reciprocal-inverse lw-complex-mul-associative))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-log-quotient-value-product
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (equal (lw-complex-mul (lw-complex-zeta-log-quotient-value rate height error) (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision error))) (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision error))))
 :hints (("Goal"
  :use (lw-zeta-log-quotient-precision-valid
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error (lw-zeta-log-quotient-precision error)))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error (lw-zeta-log-quotient-precision error)))
        (:instance lw-complex-zeta-series-clearance (error (lw-zeta-log-quotient-precision error)))
        (:instance lw-zlq-product-cancel (numerator (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision error))) (denominator (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision error)))))
  :in-theory (e/d (lw-complex-zeta-log-quotient-value)
                  (lw-complex-zeta-series-value-rational))
  :do-not-induct t)))

