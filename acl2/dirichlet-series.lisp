(in-package "ACL2")

(include-book "dirichlet-finite-cauchy")

; A rational Cauchy name for the actual Mangoldt Dirichlet series at rate > 3.
; The count is computed from the requested error.  Count monotonicity is
; unnecessary: the Cauchy proof handles either ordering of two counts.

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

(local (defthm lw-dsv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dsv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dsv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dsv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dsv-times-negative (a b) (b a)))
                 :in-theory (disable lw-dsv-times-negative)))))

(local (defthm lw-dsv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dsv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dsv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dsv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dsv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dsv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dsv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dsv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dsv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dsv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dsv-left-commutes)))))

(local (in-theory
 (disable lw-complex-dirichlet-finite-value lw-dirichlet-finite-model-precision
          lw-dirichlet-finite-coefficient-precision lw-dirichlet-finite-node-precision)))

(local (defthm lw-dsv-fuel-natural
 (natp (lw-precision-fuel width epsilon))
 :hints (("Goal" :in-theory (enable lw-precision-fuel)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-dirichlet-series-count (error)
 (+ 1 (lw-precision-fuel 8 error)))

(local (in-theory (disable lw-dirichlet-series-count)))

(defthm lw-dirichlet-series-count-valid
 (implies (and (rationalp error) (< 0 error))
  (and (posp (lw-dirichlet-series-count error))
       (<= (* 2 (/ (lw-dirichlet-series-count error))) (* 1/4 error))))
 :hints (("Goal"
  :use ((:instance lw-precision-fuel-adequate (width 8) (epsilon error))
        (:instance lw-positive-division-bound (numerator 2)
         (divisor (lw-dirichlet-series-count error)) (bound (* 1/4 error))))
  :in-theory (e/d (lw-dirichlet-series-count) (lw-precision-fuel-adequate))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-dirichlet-series-value (rate height error)
 (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count error) (* 1/32 error)))

(local (in-theory (disable lw-complex-dirichlet-series-value lw-dirichlet-series-count-valid)))

(defthm lw-complex-dirichlet-series-value-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-dirichlet-series-value rate height error)))
 :hints (("Goal"
  :use (lw-dirichlet-series-count-valid
        (:instance lw-complex-dirichlet-finite-value-rational
         (count (lw-dirichlet-series-count error)) (error (* 1/32 error))))
  :in-theory (e/d (lw-complex-dirichlet-series-value)
                  (lw-complex-dirichlet-finite-value-rational))
  :do-not-induct t)))

(defthm lw-complex-dirichlet-series-value-cauchy
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-series-value rate height left-error) (lw-complex-dirichlet-series-value rate height right-error))
                   (+ left-error right-error)))
 :hints (("Goal"
  :cases ((<= (lw-dirichlet-series-count left-error) (lw-dirichlet-series-count right-error)))
  :use ((:instance lw-dirichlet-series-count-valid (error left-error))
        (:instance lw-dirichlet-series-count-valid (error right-error))
        (:instance lw-complex-dirichlet-finite-value-rational
         (count (lw-dirichlet-series-count left-error)) (error (* 1/32 left-error)))
        (:instance lw-complex-dirichlet-finite-value-rational
         (count (lw-dirichlet-series-count right-error)) (error (* 1/32 right-error)))
        (:instance lw-complex-dirichlet-finite-value-truncation-cauchy
         (count (lw-dirichlet-series-count left-error)) (start (lw-dirichlet-series-count right-error))
         (left-error (* 1/32 left-error)) (right-error (* 1/32 right-error)))
        (:instance lw-complex-dirichlet-finite-value-truncation-cauchy
         (count (lw-dirichlet-series-count right-error)) (start (lw-dirichlet-series-count left-error))
         (left-error (* 1/32 right-error)) (right-error (* 1/32 left-error)))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count right-error) (* 1/32 right-error))) (right (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count left-error) (* 1/32 left-error))) (radius (+ (* 2 (/ (lw-dirichlet-series-count left-error))) (* 4 (+ (* 1/32 left-error) (* 1/32 right-error))))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count left-error) (* 1/32 left-error)) (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count right-error) (* 1/32 right-error))))
         (radius (+ (* 2 (/ (lw-dirichlet-series-count left-error))) (* 4 (+ (* 1/32 left-error) (* 1/32 right-error))))) (cap (+ left-error right-error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count left-error) (* 1/32 left-error)) (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count right-error) (* 1/32 right-error))))
         (radius (+ (* 2 (/ (lw-dirichlet-series-count right-error))) (* 4 (+ (* 1/32 left-error) (* 1/32 right-error))))) (cap (+ left-error right-error))))
  :in-theory (e/d (lw-complex-dirichlet-series-value)
    (lw-complex-dirichlet-finite-value-rational
     lw-complex-dirichlet-finite-value-truncation-cauchy))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-dirichlet-series-finite-comparison
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
       (rationalp error) (< 0 error) (<= (lw-dirichlet-series-count error) count)
       (rationalp finite-error) (< 0 finite-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-dirichlet-finite-value rate height count finite-error)
                   (lw-complex-dirichlet-series-value rate height error))
   (+ (* 3/8 error) (* 4 finite-error))))
 :hints (("Goal"
  :use (lw-dirichlet-series-count-valid
        (:instance lw-complex-dirichlet-finite-value-truncation-cauchy
         (start (lw-dirichlet-series-count error)) (left-error finite-error) (right-error (* 1/32 error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-dirichlet-finite-value rate height count finite-error)
                                (lw-complex-dirichlet-finite-value rate height (lw-dirichlet-series-count error) (* 1/32 error))))
         (radius (+ (* 2 (/ (lw-dirichlet-series-count error))) (* 4 (+ finite-error (* 1/32 error)))))
         (cap (+ (* 3/8 error) (* 4 finite-error)))))
  :in-theory (e/d (lw-complex-dirichlet-series-value)
                  (lw-complex-dirichlet-finite-value-truncation-cauchy))
  :nonlinearp nil :do-not-induct t)))


