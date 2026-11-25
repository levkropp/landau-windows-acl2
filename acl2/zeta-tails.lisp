(in-package "ACL2")

(include-book "zeta-family-precision")
(include-book "dirichlet-tails")

; Summable tails for ordinary and logarithm-weighted zeta sums.
; The common cubic cost and rational tail potential are reused exactly.

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

(local (defthm lw-ztd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ztd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ztd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ztd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ztd-times-negative (a b) (b a)))
                 :in-theory (disable lw-ztd-times-negative)))))

(local (defthm lw-ztd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ztd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ztd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ztd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ztd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ztd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ztd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ztd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ztd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ztd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ztd-left-commutes)))))

(local (in-theory
 (disable lw-dirichlet-cubic-node-cost lw-complex-zeta-partial-sum
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (in-theory (disable lw-complex-zeta-partial-sum lw-zeta-dirichlet-weight)))

(local (in-theory (disable lw-dirichlet-cubic-cost lw-dirichlet-cubic-cost-valid)))

(local (defun lw-ztd-tail-induction (count start)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (<= count start)) count
  (lw-ztd-tail-induction (- count 1) start))))

(local (defthm lw-ztd-cost-order
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (posp start) (natp count) (<= start count))
  (<= (lw-dirichlet-cubic-cost rate height start) (lw-dirichlet-cubic-cost rate height count)))
 :hints (("Goal" :induct (lw-ztd-tail-induction count start)
          :in-theory (disable lw-dirichlet-cubic-node-cost-valid))
         (and stable-under-simplificationp
          '(:expand ((lw-dirichlet-cubic-cost rate height count))
            :use ((:instance lw-dirichlet-cubic-node-cost-valid (index count)))
            :do-not-induct t)))
 :rule-classes nil))

(local (defthm lw-ztd-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error)) (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-ztd-reciprocal-difference
 (implies (and (rationalp count) (< 1 count))
  (equal (- (/ (- count 1)) (/ count))
         (* (/ count) (/ (- count 1)))))
 :hints (("Goal"
  :use ((:instance lw-ztd-inverse-factor
         (divisor count) (coefficient (/ (- count 1))))
        (:instance lw-ztd-inverse-factor
         (divisor (- count 1)) (coefficient (/ count))))
  :in-theory (disable lw-ztd-inverse-factor)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ztd-reciprocal-step
 (implies (and (rationalp count) (< 1 count))
  (<= (* 2 (/ count) (/ count))
      (* 2 (- (/ (- count 1)) (/ count)))))
 :hints (("Goal"
  :use (lw-ztd-reciprocal-difference
        (:instance lw-reciprocal-antitone (left (- count 1)) (right count))
        (:instance lw-ztd-multiply-order
         (a (/ count)) (b (/ (- count 1))) (factor (/ count))))
  :in-theory (disable inverse-of-* lw-reciprocal-antitone)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-cubic-term-bound
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (natp index) (< 1 index) (natp total)
       (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-scale (lw-zeta-dirichlet-weight logp index primitive-error) (lw-complex-log-ramp-independent-exp rate height index (lw-smoothed-ramp-log-error index total model-error) error)) (+ (* 2 (/ index) (/ index)) (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-smoothed-ramp-unit-error total model-error)))))
 :hints (("Goal"
  :use (lw-ztd-unit-data
        lw-dirichlet-cubic-node-cost-valid
        (:instance lw-smoothed-ramp-log-error-adequate (error model-error))
        (:instance lw-zeta-dirichlet-weight-valid (epsilon primitive-error))
        (:instance lw-complex-dirichlet-cubic-point-bound (weight (lw-zeta-dirichlet-weight logp index primitive-error)) (log-error (lw-smoothed-ramp-log-error index total model-error)))
        (:instance lw-ztd-multiply-order (a (* (lw-exp-lipschitz-cap index) (lw-smoothed-ramp-log-error index total model-error))) (b (lw-smoothed-ramp-unit-error total model-error)) (factor 6))
        (:instance lw-complex-disk-enlarge (point (lw-complex-scale (lw-zeta-dirichlet-weight logp index primitive-error) (lw-complex-log-ramp-independent-exp rate height index (lw-smoothed-ramp-log-error index total model-error) error)))
         (radius (+ (* 2 (/ index) (/ index)) (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-exp-lipschitz-cap index) (lw-smoothed-ramp-log-error index total model-error))))
         (cap (+ (* 2 (/ index) (/ index)) (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-smoothed-ramp-unit-error total model-error))))))
  :in-theory (disable lw-dirichlet-cubic-node-cost-valid lw-smoothed-ramp-log-error-adequate
                      lw-zeta-dirichlet-weight-valid lw-complex-dirichlet-cubic-point-bound)
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-tail-radius)))

(local (defthm lw-ztd-radius-diagonal
 (equal (lw-dirichlet-tail-radius rate height count count total model-error error) 0)
 :hints (("Goal" :in-theory (enable lw-dirichlet-tail-radius)))))

(local (defthm lw-ztd-radius-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (posp start) (natp count) (<= start count) (natp total)
               (rationalp model-error) (< 0 model-error)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-dirichlet-tail-radius rate height count start total model-error error)) (<= 0 (lw-dirichlet-tail-radius rate height count start total model-error error))))
 :hints (("Goal"
  :use (lw-ztd-unit-data lw-ztd-cost-order
        lw-dirichlet-cubic-cost-valid
        (:instance lw-dirichlet-cubic-cost-valid (count start))
        (:instance lw-reciprocal-antitone (left start) (right count)))
  :in-theory (e/d (lw-dirichlet-tail-radius) (lw-reciprocal-antitone))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ztd-radius-step
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (posp start) (natp count) (< start count) (natp total)
               (rationalp model-error) (< 0 model-error)
               (rationalp error) (< 0 error))
  (<= (+ (+ (* 2 (/ count) (/ count))
            (* (lw-dirichlet-cubic-node-cost rate height count) error)
            (* 6 (lw-smoothed-ramp-unit-error total model-error)))
         (lw-dirichlet-tail-radius rate height (- count 1) start total model-error error))
      (lw-dirichlet-tail-radius rate height count start total model-error error)))
 :hints (("Goal"
  :use (lw-ztd-unit-data lw-ztd-reciprocal-step
        lw-dirichlet-cubic-cost-valid
        (:instance lw-dirichlet-cubic-cost-valid (count start))
        (:instance lw-dirichlet-cubic-cost-valid (count (- count 1)))
        (:instance lw-dirichlet-cubic-node-cost-valid (index count)))
  :expand ((lw-dirichlet-cubic-cost rate height count))
  :in-theory (e/d (lw-dirichlet-tail-radius) (lw-dirichlet-cubic-node-cost-valid))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ztd-add-subtract
 (equal (lw-complex-sub (lw-complex-add term rest) prefix)
        (lw-complex-add term (lw-complex-sub rest prefix)))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(local (defthm lw-ztd-sub-self
 (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-ztd-zero-disk
 (implies (and (rationalp radius) (<= 0 radius))
  (lw-complex-diskp (cons 0 0) radius))
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-complex-zeta-finite-tail
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
       (posp start) (natp count) (<= start count) (natp total)
       (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error error) (lw-complex-zeta-partial-sum logp rate height start total model-error primitive-error error)) (lw-dirichlet-tail-radius rate height count start total model-error error)))
 :hints (("Goal" :induct (lw-ztd-tail-induction count start)
          :in-theory (disable lw-complex-zeta-cubic-term-bound lw-complex-add-disk))
         (and stable-under-simplificationp
          '(:use (lw-ztd-radius-data lw-ztd-radius-step
                  (:instance lw-complex-zeta-cubic-term-bound (index count))
                  (:instance lw-complex-add-disk
                   (left (lw-complex-scale (lw-zeta-dirichlet-weight logp count primitive-error) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count total model-error) error))) (right (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height (- count 1) total model-error primitive-error error) (lw-complex-zeta-partial-sum logp rate height start total model-error primitive-error error)))
                   (radius (+ (* 2 (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error) (* 6 (lw-smoothed-ramp-unit-error total model-error)))) (other-radius (lw-dirichlet-tail-radius rate height (- count 1) start total model-error error)))
                  (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error error) (lw-complex-zeta-partial-sum logp rate height start total model-error primitive-error error)))
                   (radius (+ (+ (* 2 (/ count) (/ count)) (* (lw-dirichlet-cubic-node-cost rate height count) error) (* 6 (lw-smoothed-ramp-unit-error total model-error))) (lw-dirichlet-tail-radius rate height (- count 1) start total model-error error)))
                   (cap (lw-dirichlet-tail-radius rate height count start total model-error error))))
            :expand ((lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error error))
            :in-theory (disable lw-complex-zeta-partial-sum
                                lw-complex-zeta-cubic-term-bound lw-complex-add-disk)
            :nonlinearp nil :do-not-induct t))))

(local (defthm lw-ztd-radius-upper
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
       (posp start) (natp count) (<= start count) (natp total)
       (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1))
  (<= (lw-dirichlet-tail-radius rate height count start total model-error error)
      (+ (* 2 (/ start)) (* (lw-dirichlet-cubic-cost rate height count) error) (* 6 count (lw-smoothed-ramp-unit-error total model-error)))))
 :hints (("Goal"
  :use (lw-ztd-unit-data lw-dirichlet-cubic-cost-valid
        (:instance lw-dirichlet-cubic-cost-valid (count start)))
  :in-theory (enable lw-dirichlet-tail-radius)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ztd-count-unit-budget
 (implies (and (natp count) (natp total) (<= count total)
               (rationalp model-error) (< 0 model-error))
  (<= (* count (lw-smoothed-ramp-unit-error total model-error)) (* 1/16 model-error)))
 :hints (("Goal"
  :use ((:instance lw-ztd-multiply-order (a count) (b (+ 1 total)) (factor model-error))
        (:instance lw-positive-division-bound
         (numerator (* count model-error)) (divisor (+ 1 total)) (bound model-error)))
  :in-theory (enable lw-smoothed-ramp-unit-error)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-uniform-tail
 (implies (and (and (rationalp rate) (< 3 rate) (rationalp height)
       (posp start) (natp count) (<= start count) (natp total)
       (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1)) (<= count total))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error error) (lw-complex-zeta-partial-sum logp rate height start total model-error primitive-error error))
   (+ (* 2 (/ start)) (* (lw-dirichlet-cubic-cost rate height count) error) (* 3/8 model-error))))
 :hints (("Goal"
  :use (lw-complex-zeta-finite-tail lw-ztd-radius-upper
        lw-ztd-count-unit-budget
        lw-dirichlet-cubic-cost-valid
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error error) (lw-complex-zeta-partial-sum logp rate height start total model-error primitive-error error)))
         (radius (lw-dirichlet-tail-radius rate height count start total model-error error))
         (cap (+ (* 2 (/ start)) (* (lw-dirichlet-cubic-cost rate height count) error) (* 3/8 model-error)))))
  :in-theory (disable lw-complex-zeta-finite-tail)
  :nonlinearp nil :do-not-induct t)))

